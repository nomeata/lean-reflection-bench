import Lean
import ReflectionBench.LazyWHNF
import ReflectionBench.LazyNbE
import ReflectionBench.TypeChecker

open Lean Meta

structure WhnfStat where
  time : Nat
  isValue : Bool
  outputSize : Nat
  ruleKSuccesses : Nat := 0
  ruleKFailures : Nat := 0
deriving ToJson, Repr

def WhnfStat.hasRuleK (s : WhnfStat) : Bool := s.ruleKFailures + s.ruleKFailures > 0

structure Stat where
  module : String -- no Name, we must not reference anything from the olean
  decl : String
  inputSize : Nat
  kernel : WhnfStat
  lazyWhnf : WhnfStat
  lazyWhnfUnfold : WhnfStat
deriving ToJson, Repr

abbrev Stats := Array Stat

partial def isReflProof (e : Expr) : Bool :=
  match_expr e with
  | Eq.refl _ _ => true
  | rfl _ _ => true
  | id _ e => isReflProof e
  | _ => false

def kernelWhnf (env : Environment) (lctx : LocalContext) (e : Expr) : MetaM Expr := do
  Lean.ofExceptKernelException <| Lean.Kernel.whnf env lctx e

def lean4LeanCheck (e : Expr) : MetaM Unit := do
  let r ← TypeChecker.M.run (← getEnv) .safe (← getLCtx) do
      TypeChecker.check e .none
  let _ ← Lean.ofExceptKernelException r

def isValue : Expr → MetaM Bool
  | .sort .. | .lam .. | .lit .. | .forallE .. => return true
  | .fvar .. | .bvar .. | .mvar .. => return true -- these are questionalbe
  | .proj .. | .letE ..  => return false
  | .mdata _ e => isValue e
  | e => do
    let arity := e.getAppNumArgs
    let f := e.getAppFn
    unless f.isConst do return false
    if (← Lean.Meta.isOffset? e).isSome then return true
    match (← getConstInfo f.constName!) with
    | .ctorInfo _ => return true
    | .recInfo ci =>
      -- is a value if underapplied
      return arity < ci.numParams + ci.numMotives + ci.numMinors + ci.numIndices
    | _ => return false

def timeIt (act : MetaM α) : MetaM (Nat × α) := do
  let startT ← IO.monoNanosNow
  let r ← act
  let endT ← IO.monoNanosNow
  return (endT - startT, r)

def runWhnf (desc : String)
    (whnf : Environment → LocalContext → Expr → MetaM (LazyWhnf.Diagnostics × Expr))
    (e : Expr) (checkResult := true) (expectVal : Bool) : MetaM WhnfStat := do
  try
    let env ← getEnv
    let lctx ← getLCtx
    let _ ← whnf env lctx e -- warm up
    let (diffT, (diag, r)) ← timeIt <| whnf env lctx e
    let isVal ← isValue r

    if expectVal && !isVal then
        IO.println f!"{desc} reduced\n{← ppExpr e}\nto non-value \n{← ppExpr r}"

    if isVal && diag.ruleKFailures > 0 then
        IO.println f!"{desc} reduced\n{← ppExpr e}\nwith rulek-failures to non-value \n{← ppExpr r}"

    if checkResult then
      try withCurrHeartbeats <| withOptions (smartUnfolding.set ·  false) <| Meta.check r
      catch ex =>
        -- withOptions (pp.universes.set · true) do
        -- withOptions (pp.explicit.set · true) do
          IO.println f!"{desc} reduced\n{← ppExpr e}\nto type-incorrect\n{← ppExpr r}\n{← ex.toMessageData.format}"

      let r' ← kernelWhnf (← Lean.getEnv) (← Lean.getLCtx) e
      unless (← withOptions (smartUnfolding.set ·  false) <| withTransparency .all <| isDefEqGuarded r r') do
        -- withOptions (pp.universes.set · true) do
        withOptions (pp.deepTerms.set · true) do
          IO.println f!"{desc} reduced\n{← ppExpr e}\nto\n{← ppExpr r}\nnot defeq to \n{← ppExpr r'}"

    return {
        time := diffT
        isValue := (← isValue r)
        outputSize := (← r.numObjs)
        ruleKSuccesses := diag.ruleKSuccesses
        ruleKFailures := diag.ruleKFailures
    }
  catch ex =>
    let f ← Lean.MessageData.format (Lean.Exception.toMessageData ex)
    withOptions (pp.explicit.set · true) do
      IO.println f!"{desc} failed with {f} at\n{← ppExpr e}"
    return {
        time := 0
        isValue := false
        outputSize := 0
    }

def checkWhnf (stats : IO.Ref Stats) (module decl : String) (e : Expr) : MetaM Unit := do
    -- IO.println f!"Looking at {← ppExpr e}"
    let inputSize ← e.numObjs

    let (kernelTime, r1) ← timeIt <| kernelWhnf (← getEnv) (← getLCtx) e
    let outputSize ← r1.numObjs

    let isVal ← isValue r1
    -- unless isVal do IO.println f!"The kernel reduced\n{← ppExpr e}\nto non-value\n{← ppExpr r1}"

    let lazyWhnfStats ← runWhnf (expectVal := isVal) "lazyWhnf" lazyWhnf e
    let lazyWhnfUnfoldStats ← runWhnf (expectVal := isVal) (checkResult := false) "lazyWhnfUnfold" (lazyWhnf (useUnfold := true)) e
    let kernel : WhnfStat := { outputSize, time := kernelTime,
                               isValue := isVal }
    let stat : Stat := { module, decl, inputSize, kernel,
                         lazyWhnf := lazyWhnfStats, lazyWhnfUnfold := lazyWhnfUnfoldStats }
    stats.modify (·.push stat)
    if kernelTime > 5000000 ∨ lazyWhnfStats.time > 5000000 then
      IO.println f!"Looking at {← ppExpr e}:"
      IO.println f!"{toJson stat}"

def checkDecide (stats : IO.Ref Stats) (mod declName : String) (p inst eq : Expr) : MetaM Unit := do
  if isReflProof eq then
    let e' := mkApp2 (.const ``Decidable.decide []) p inst
    checkWhnf stats mod declName e'
  else
      IO.println f!"ignoring proof {← ppExpr eq}"

def hasByDecideProof (e : Expr) : Bool :=
  Option.isSome <| e.find? fun e =>
       e.isAppOfArity ``of_decide_eq_true 3
    || e.isAppOfArity ``eq_true_of_decide 3

def checkBody (stats : IO.Ref Stats) (mod declName : String) (e : Expr) : MetaM Unit := do
  if hasByDecideProof e then
    let _ ← transform e (skipConstInApp := true) fun e => do
      match_expr e with
      | of_decide_eq_true p inst eq => checkDecide stats mod declName p inst eq
      | eq_true_of_decide p inst eq => checkDecide stats mod declName p inst eq
      | _ => pure ()
      return .continue
  return

def whnfHook (sref : IO.Ref Stats) (mod decl : String) (e : Expr) : TypeChecker.M Unit := do
  unless e.isSort || e.isLambda || e.isLit || e.isForall do
  -- don't run if already cached
  if let some _ := (← get).whnfCache[e]? then return
  let env ← getEnv
  let lctx ← getLCtx
  let ctx := {fileName := "mFile", fileMap := Inhabited.default}
  let state := {env}
  let mctxt := {lctx}
  let _ ← (checkWhnf sref mod decl e).run' mctxt |>.toIO ctx state

unsafe def methodsImpl : TypeChecker.Methods where
  isDefEqCore := fun t s => TypeChecker.Inner.isDefEqCore' t s methodsImpl
  whnfCore := fun e r p => TypeChecker.Inner.whnfCore' e r p methodsImpl
  whnf := fun e => do TypeChecker.Inner.whnf' e methodsImpl
  inferType := fun e i => TypeChecker.Inner.inferType' e i methodsImpl

@[implemented_by methodsImpl]
opaque methods : TypeChecker.Methods := TypeChecker.Methods.withFuel 0

unsafe def wrappedMethodsImpl (sref : IO.Ref Stats) (mod decl : String) : TypeChecker.Methods where
  isDefEqCore := fun t s => TypeChecker.Inner.isDefEqCore' t s (wrappedMethodsImpl sref mod decl)
  whnfCore := fun e r p => TypeChecker.Inner.whnfCore' e r p (wrappedMethodsImpl sref mod decl)
  whnf := fun e => do whnfHook sref mod decl e; TypeChecker.Inner.whnf' e methods
  inferType := fun e i => TypeChecker.Inner.inferType' e i (wrappedMethodsImpl sref mod decl)

@[implemented_by wrappedMethodsImpl]
opaque wrappedMethods (sref : IO.Ref Stats) (mod decl : String) : TypeChecker.Methods := TypeChecker.Methods.withFuel 0


def checkWithLean4Lean (sref : IO.Ref Stats) (mod declName : String) (e : Expr) (lps : List Name) : MetaM Unit := do
  let r ← TypeChecker.M.run (← getEnv) .safe {} do
    withReader ({ · with lparams := lps }) do
      ReaderT.run (r := wrappedMethods sref mod declName) do
          TypeChecker.Inner.inferType e (inferOnly := false)
  match r with
  | .ok _t => pure () -- IO.println s!"{t}"
  | .error e => throwError "Lean4Lean complains: {e.toMessageData (← getOptions)}"


def checkConstInfo (sref : IO.Ref Stats) (mod : String) (ci : ConstantInfo) : MetaM Unit := do
  let nameStr := ci.name.toString.map id -- Do not reference objects in the olean
  match ci with
  | .defnInfo ci =>
    if ci.safety matches .safe then
      -- checkBody ci.value
      checkWithLean4Lean sref mod nameStr ci.value ci.levelParams
  | .thmInfo ci =>
      -- checkBody ci.value
      checkWithLean4Lean sref mod nameStr ci.value ci.levelParams
  | _ => return

def checkConstInfos (sref : IO.Ref Stats) (mod : String) (consts : Array ConstantInfo) : MetaM Unit := do
  consts.forM (checkConstInfo sref mod)

def findEqRecs (mod : String) (consts : Array ConstantInfo) : MetaM Unit := do
  consts.forM fun ci => do
    if isNoConfusion (← getEnv) ci.name then return
    if ← isMatcher ci.name then return
    if Match.isMatchEqnTheorem (← getEnv) ci.name then return
    let some value := ci.value? | return
    let some e := value.find? fun e =>
      if e.isConstOf ``Eq.rec || e.isConstOf ``Eq.ndrec then
        let u := e.constLevels![0]!
        !u.isZero
      else
        false
      | return
    let u := e.constLevels![0]!
    let t := if ci matches .defnInfo .. then "def" else "theorem"
    IO.println s!"({mod}) {t} {ci.name} eliminates Eq into universe {u}"
    (← IO.getStdout).flush

unsafe def withMod (module : Name) (k : Array ConstantInfo → MetaM Unit): IO Unit := do
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' of module {module} does not exist"
  let (mod, region) ← readModuleData mFile
  let (_, s) ← importModulesCore #[⟨module, false⟩] |>.run
  let env ← finalizeImport s #[{module}] {} 0
  let ctx := {fileName := "mFile", fileMap := Inhabited.default}
  let state := {env}
  Prod.fst <$> (MetaM.run' (k mod.constants)).toIO ctx state
  env.freeRegions
  region.free

def flags := #["--module-list", "--eqrecs"]

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let sp ← searchPathRef.get
  let (flags, args) := args.partition fun s => s.startsWith "--"
  if let .some bad := flags.find? fun f => !flags.contains f then
    throw <| IO.userError s!"Invalid flag {bad}"
  let stats : IO.Ref Stats ← IO.mkRef #[]
  args.forM fun arg => do
    let mod ← if arg.endsWith ".olean" then
      let some mod ← searchModuleNameOfFileName arg sp
        | throw <| IO.userError s!"Could not resolve file name: {arg}"
      pure mod
    else
      match arg.toName with
      | .anonymous => throw <| IO.userError s!"Not a module name: {arg}"
      | m => pure m
    withMod mod fun cis => do
      if flags.contains "--eqrecs" then
        findEqRecs mod.toString cis
      else
      if flags.contains "--module-list" then
        let interesting := cis.any fun ci =>
          match ci with
          | .defnInfo {value := e, ..}
          | .thmInfo {value := e, ..} =>
            hasByDecideProof e
          | _ => false
        if interesting then IO.println mod
      else
        IO.println s!"Processing {mod}"
        checkConstInfos stats mod.toString cis
  unless flags.contains "--eqrecs" do
    let filename := "stats.json"
    let s ← stats.get
    IO.println s!"Writing {s.size} statistics to {filename}."
    IO.FS.writeFile filename (toJson s).pretty
    let good := s.filter (·.lazyWhnf.time > 0)
    IO.println s!"Of these, {s.size - good.size} failed to compute."

    let totalKernel : Nat := good.foldl (·+ ·.kernel.time) 0 / 1000000
    let totalLazyWhnf : Nat := good.foldl (·+ ·.lazyWhnf.time) 0 / 1000000
    let fracLazy : Float := .ofNat totalLazyWhnf / .ofNat totalKernel * 100

    let good2 := s.filter (·.lazyWhnfUnfold.time > 0)
    let totalLazyWhnfUnfold : Nat := good2.foldl (·+ ·.lazyWhnfUnfold.time) 0 / 1000000
    let fracLazyUnfold : Float := .ofNat totalLazyWhnfUnfold / .ofNat totalKernel * 100
    IO.println s!"Total kernel: {totalKernel}ms, Total lazyWhnf: {totalLazyWhnf}ms ({fracLazy}%), Total lazyWhnfUnfold: {totalLazyWhnfUnfold}ms ({fracLazyUnfold}%)"

    let ruleKFrac : Float := .ofNat (good.filter (·.lazyWhnf.hasRuleK)).size / .ofNat good.size * 100
    IO.println s!"Rule K used in {ruleKFrac}% of reductions."

    let good3 := s.filter fun s => s.lazyWhnf.time > 0 && s.kernel.isValue
    let totalKernel : Nat := good3.foldl (·+ ·.kernel.time) 0 / 1000000
    let totalLazyWhnf : Nat := good3.foldl (·+ ·.lazyWhnf.time) 0 / 1000000
    let fracLazy : Float := .ofNat totalLazyWhnf / .ofNat totalKernel * 100
    IO.println s!"Only successful reductions: Count: {good3.size}, Total kernel: {totalKernel}ms, Total lazyWhnf: {totalLazyWhnf}ms ({fracLazy}%)"
    let ruleKFrac : Float := .ofNat (good3.filter (·.lazyWhnf.hasRuleK)).size / .ofNat good3.size * 100
    IO.println s!"Rule K used in {ruleKFrac}% of reductions."

    let good4 := s.filter fun s => !s.lazyWhnf.hasRuleK
    let totalKernel : Nat := good4.foldl (·+ ·.kernel.time) 0 / 1000000
    let totalLazyWhnf : Nat := good4.foldl (·+ ·.lazyWhnf.time) 0 / 1000000
    let fracLazy : Float := .ofNat totalLazyWhnf / .ofNat totalKernel * 100
    IO.println s!"Only reductions without rule k: Count: {good4.size}, Total kernel: {totalKernel}ms, Total lazyWhnf: {totalLazyWhnf}ms ({fracLazy}%)"

  return 0
