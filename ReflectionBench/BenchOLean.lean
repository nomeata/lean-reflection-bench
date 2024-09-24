import Lean
import ReflectionBench.LazyWHNF
import ReflectionBench.LazyNbE
import ReflectionBench.TypeChecker

open Lean Meta

structure Stat where
  module : String -- no Name, we must not reference anything from the olean
  decl : String
  inputSize : Nat
  kernelTime : Nat
  lazyWhnfTime : Option Nat
  lazyWhnfUnfoldTime : Option Nat
  -- outputSize : Option Nat
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

def runWhnf (desc : String) (whnf : Environment → LocalContext → Expr → MetaM Expr) (e : Expr)
    (checkResult := true): MetaM (Option Nat) := do
  try
    let env ← getEnv
    let lctx ← getLCtx
    let _ ← whnf env lctx e -- warm up
    let startT ← IO.monoNanosNow
    let r ← whnf env lctx e
    let endT ← IO.monoNanosNow
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

    let diffT := endT - startT
    return .some diffT
  catch ex =>
    let f ← Lean.MessageData.format (Lean.Exception.toMessageData ex)
    withOptions (pp.explicit.set · true) do
      IO.println f!"{desc} failed with {f} at\n{← ppExpr e}"
      let r' ← Meta.whnf e -- kernelWhnf (← Lean.getEnv) (← Lean.getLCtx) e
    -- unless r matches .const ``Bool.true [] do
      IO.println f!"Expected result {← ppExpr r'}"
    return .none

def checkWhnf (stats : IO.Ref Stats) (module decl : String) (e : Expr) : MetaM Unit := do
    -- IO.println f!"Looking at {← ppExpr e}"
    let inputSize ← e.numObjs
    let .some kernelTime ← runWhnf "Kernel.whnf" kernelWhnf e
      | IO.println f!"Kernel.whnf failed?"
    let lazyWhnfTime ← runWhnf "lazyWhnf" lazyWhnf e
    let lazyWhnfUnfoldTime ← runWhnf (checkResult := false) "lazyWhnfUnfold" (lazyWhnf (useUnfold := true)) e
    let stat : Stat := { module, decl, inputSize, kernelTime, lazyWhnfTime, lazyWhnfUnfoldTime }
    stats.modify (·.push stat)
    if kernelTime > 5000000 ∨ lazyWhnfTime.any (· > 5000000) then
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

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let sp ← searchPathRef.get
  let (flags, args) := args.partition fun s => s.startsWith "--"
  if let .some bad := flags.find? fun f => !#["--module-list"].contains f then
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
  let filename := "stats.json"
  let s ← stats.get
  IO.println s!"Writing {s.size} statistics to {filename}."
  IO.FS.writeFile filename (toJson s).pretty
  let (bad, good) := s.partition (·.lazyWhnfTime.isNone)
  IO.println s!"Of these, {bad.size} failed to compute."

  let totalKernel : Nat := good.foldl (·+ ·.kernelTime) 0 / 1000000
  let totalLazyWhnf : Nat := good.foldl (·+ ·.lazyWhnfTime.get!) 0 / 1000000
  let fracLazy : Float := .ofNat totalLazyWhnf / .ofNat totalKernel * 100

  let good2 := s.filter (·.lazyWhnfTime.isSome)
  let totalLazyWhnfUnfold : Nat := good2.foldl (·+ ·.lazyWhnfUnfoldTime.get!) 0 / 1000000
  let fracLazyUnfold : Float := .ofNat totalLazyWhnfUnfold / .ofNat totalKernel * 100
  IO.println s!"Total kernel: {totalKernel}ms, Total lazyWhnf: {totalLazyWhnf}ms ({fracLazy}%), Total lazyWhnfUnfold: {totalLazyWhnfUnfold}ms ({fracLazyUnfold}%)"
  return 0
