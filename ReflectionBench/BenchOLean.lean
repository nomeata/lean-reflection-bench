import Lean
import ReflectionBench.LazyWHNF
import ReflectionBench.LazyNbE
import ReflectionBench.TypeChecker

open Lean Meta

partial def isReflProof (e : Expr) : Bool :=
  match_expr e with
  | Eq.refl _ _ => true
  | rfl _ _ => true
  | id _ e => isReflProof e
  | _ => false

def kernelWhnf (env : Environment) (lctx : LocalContext) (e : Expr) : MetaM Expr := do
  Lean.ofExceptKernelException <| Lean.Kernel.whnf env lctx e

def runWhnf (desc : String) (whnf : Environment → LocalContext → Expr → MetaM Expr) (e : Expr) : MetaM Nat:= do
  let startT ← IO.monoMsNow
  try
    let r ← whnf (← Lean.getEnv) (← Lean.getLCtx) e
    let endT ← IO.monoMsNow
    try check r
    catch ex =>
      withOptions (pp.universes.set · true) do
        IO.println f!"{desc} reduced\n{← ppExpr e}\nto type-incorrect\n{← ppExpr r}\n{← ex.toMessageData.format}"
    let r' ← kernelWhnf (← Lean.getEnv) (← Lean.getLCtx) e
    unless (← isDefEqGuarded r r') do
      withOptions (pp.universes.set · true) do
        IO.println f!"{desc} reduced\n{← ppExpr e}\nto\n{← ppExpr r}\nnot defeq to \n{← ppExpr r'}"
    let diffT := endT - startT
    return diffT
  catch ex =>
    let f ← Lean.MessageData.format (Lean.Exception.toMessageData ex)
    withOptions (pp.explicit.set · true) do
      IO.println f!"{desc} failed with {f} at\n{← ppExpr e}"
      let r' ← Meta.whnf e -- kernelWhnf (← Lean.getEnv) (← Lean.getLCtx) e
    -- unless r matches .const ``Bool.true [] do
      IO.println f!"Expected result {← ppExpr r'}"
    return 0

def checkWhnf (e : Expr) : MetaM Unit := do
    -- IO.println f!"Looking at {← ppExpr e}"
    let stats ←
      -- runWhnf "Meta.whnf"   (fun _ _ => whnf) e
      [ runWhnf "Kernel.whnf" kernelWhnf e
      , runWhnf "lazyWhnf"    lazyWhnf e
      -- , runWhnf "lazyNbE"     LazyNbE.lazyNbE e
      ].mapM id
    if stats.any (· > 5) then
      IO.println f!"Looking at {← ppExpr e}"
      IO.println f!"Stats: {stats}"

def checkDecide (p inst eq : Expr) : MetaM Unit := do
  if isReflProof eq then
    let e' := mkApp2 (.const ``Decidable.decide []) p inst
    checkWhnf e'
  else
      IO.println f!"ignoring proof {← ppExpr eq}"

def hasInterestingFunction (e : Expr) : Bool :=
  Option.isSome <| e.find? fun e =>
       e.isAppOfArity ``of_decide_eq_true 3
    || e.isAppOfArity ``eq_true_of_decide 3

def checkBody (e : Expr) : MetaM Unit := do
  if hasInterestingFunction e then
    let _ ← transform e (skipConstInApp := true) fun e => do
      match_expr e with
      | of_decide_eq_true p inst eq => checkDecide p inst eq
      | eq_true_of_decide p inst eq => checkDecide p inst eq
      | _ => pure ()
      return .continue
  return

def whnfHook (e : Expr) : TypeChecker.M Unit := do
  unless e.isSort || e.isLambda || e.isLit || e.isForall do
  -- don't run if already cached
  if let some _ := (← get).whnfCache[e]? then return
  let env ← getEnv
  let lctx ← getLCtx
  let ctx := {fileName := "mFile", fileMap := Inhabited.default}
  let state := {env}
  let mctxt := {lctx}
  let _ ← (checkWhnf e).run' mctxt |>.toIO ctx state

unsafe def methodsImpl : TypeChecker.Methods where
  isDefEqCore := fun t s => TypeChecker.Inner.isDefEqCore' t s methodsImpl
  whnfCore := fun e r p => TypeChecker.Inner.whnfCore' e r p methodsImpl
  whnf := fun e => do TypeChecker.Inner.whnf' e methodsImpl
  inferType := fun e i => TypeChecker.Inner.inferType' e i methodsImpl

@[implemented_by methodsImpl]
opaque methods : TypeChecker.Methods := TypeChecker.Methods.withFuel 0

unsafe def wrappedMethodsImpl : TypeChecker.Methods where
  isDefEqCore := fun t s => TypeChecker.Inner.isDefEqCore' t s wrappedMethodsImpl
  whnfCore := fun e r p => TypeChecker.Inner.whnfCore' e r p wrappedMethodsImpl
  whnf := fun e => do whnfHook e; TypeChecker.Inner.whnf' e methods
  inferType := fun e i => TypeChecker.Inner.inferType' e i wrappedMethodsImpl

@[implemented_by wrappedMethodsImpl]
opaque wrappedMethods : TypeChecker.Methods := TypeChecker.Methods.withFuel 0


def checkWithLean4Lean (e : Expr) (lps : List Name) : MetaM Unit := do
  let env ← getEnv
  let r ← TypeChecker.M.run env .safe {} do
    withReader ({ · with lparams := lps }) do
      ReaderT.run (r := wrappedMethods) do
          TypeChecker.Inner.inferType e (inferOnly := false)
  match r with
  | .ok _t => pure () -- IO.println s!"{t}"
  | .error e => throwError "Lean4Lean complains: {e.toMessageData (← getOptions)}"


def checkConstInfo (ci : ConstantInfo) : MetaM Unit := do
  match ci with
  | .defnInfo ci =>
    if ci.safety matches .safe then
      -- checkBody ci.value
      checkWithLean4Lean ci.value ci.levelParams
  | .thmInfo ci =>
      -- checkBody ci.value
      checkWithLean4Lean ci.value ci.levelParams
  | _ => return

def checkConstInfos (consts : Array ConstantInfo) : MetaM Unit := do
  consts.forM checkConstInfo

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
          | .thmInfo {value := e,..} =>
            hasInterestingFunction e
          | _ => false
        if interesting then IO.println mod
      else
        IO.println s!"Processing {mod}"
        checkConstInfos cis
  return 0
