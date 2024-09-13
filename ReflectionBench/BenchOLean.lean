import Lean
import ReflectionBench.LazyWHNF
import ReflectionBench.LazyNbE

open Lean Meta

partial def isReflProof (e : Expr) : Bool :=
  match_expr e with
  | Eq.refl _ _ => true
  | rfl _ _ => true
  | id _ e => isReflProof e
  | _ => false

def runWhnf (desc : String) (whnf : Environment → LocalContext → Expr → MetaM Expr) (e : Expr) : MetaM Unit:= do
  try
    let r ← whnf (← Lean.getEnv) (← Lean.getLCtx) e
    unless r matches .const ``Bool.true [] do
      throwError "Unexpected result {← ppExpr r}"
  catch ex =>
    let f ← Lean.MessageData.format (Lean.Exception.toMessageData ex)
    IO.println f!"{desc} failed: {f}"

def kernelWhnf (env : Environment) (lctx : LocalContext) (e : Expr) : MetaM Expr := do
  Lean.ofExceptKernelException <| Lean.Kernel.whnf env lctx e

def checkDecide (p inst eq : Expr) : MetaM Unit := do
  if isReflProof eq then
    let e' := mkApp2 (.const ``Decidable.decide []) p inst
    IO.println f!"Looking at {← ppExpr p}"
    runWhnf "Kernel.whnf" kernelWhnf e'
    runWhnf "lazyWhnf"    lazyWhnf e'
    runWhnf "lazyNbE"     LazyNbE.lazyNbE e'
  else
      IO.println f!"ignoring proof {← ppExpr eq}"

def checkBody (e : Expr) : MetaM Unit := do
  if Option.isSome <| e.find? fun e =>
       e.isAppOfArity ``of_decide_eq_true 3
    || e.isAppOfArity ``eq_true_of_decide 3
  then
    let _ ← transform e (skipConstInApp := true) fun e => do
      match_expr e with
      | of_decide_eq_true p inst eq => checkDecide p inst eq
      | eq_true_of_decide p inst eq => checkDecide p inst eq
      | _ => pure ()
      return .continue
  return


def checkConstInfo (ci : ConstantInfo) : MetaM Unit := do
  match ci with
  | .defnInfo ci => checkBody ci.value
  | .thmInfo ci => checkBody ci.value
  | _ => return

def checkConstInfos (consts : Array ConstantInfo) : MetaM Unit := do
  consts.forM checkConstInfo

unsafe def checkMod (module : Name) : IO Unit := do
  IO.println s!"Processing {module}"
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' of module {module} does not exist"
  let (mod, region) ← readModuleData mFile
  let (_, s) ← importModulesCore #[⟨module, false⟩] |>.run
  let env ← finalizeImport s #[{module}] {} 0
  let ctx := {fileName := "mFile", fileMap := Inhabited.default}
  let state := {env}
  Prod.fst <$> (MetaM.run' (checkConstInfos mod.constants)).toIO ctx state
  env.freeRegions
  region.free

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let sp ← searchPathRef.get
  let (flags, args) := args.partition fun s => s.startsWith "--"
  match flags, args with
    | [], args =>
      args.forM fun arg => do
        let mod ← if arg.endsWith ".olean" then
          let some mod ← searchModuleNameOfFileName arg sp
            | throw <| IO.userError s!"Could not resolve file name: {arg}"
          pure mod
        else
          match arg.toName with
          | .anonymous => throw <| IO.userError s!"Not a module name: {arg}"
          | m => pure m
        checkMod mod
    | _, _ => throw <| IO.userError "This does not take flags yet"
  return 0
