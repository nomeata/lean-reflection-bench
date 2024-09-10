import Lean

open Lean

unsafe inductive Val
  | neutral : Expr → Val
  | thunk : Expr → List Val → Val
  | closure : Name → Expr → BinderInfo → (Val → MetaM Val) → Val
  | con : Name → (arity fields : Nat) → List Level → Array Val → Val
  | lit : Literal → Val

unsafe instance : Inhabited Val where
  default := .lit (.natVal 42)

private def Lean.ConstructorVal.arity (ci : ConstructorVal) : Nat :=
  ci.numParams + ci.numFields

unsafe def eval (genv : Environment) (lctx : LocalContext) (e : Expr) (ρ : List Val) :
    MetaM Val := do
  match e with
  | .bvar n => match ρ[n]! with
    | .thunk e ρ => eval genv lctx e ρ
    | v => return v
  | .lam n t b bi =>
    return .closure n t bi (fun x => return .thunk b (x :: ρ))
  | .app e₁ e₂ =>
      match (← eval genv lctx e₁ ρ) with
      | .neutral e₁' => return .neutral (.app e₁' e₂)
      | .lit l => throwError "Cannot apply literal {repr l} to {e₂}"
      | .con n _ _ _ _ => throwError "Cannot apply constructor {n} to {e₂}"
      | .closure _ _ _ f => f (.thunk e₂ ρ)
      | .thunk _ _ => panic! "eval returned thunk"
  | .const n us =>
      let some ci := genv.find? n | throwError "Did not find {n}"
      match ci with
      | .defnInfo ci | .thmInfo ci =>
        eval genv lctx ci.value []
      | .ctorInfo ci =>
        if ci.arity = 0 then
        return .con ci.name ci.arity ci.numFields us #[]
        else
        throwError "TODO: Nary-constructor"
      -- | .recInfo ci =>
      --  return .some (.rec_ ci us #[])
      | _ => return .neutral e
  | _ => throwError "eval: unimplemented: {e}"

unsafe def readback : Val → MetaM Expr
  | .neutral e => return e
  | .thunk e ρ => return e.instantiateRev (← ρ.mapM readback).toArray
  | .lit l => return .lit l
  | .con cn _ _ us args => return mkAppN (.const cn us) (← args.mapM readback)
  | .closure n t bi f =>
    Meta.withLocalDecl n bi t fun x => do
      let r ← f (.neutral x)
      Meta.mkLambdaFVars #[x] (← readback r)

unsafe def lazyWhnfImpl (genv : Environment) (lctx : LocalContext) (e : Expr) : MetaM Expr := do
  readback (← eval genv lctx e [])

@[implemented_by lazyWhnfImpl]
opaque lazyWhnf (genv : Environment) (lctx : LocalContext) (e : Expr) : MetaM Expr

elab "#nbe_reduce" t:term : command => Lean.Elab.Command.runTermElabM fun _ => do
  let e ← Lean.Elab.Term.elabTermAndSynthesize t none
  let e'' ← lazyWhnf (← Lean.getEnv) (← Lean.getLCtx) e
  Lean.logInfo m!"{e''}"

set_option linter.unusedVariables false

#nbe_reduce (fun y => y) (fun y => y)
#nbe_reduce (fun z => (fun y => y) (fun y => y))
#nbe_reduce (fun y => (fun z => (fun x => x) (fun x => y))) ((fun a => a) (fun a => false))
