import Lean

open Lean

unsafe inductive Val
  | neutral : Expr → List Val → Array Val → Val
  | thunk : Expr → List Val → (IO.Ref (Option Val)) → Val
  | closure : Name → Val → BinderInfo → (Val → MetaM Val) → Val
  | con : Name → (arity fields : Nat) → List Level → Array Val → Val
  | lit : Literal → Val

unsafe def Val.toString : Val → String
  | .neutral e ρ as => s!"{e} {ρ.map toString} {as.map toString}"
  | .thunk e b _ => s!"(t) {e}{b.map toString}"
  | .closure n t _ _ => s!"(λ {n} : {toString t}.…)"
  | .con cn _ _ _ as => s!"{cn} {as.map toString}"
  | .lit l => (repr l).pretty

unsafe instance : ToString Val where toString := Val.toString

unsafe instance : Inhabited Val where
  default := .lit (.natVal 42)

private def Lean.ConstructorVal.arity (ci : ConstructorVal) : Nat :=
  ci.numParams + ci.numFields

unsafe def mkThunk (e : Expr) (ρ : List Val) : MetaM Val := do
  let r ← IO.mkRef .none
  return .thunk e ρ r

unsafe def mkClosureN (t : Expr) (ρ : List Val)
    (f : Array Val → MetaM Val) (acc : Array Val := #[]) : MetaM Val := do
  match t with
  | .forallE _n d b _bi =>
  let vt := .neutral d ρ #[]
    -- let vt ← mkThunk d ρ
    -- let vt ← eval genv lctx d ρ
    return .closure `x vt .default fun x =>
      mkClosureN b (x :: ρ) f (acc.push x)
  | _ =>
    f acc

mutual
unsafe def force (genv : Environment) (lctx : LocalContext) : Val → MetaM Val
  | .thunk e ρ r => do
    match ← r.get with
    | .some v => return v
    | .none =>
      let v ← force genv lctx (← eval genv lctx e ρ)
      r.set v
      return v
  | v => return v

unsafe def eval (genv : Environment) (lctx : LocalContext) (e : Expr) (ρ : List Val) :
    MetaM Val := do
  match e with
  | .bvar n => return ρ[n]!
  | .lam n t b bi =>
    let vt ← eval genv lctx t ρ
    return .closure n vt bi (fun x => mkThunk b (x :: ρ))
  | .app e₁ e₂ =>
      match (← force genv lctx (← eval genv lctx e₁ ρ)) with
      | .neutral e₁' ρ as => return .neutral e₁' ρ (as.push (.neutral e₂ ρ #[]))
      | .closure _ _ _ f => f (← mkThunk e₂ ρ)
      | .thunk _ _ _ => panic! "force returned thunk"
      | v => throwError "Cannot apply value {v}"
  | .proj _ idx e =>
      match (← force genv lctx (← eval genv lctx e ρ)) with
      | .con _cn arity fields _ args =>
        if let some v := args[arity - fields + idx]? then
          return v
        else
          throwError "Projection out of range"
      | v => throwError "Cannot project value {v}"
  | .const n us =>
      let some ci := genv.find? n | throwError "Did not find {n}"
      match ci with
      | .defnInfo ci | .thmInfo ci =>
        -- logInfo m!"Unfolding {ci.name}"
        eval genv lctx ci.value []
      | .ctorInfo ci =>
        mkClosureN ci.type ρ fun vs =>
          return .con ci.name ci.arity ci.numFields us vs
      | _ => return .neutral e ρ #[]
  | .lit l => return .lit l
  | .forallE .. => return .neutral e ρ #[]
  | .sort .. => return .neutral e ρ #[]
  | _ => throwError "eval: unimplemented: {e}"
end

unsafe def readback : Val → MetaM Expr
  | .neutral e ρ as => do
    return mkAppN (e.instantiate (← ρ.mapM readback).toArray) (← as.mapM readback)
  | .thunk e ρ t => do match (← t.get) with
    | .some v => readback v
    | .none => return e.instantiate (← ρ.mapM readback).toArray
  | .lit l => return .lit l
  | .con cn _ _ us args =>
    return mkAppN (.const cn us) (← args.mapM readback)
  | .closure n tv bi f => do
    let t ← readback tv
    Meta.withLocalDecl n bi t fun x => do
      let rv ← f (.neutral x [] #[])
      let re ← readback rv
      Meta.mkLambdaFVars #[x] re

unsafe def lazyWhnfImpl (genv : Environment) (lctx : LocalContext) (e : Expr) : MetaM Expr := do
  let v ← eval genv lctx e []
  -- logInfo m!"{v}"
  let v ← force genv lctx v
  readback v

@[implemented_by lazyWhnfImpl]
opaque lazyWhnf (genv : Environment) (lctx : LocalContext) (e : Expr) : MetaM Expr

elab "#nbe_reduce" t:term : command => Lean.Elab.Command.runTermElabM fun _ => do
  let e ← Lean.Elab.Term.elabTermAndSynthesize t none
  let e'' ← lazyWhnf (← Lean.getEnv) (← Lean.getLCtx) e
  -- Meta.check e''
  -- guard (← Meta.isDefEq e e'')
  Lean.logInfo m!"{e''}"

set_option linter.unusedVariables false
set_option pp.funBinderTypes true

-- Tests sharing:
-- The `id (fun a => a)` should be reduced once, not twice, and the result
-- should not mention that redex anymore.

/-- info: fun (z : Bool) => (fun (a : Bool → Bool) => a) Bool.not z -/
#guard_msgs in
#nbe_reduce (fun x => x (x (fun z => x Bool.not z))) (id (fun (a : Bool → Bool) => a))

/-- info: fun (x : Nat) (x_1 : List Nat) => x :: x_1 -/
#guard_msgs in
#nbe_reduce @List.cons Nat

/-- info: fun (x : List Nat) => id 1 :: x -/
#guard_msgs in
#nbe_reduce @List.cons Nat (id 1)

/-- info: [id 1] -/
#guard_msgs in
#nbe_reduce List.cons (id 1) List.nil

-- Checks that binders are correctly substituted
/-- info: fun (y : id Bool) => true -/
#guard_msgs in
#nbe_reduce (fun (x : Type) => (fun (y : x) => true)) (id Bool)
