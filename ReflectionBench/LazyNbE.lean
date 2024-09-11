import Lean

open Lean

unsafe inductive Val
  -- Neutral terms that cannot (or don't expect to, e.g. types) evaluate
  -- include an environment (is that correct?) and list of arguments
  | neutral : Expr → List Val → Array Val → Val
  -- An expression (with environment) we may want to evaluate later
  -- If we do, we remember the result in the IORef.
  | thunk : Expr → List Val → (IO.Ref (Option Val)) → Val
  -- Evaluated closure
  -- We store the type for readback. It's a `Val`, but will always
  -- be `.neutral`, it seems, since we don't evaluate them anyways.
  | closure : Name → Val → BinderInfo → (Val → MetaM Val) → Val
  -- Evaluated, fully applied constructor
  | con : Name → List Level → (params fields : Array Val)  → Val
  -- Literal
  | lit : Literal → Val

unsafe def Val.toString : Val → String
  | .neutral e ρ as => s!"{e} {ρ.map toString} {as.map toString}"
  | .thunk e ρ _ => s!"(t) {e}{ρ.map toString}"
  | .closure n t _ _ => s!"(λ {n} : {toString t}.…)"
  | .con cn _ ps fs => s!"{cn} {(ps ++ fs).map toString}"
  | .lit l => (repr l).pretty

unsafe instance : ToString Val where toString := Val.toString

unsafe instance : Inhabited Val where
  default := .lit (.natVal 42)

unsafe def mkThunk (e : Expr) (ρ : List Val) : MetaM Val := do
  -- Avoid creating thunks for cheap things. (TODO: Deduplicate)
  match e with
  | .bvar n =>
    return ρ[n]!
  | .lit l => return .lit l
  | .forallE .. => return .neutral e ρ #[]
  | .sort .. => return .neutral e ρ #[]
  | _ =>
    let r ← IO.mkRef .none
    let ρ := ρ.take (e.looseBVarRange)
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

def getLambdaBodyN (n : Nat) (e : Expr) : Expr := match n with
  | 0 => e
  | n+1 => getLambdaBodyN n e.bindingBody!

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
    let vt := .neutral t ρ #[]
    return .closure n vt bi fun x => do
      -- We thunk the body here: Just because we want to eval `e` does not mean
      -- we will enter the closure, so no need to look at it yet
      -- (and if we do, remember the result)
      mkThunk b (x :: ρ)
  | .app e₁ e₂ =>
      match (← force genv lctx (← eval genv lctx e₁ ρ)) with
      | .neutral e₁' ρ as =>
        return .neutral e₁' ρ (as.push (.neutral e₂ ρ #[]))
      | .closure _ _ _ f =>
        f (← mkThunk e₂ ρ)
      | .thunk _ _ _ =>
        panic! "force returned thunk"
      | v => throwError "Cannot apply value {v}"
  | .proj _ idx e =>
      match (← force genv lctx (← eval genv lctx e ρ)) with
      | .con _cn _us _ps fs =>
        if let some v := fs[idx]? then
          return v
        else
          throwError "Projection out of range"
      | v => throwError "Cannot project value {v}"
  | .const n us =>
      let some ci := genv.find? n | throwError "Did not find {n}"
      match ci with
      | .defnInfo ci | .thmInfo ci =>
        -- logInfo m!"Unfolding {ci.name}"
        let e := ci.value.instantiateLevelParams ci.levelParams us
        eval genv lctx e []
      | .ctorInfo ci =>
        mkClosureN ci.type ρ fun vs => do
          unless vs.size = ci.numParams + ci.numFields do
            throwError "Closure arity mismatch"
          return .con ci.name us vs[:ci.numParams] vs[ci.numParams:]
      | .recInfo ci =>
        mkClosureN ci.type ρ fun vs => do
          unless vs.size = ci.numParams + ci.numMotives + ci.numMinors + ci.numIndices + 1 do
            throwError "Recursor arity mismatch"
          match (← force genv lctx vs.back) with
          | .con cn _us _as fs =>
            let some rule := ci.rules.find? (·.ctor == cn)
              | throwError "Unexpected constructor {cn} for recursor {ci.name}"
            if ! rule.nfields = fs.size then
              throwError "Arity mismatch: {cn} has {fs.size} but {ci.name} expects {rule.nfields} fields"
            else
              let rargs : Array _ := vs[:ci.numParams + ci.numMotives + ci.numMinors]
              let rhs := rule.rhs.instantiateLevelParams ci.levelParams us
              let rhs := getLambdaBodyN (rargs.size + fs.size) rhs
              -- logInfo m!"Applying {ci.name} with args {rargs} and {fs}\n"
              -- IO.eprint s!"Applying {ci.name} with args {rargs} and {fs}\n"
              eval genv lctx rhs ((rargs ++ fs).toListRev ++ ρ) -- TODO: Reverse?
          | v => throwError "Cannot apply recursor to {v}"
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
  | .con cn us ps fs =>
    return mkAppN (.const cn us) (← (ps ++ fs).mapM readback)
  | .closure n tv bi f => do
    let t ← readback tv
    Meta.withLocalDecl n bi t fun x => do
      let rv ← f (.neutral x [] #[])
      let re ← readback rv
      Meta.mkLambdaFVars #[x] re

unsafe def lazyWhnfImpl (genv : Environment) (lctx : LocalContext) (e : Expr) : MetaM Expr := do
  let v ← eval genv lctx e []
  -- logInfo m!"Evaled, not forced: {v}"
  let v ← force genv lctx v
  -- logInfo m!"Forced: {v}"
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


/-- info: 2 -/
#guard_msgs in
#nbe_reduce (Bool.rec 1 2 true : Nat)

/-- info: id true :: List.rec [] (fun (x : Bool) (xs ih : List Bool) => id x :: ih) [false] -/
#guard_msgs in
#nbe_reduce (List.rec [] (fun x xs ih => id x :: ih) [true, false] : List Bool)
-- #nbe_reduce List.map id [true, false]

/-- info: some (id true) -/
#guard_msgs in
#nbe_reduce ([id true, false] ++ [false]).head?