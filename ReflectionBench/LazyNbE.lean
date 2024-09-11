import Lean

open Lean

namespace Lean.LazyNbE

unsafe inductive Val
  -- Neutral terms that cannot (or don't expect to, e.g. types) evaluate
  -- include an environment (is that correct?) and list of arguments
  | neutral : Expr → List Val → Array Val → Val
  -- An expression (with environment) we may want to evaluate later
  -- If we do, we remember the result in the IORef.
  | thunk : Expr → List Val → (IO.Ref (Option Val)) → Val
  -- Evaluated, partially applied closure
  -- We store the type for readback. It's a `Val`, but will always
  -- be `.neutral`, it seems, since we don't evaluate them anyways.
  | closure : (arity : Nat) → (type : Val) → (pargs : Array Val) → (Array Val → MetaM Val) → Val
  -- Evaluated, fully applied constructor
  | con : Name → List Level → (params fields : Array Val)  → Val
  -- Literal
  | lit : Literal → Val

unsafe def Val.toString : Val → String
  | .neutral e ρ as => s!"{e} {ρ.map toString} {as.map toString}"
  | .thunk e ρ _ => s!"(t) {e}{ρ.map toString}"
  | .closure n t as _f => s!"(λ^{n} … : {toString t}) {as.map toString}"
  | .con cn _ ps fs => s!"{cn} {(ps ++ fs).map toString}"
  | .lit l => (repr l).pretty

unsafe def mkClosure (arity : Nat) (type : Val) (f : Array Val → MetaM Val) : MetaM Val :=
  if arity = 0 then
    f #[]
  else
    return .closure arity type #[] f

unsafe instance : ToString Val where toString := Val.toString

unsafe instance : Inhabited Val where
  default := .lit (.natVal 42)

unsafe def mkThunk (e : Expr) (ρ : List Val) : MetaM Val := do
  -- Avoid creating thunks for cheap things. (TODO: Deduplicate)
  match e with
  | .bvar n =>
    assert! n < ρ.length
    return ρ[n]!
  | .lit l => return .lit l
  | .forallE .. => return .neutral e ρ #[]
  | .sort .. => return .neutral e ρ #[]
  | _ =>
    let r ← IO.mkRef .none
    let ρ := ρ.take (e.looseBVarRange)
    return .thunk e ρ r

def getLambdaBodyN (n : Nat) (e : Expr) : Expr := match n with
  | 0 => e
  | n+1 => getLambdaBodyN n e.bindingBody!

unsafe def Val.ofNat (n : Nat) : Val := .lit (.natVal n)

unsafe def Val.ofBool : Bool → Val
  | true => .con ``Bool.true [] #[] #[]
  | false => .con ``Bool.false [] #[] #[]

private unsafe def primNatFuns : NameMap ((a1 a2 : Nat) → Val) :=
  .fromArray (cmp := _) #[
    (``Nat.add, fun a1 a2 => .ofNat <| Nat.add a1 a2),
    (``Nat.sub, fun a1 a2 => .ofNat <| Nat.sub a1 a2),
    (``Nat.mul, fun a1 a2 => .ofNat <| Nat.mul a1 a2),
    (``Nat.div, fun a1 a2 => .ofNat <| Nat.div a1 a2),
    (``Nat.mod, fun a1 a2 => .ofNat <| Nat.mod a1 a2),
    (``Nat.pow, fun a1 a2 => .ofNat <| Nat.pow a1 a2), -- todo: guard against large exponents
    (``Nat.gcd, fun a1 a2 => .ofNat <| Nat.gcd a1 a2),
    (``Nat.beq, fun a1 a2 => .ofBool <| Nat.beq a1 a2),
    (``Nat.ble, fun a1 a2 => .ofBool <| Nat.ble a1 a2),
    (``Nat.land, fun a1 a2 => .ofNat <| Nat.land a1 a2),
    (``Nat.lor , fun a1 a2 => .ofNat <| Nat.lor a1 a2),
    (``Nat.xor , fun a1 a2 => .ofNat <| Nat.xor a1 a2),
    (``Nat.shiftLeft , fun a1 a2 => .ofNat <| Nat.shiftLeft a1 a2),
    (``Nat.shiftRight, fun a1 a2 => .ofNat <| Nat.shiftRight a1 a2)]

mutual
-- Using a while loop to make sure it's tail recursive
unsafe def force (genv : Environment) (lctx : LocalContext) (v : Val) : MetaM Val := do
  let mut v := v
  let mut rs := #[]
  while true do
    if let .thunk e ρ r := v then
      match ← r.get with
      | .some v' => v := v'
      | .none =>
        rs := rs.push r
        v ← eval genv lctx e ρ
    else
      break
  rs.forM (·.set v)
  return v

unsafe def forceNat (genv : Environment) (lctx : LocalContext) (acc : Nat) (v : Val) : MetaM (Option Nat) := do
  match (← force genv lctx v) with
  | .lit (.natVal n) => return (n+acc)
  | .con `Nat.succ _ _ #[v] => forceNat genv lctx (acc + 1) v
  | .con `Nat.zero _ _ _ => return acc
  | _ => return none

unsafe def eval (genv : Environment) (lctx : LocalContext) (e : Expr) (ρ : List Val) :
    MetaM Val := do
  match e with
  | .bvar n => return ρ[n]!
  | .lam n t b bi =>
    let vt := .neutral (.forallE n t (.sort 24) bi) ρ #[]
    mkClosure 1 vt fun xs => do
      assert! xs.size = 1
      -- We thunk the body here: Just because we want to eval `e` does not mean
      -- we will enter the closure, so no need to look at it yet
      -- (and if we do, remember the result)
      mkThunk b (xs.toList ++ ρ)
  | .app e₁ e₂ =>
      match (← force genv lctx (← eval genv lctx e₁ ρ)) with
      | .neutral e₁' ρ as =>
        return .neutral e₁' ρ (as.push (.neutral e₂ ρ #[]))
      | .closure arity t as f => do
        let as' := as.push (← mkThunk e₂ ρ)
        if as'.size < arity then
          return .closure arity t as' f
        else
          assert! as'.size = arity
          f as'
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
      if let some fn := primNatFuns.find? n then
        -- IO.eprint s!"Unfolding {n} (primitive)\n"
        mkClosure 2 (.neutral ci.type ρ #[]) fun vs => do
          assert! vs.size = 2
          let v1 ← forceNat genv lctx 0 vs[0]!
          let v2 ← forceNat genv lctx 0 vs[1]!
          match v1, v2 with
          | .some n₁, .some n₂ =>
            return fn n₁ n₂
          | _, _ =>
            return .neutral e [] vs
      else match ci with
      | .defnInfo ci | .thmInfo ci =>
        -- logInfo m!"Unfolding {ci.name}"
        let e := ci.value.instantiateLevelParams ci.levelParams us
        eval genv lctx e []
      | .ctorInfo ci =>
        let arity := ci.numParams + ci.numFields
        mkClosure arity (.neutral ci.type ρ #[]) fun vs => do
          return .con ci.name us vs[:ci.numParams] vs[ci.numParams:]
      | .recInfo ci =>
        let arity :=ci.numParams + ci.numMotives + ci.numMinors + ci.numIndices + 1
        mkClosure arity (.neutral ci.type ρ #[]) fun vs => do
          let rargs : Array _ := vs[:ci.numParams + ci.numMotives + ci.numMinors]
          match (← force genv lctx vs.back) with
          | .con cn _us _as fs =>
            let some rule := ci.rules.find? (·.ctor == cn)
              | throwError "Unexpected constructor {cn} for recursor {ci.name}"
            if ! rule.nfields = fs.size then
              throwError "Arity mismatch: {cn} has {fs.size} but {ci.name} expects {rule.nfields} fields"
            else
              let rhs := rule.rhs.instantiateLevelParams ci.levelParams us
              let rhs := getLambdaBodyN (rargs.size + fs.size) rhs
              -- logInfo m!"Applying {ci.name} with args {rargs} and {fs}\n"
              -- IO.eprint s!"Applying {ci.name} with args {rargs} and {fs}\n"
              eval genv lctx rhs ((rargs ++ fs).toListRev ++ ρ)
          | .lit (.natVal n) =>
            unless ci.name = ``Nat.rec do
              throwError "Cannot apply recursor {ci.name} to literal {n}"
            if n = 0 then
              let rhs := ci.rules[0]!.rhs
              let rhs := rhs.instantiateLevelParams ci.levelParams us
              let rhs := getLambdaBodyN rargs.size rhs
              eval genv lctx rhs (rargs.toListRev ++ ρ)
            else
              let rhs := ci.rules[1]!.rhs
              let rhs := rhs.instantiateLevelParams ci.levelParams us
              let rhs := getLambdaBodyN (rargs.size + 1) rhs
              eval genv lctx rhs ((.lit (.natVal (n-1))) :: rargs.toListRev ++ ρ)

          | v => throwError "Cannot apply recursor to {v}"
      | _ => return .neutral e ρ #[]
  | .letE n t rhs b _ =>
    eval genv lctx (.app (.lam n t b .default) rhs) ρ
  | .lit l => return .lit l
  | .forallE .. => return .neutral e ρ #[]
  | .sort .. => return .neutral e ρ #[]
  | _ => throwError "eval: unimplemented: {e}"
end

-- Highly inefficient
-- Should cache results and read back only those elements of the environment that are actually
-- used.
-- But as long as we only test reading back small examples and `Nat`s otherwise, fine
unsafe def readback : Val → MetaM Expr
  | .neutral e ρ as => do
    return mkAppN (e.instantiate (← ρ.mapM readback).toArray) (← as.mapM readback)
  | .thunk e ρ t => do match (← t.get) with
    | .some v => readback v
    | .none => return e.instantiate (← ρ.mapM readback).toArray
  | .lit l => return .lit l
  | .con cn us ps fs =>
    return mkAppN (.const cn us) (← (ps ++ fs).mapM readback)
  | .closure arity tv as f => do
    let t ← readback tv
    let f ← Meta.forallBoundedTelescope t arity fun xs _ => do
      let rv ← f (xs.map (Val.neutral · [] #[]))
      let re ← readback rv
      Meta.mkLambdaFVars xs re
    return f.beta (← as.mapM readback)

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

/-- info: true -/
#guard_msgs in
#nbe_reduce id true

-- Tests sharing:
-- The `id (fun a => a)` should be reduced once, not twice, and the result
-- should not mention that redex anymore.


/-- info: fun (z : Bool) => (fun (a : Bool → Bool) => a) Bool.not z -/
#guard_msgs in
#nbe_reduce (fun x => x (x (fun z => x Bool.not z))) (id (fun (a : Bool → Bool) => a))

/-- info: fun (head : Nat) (tail : List Nat) => head :: tail -/
#guard_msgs in
#nbe_reduce @List.cons Nat

/-- info: fun (tail : List Nat) => id 1 :: tail -/
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

/-- info: 22 -/
#guard_msgs in
#nbe_reduce 42 - 20

/-- info: true -/
#guard_msgs in
#nbe_reduce let x := id id; x true

/-- info: 66 -/
#guard_msgs in
#nbe_reduce Nat.add 42 (Nat.succ 23)

/-- info: fun (a : Nat) => Nat.add 42 a -/
#guard_msgs in
#nbe_reduce Nat.add 42

/-- info: fun (a : Nat) => (Nat.succ 42).add a -/
#guard_msgs in
#nbe_reduce Nat.add (Nat.succ 42)

opaque aNat : Nat
/-- info: (Nat.succ 42).add aNat.succ -/
#guard_msgs in
#nbe_reduce Nat.add (Nat.succ 42) (Nat.succ aNat)

end Lean.LazyNbE
