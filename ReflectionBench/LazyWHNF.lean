import Lean
/-

Rough notes

* Tail-recursion Optimization is fragile in lean. Do not use mutual recursion, avoid early
  exit using `unless`
* The kernel's `whns` optimisitically reduce the argument of `Nat.succ`, but throws it away
  if it doesn't turn into a literal. Presumably the cache avoids duplicated work, but this is not
  strictly call-by-name. See
  https://gist.github.com/nomeata/e368723d9d236452f97ef7e66e652532

TODO:

* Eager Nat.succ
* Nat operations

-/

open Lean

abbrev Env := List Nat

inductive StackElem
  | app : Nat → StackElem
  | proj : Name → Nat → StackElem
  | upd : Nat → StackElem
  | rec_ : RecursorVal → List Level → Array Nat → StackElem
  | nfNat : Nat → StackElem
  | primNat : Name → Option Nat → StackElem
deriving Inhabited

instance : ToString StackElem where
  toString
    | .app n => s!"@{n}"
    | .proj _ n => s!".{n}"
    | .upd n => s!"upd {n}"
    | .rec_ ci _ _ => s!"#{ci.name}"
    | .nfNat n => s!"_{n}"
    | .primNat n .none => s!"{n}"
    | .primNat n (.some m) => s!"{n} {m}"

abbrev Stack := Array StackElem

inductive Val
  | con : Name → (arity fields : Nat) → List Level → Array Nat → Val -- primitive, maybe partially applied
  | rec_ : RecursorVal → List Level → Array Nat → Val -- primitive, maybe partially applied
  -- | vlam : Nat → Val → Val
  | elam : Name → Expr → Expr → BinderInfo → Val
  | lit : Lean.Literal → Val
  | primNat : Name → Option Nat → Val

def Val.toString : Val → String
  | .con cn _ _ _ as => s!"{cn} {as}"
  -- | .vlam n v => s!"λ^{n} ({v.toString})"
  | .rec_ ci _ as => s!"{ci.name} {as}"
  | .elam n _ e _ => s!"λ {n}. {e}"
  | .lit l => (repr l).pretty
  | .primNat n .none => s!"{n}"
  | .primNat n (.some m) => s!"{n} {m}"

instance : ToString Val where toString := Val.toString

inductive HeapElem
  | thunk : Expr → HeapElem
  | value : Val → HeapElem
  | ind : Nat → HeapElem -- mostly a hack to keep step non-mutual
deriving Inhabited

abbrev Heap := Array (HeapElem × Env)

def Lean.ConstructorVal.arity (ci : ConstructorVal) : Nat :=
  ci.numParams + ci.numFields

-- Arity without the major premis
def Lean.RecursorVal.arity (ci : RecursorVal) : Nat :=
  ci.numParams + ci.numMotives + ci.numMinors + ci.numIndices

partial def toVal (genv : Environment) : Expr → MetaM (Option Val)
  | .lam n t e bi => do
    return .some (.elam n t e bi)
  | .const n us => do
      let some ci := genv.find? n | throwError "Did not find {n}"
      match ci with
      | .defnInfo _ | .thmInfo _ =>
        return .none
      | .ctorInfo ci =>
        return .some (.con ci.name ci.arity ci.numFields us #[])
      | .recInfo ci =>
        return .some (.rec_ ci us #[])
        -- let arity := ci.numParams + ci.numFields
        -- return .some (.vlam arity (.con ci (Array.range ci.numFields)))
      | _ => throwError "Unsupported constant info for {n}"
  | .lit l =>
    return .some (.lit l)
  | _ => return none

mutual
partial def ofVal (heap : Heap) (v : Val) (env : Env) : MetaM Expr := do match v with
  | .con cn _ _ us args => return mkAppN (.const cn us) (← args.mapM (ofPos heap ·))
  | .rec_ ci us args => return mkAppN (.const ci.name us) (← args.mapM (ofPos heap ·))
  | .elam n t b bi => return (Expr.lam n t b bi).instantiate (← env.toArray.mapM (ofPos heap ·))
  | .lit t => return .lit t
  | .primNat n none => return .const n []
  | .primNat n (some m) => return mkApp (.const n []) (.lit (.natVal m)) -- ofNat?


partial def ofPos (heap : Heap) (p : Nat) : MetaM Expr := do
  let (he, env) := heap[p]!
  match he with
  | .thunk e => return e.instantiate (← env.toArray.mapM (ofPos heap ·))
  | .value v => ofVal heap v env
  | .ind p => ofPos heap p
end

def inStackElem (heap : Heap) (se : StackElem) (e : Expr) : MetaM Expr := match se with
  | .upd _ => return e
  | .app p => return mkApp e (← ofPos heap p)
  | .rec_ ci us args => return mkAppN (.const ci.name us) ((← args.mapM (ofPos heap ·)) ++ #[e])
  | .proj n i => return e.proj n i
  | .nfNat n => return mkNatAdd e (mkNatLit n)
  | .primNat n none => return mkApp (.const n []) e
  | .primNat n (some m) => return mkApp2 (.const n []) (.lit (.natVal m)) e -- ofNat?

def inStack (heap : Heap) (e : Expr) (stack : Stack) : MetaM Expr :=
  stack.foldrM (inStackElem heap) e

def ofConf (heap : Heap) (v : Val) (env : Env) (stack : Stack) : MetaM Expr := do
  inStack heap (← ofVal heap v env) stack

def checkValConf (lctx : LocalContext) (heap : Heap) (v : Val) (env : Env) (stack : Stack) : MetaM Unit := do
  let le ← ofConf heap v env stack
  unless (← withCurrHeartbeats (Meta.withLCtx lctx {} (Meta.isTypeCorrect le))) do
    IO.eprint s!"In stepVal {le} not typecorrect\n"
    Meta.check le

def checkExprConf (lctx : LocalContext) (heap : Heap) (e : Expr) (env : Env) (stack : Stack) : MetaM Unit := do
  let le ← inStack heap (e.instantiate (← env.toArray.mapM (ofPos heap ·))) stack
  unless (← withCurrHeartbeats (Meta.withLCtx lctx {} (Meta.isTypeCorrect le))) do
    IO.eprint s!"In stepExpr {le} not typecorrect\n"
    Meta.check le

def Val.ofNat (n : Nat) : Val := .lit (.natVal n)

def Val.ofBool : Bool → Val
  | true => .con ``Bool.true 0 0 [] #[]
  | false => .con ``Bool.false 0 0 [] #[]

def primNatFuns := #[
    ``Nat.add,
    ``Nat.sub,
    ``Nat.mul,
    ``Nat.div,
    ``Nat.mod,
    ``Nat.pow,
    ``Nat.gcd,
    ``Nat.beq,
    ``Nat.ble,
    ``Nat.land,
    ``Nat.lor,
    ``Nat.xor,
    ``Nat.shiftLeft,
    ``Nat.shiftRight ]

def evalPrimNat (n : Name) (a1 a2 : Nat) : Val := match n with
  | ``Nat.add => .ofNat <| Nat.add a1 a2
  | ``Nat.sub => .ofNat <| Nat.sub a1 a2
  | ``Nat.mul => .ofNat <| Nat.mul a1 a2
  | ``Nat.div => .ofNat <| Nat.div a1 a2
  | ``Nat.mod => .ofNat <| Nat.mod a1 a2
  | ``Nat.pow => .ofNat <| Nat.pow a1 a2 -- todo: guard against large exponents
  | ``Nat.gcd => .ofNat <| Nat.gcd a1 a2
  | ``Nat.beq => .ofBool <| Nat.beq a1 a2
  | ``Nat.ble => .ofBool <| Nat.ble a1 a2
  | ``Nat.land => .ofNat <| Nat.land a1 a2
  | ``Nat.lor  => .ofNat <| Nat.lor a1 a2
  | ``Nat.xor  => .ofNat <| Nat.xor a1 a2
  | ``Nat.shiftLeft  => .ofNat <| Nat.shiftLeft a1 a2
  | ``Nat.shiftRight => .ofNat <| Nat.shiftRight a1 a2
  | _         => .ofNat 42

partial def lazyWhnf (genv : Environment) (_lctx : LocalContext) (e : Expr) : MetaM Expr := do
  go #[] (HeapElem.thunk e) [] #[]
where
  go (heap : Heap) (he : HeapElem) (env : Env) (stack : Stack) : MetaM Expr := do
  match he with
  | .ind p =>
    let (he, env') := heap[p]!
    let stack' := if he matches .thunk _ then stack.push (.upd p) else stack
    go heap he env' stack'

  | .value v =>

    if stack.isEmpty then
      ofVal heap v env
    else
      -- checkValConf lctx heap v env stack

      let se := stack.back
      let stack := stack.pop
      -- IO.eprint s!"{se} ⊢ ({v})\n"

      match se with
      | .upd p =>
        let heap' := heap.set! p (.value v, env)
        go heap' (.value v) env stack
      | .app p =>
        match v with
        | .con ci carity cfields us args =>
          if args.size < carity then
            go heap (.value (.con ci carity cfields us (args.push p))) env stack
          else
            throwError "Constructor is over-applied" -- {← ofVal heap v env}"
        | .rec_ ci us args =>
          if args.size < ci.arity then
            go heap (.value (.rec_ ci us (args.push p))) env stack
          else if args.size == ci.arity then
            go heap (.ind p) env (stack.push (.rec_ ci us args))
          else
            throwError "Over-applied recursor?"
        -- | .vlam (n+1) v' =>
        --  stepVal genv lctx heap (.vlam n v') (p :: env) stack.pop
        | .elam _ _ e' _ =>
          go heap (.thunk e') (p :: env) stack
        | .primNat n a? =>
          go heap (.ind p) env (stack.push (.primNat n a?) |>.push (.nfNat 0))
        | _ => throwError "Cannot apply value {v}"
      | .proj _ idx =>
        match v with
        | .con _cn arity fields _ args =>
          if let some p := args[arity - fields  + idx]? then
            go heap (.ind p) env stack
          else
            throwError "Projection out of range"
        | _ => throwError "Cannot project value"
      | .rec_ ri us args =>
        assert! ri.arity == args.size
        match v with
        | .lit (.natVal n) =>
          if ri.name = ``Nat.rec then
            if n = 0 then
              let rhs := ri.rules[0]!.rhs
              let rhs := rhs.instantiateLevelParams ri.levelParams us
              go heap (.thunk rhs) [] (stack ++ args.reverse.map (.app ·))
            else
              let p := heap.size
              let heap' := heap.push (.value (.lit (.natVal (n-1))), [])
              let rhs := ri.rules[1]!.rhs
              let rhs := rhs.instantiateLevelParams ri.levelParams us
              go heap' (.thunk rhs) [] (stack ++ #[.app p] ++ args.reverse.map (.app ·))
          else
            throwError "Cannot recurse on literal"
        | .con cn arity fields _ cargs =>
          let some rule := ri.rules.find? (·.ctor == cn)
            | throwError "Unexpected constructor {cn} for recursor {ri.name}"
          if ! cargs.size = arity then
            throwError "Unsaturated constuctor {cn} analyzsed by {ri.name}"
          else if ! rule.nfields = fields then
            throwError "Arity mismatch: {cn} has {fields} but {ri.name} expects {rule.nfields}"
          else
            let rargs : Array Nat := args[:ri.numParams + ri.numMotives + ri.numMinors] ++ cargs[arity - fields:]
            let rhs := rule.rhs.instantiateLevelParams ri.levelParams us
            -- IO.eprint s!"Applying {ri.name} with args {rargs}\n"
            go heap (.thunk rhs) [] (stack ++ rargs.reverse.map (.app ·))
        | _ => throwError "Cannot recurse with {ri.name} on value {v}"
      | .nfNat n =>
        match v with
        | .con cn _ _ _us args =>
          if cn = ``Nat.succ then
            assert! args.size = 1
            go heap (.ind args[0]!) env (stack.push (.nfNat (n+1)))
          else if cn = ``Nat.zero then
            go heap (.value (.lit (.natVal n))) env stack
          else
            throwError "Unexpcted constructor in nfNat: {v}"
        | .lit (.natVal m) =>
            go heap (.value (.lit (.natVal (m + n)))) env stack
        | _ =>
            throwError "Unexpcted value in nfNat: {v}"
      | .primNat f none =>
        match v with
        | .lit (.natVal m) =>
            go heap (.value (.primNat f m)) env stack
        | _ => throwError "Unexpected value in primNat"
      | .primNat f (some m) =>
        match v with
        | .lit (.natVal n) =>
            go heap (.value (evalPrimNat f m n)) env stack
        | _ => throwError "Unexpected value in primNat"

  | .thunk e =>
    -- IO.eprint s!"⊢ {e}\n"
    -- checkExprConf lctx heap e env stack
    if let some v ← toVal genv e then
      go heap (.value v) env stack
    else
      match e with
      | .bvar i =>
        if let some p := env[i]? then
          go heap (.ind p) env stack
        else
          throwError "Bound variable {i} not supported yet (env: {env})"
      | .letE _n _t v b _ =>
        let p := heap.size
        let heap' := heap.push (.thunk v, env)
        let env' := p :: env
        go heap' (.thunk b) env' stack
      | .app f a =>
        if let .bvar i := a then
          if let some p := env[i]? then
            go heap (.thunk f) env (stack.push (.app p))
          else
            throwError "Bound variable {i} not supported yet (env: {env})"
        else
          let p := heap.size
          let heap' := heap.push (.thunk a, env)
          go heap' (.thunk f) env (stack.push (.app p))
      | .proj n i b =>
        let stack' := stack.push (.proj n i)
        go heap (.thunk b) env stack'
      | .const n us => do
          let some ci := genv.find? n | throwError "Did not find {n}"
          if primNatFuns.contains n then
            -- IO.eprint s!"Unfolding {n} (primitive)\n"
            go heap (.value (.primNat n none)) [] stack
          else match ci with
          | .defnInfo ci =>
            -- IO.eprint s!"Unfolding {ci.name}\n"
            go heap (.thunk (ci.value.instantiateLevelParams ci.levelParams us)) [] stack
          | .thmInfo ci =>
            -- IO.eprint s!"Unfolding {ci.name}\n"
            go heap (.thunk (ci.value.instantiateLevelParams ci.levelParams us)) [] stack
          | _ => throwError "Unimplemented constant: {e}"
      | .lam .. => unreachable!
      | _ => throwError "Unimplemented: {e}"
