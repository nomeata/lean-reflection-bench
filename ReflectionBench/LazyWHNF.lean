import Lean
/-

Rough notes

* Tail-recursion Optimization is fragile in lean. Do not use mutual recursion, avoid early
  exit using `unless`
* The kernel's `whns` optimisitically reduce the argument of `Nat.succ`, but throws it away
  if it doesn't turn into a literal. Presumably the cache avoids duplicated work, but this is not
  strictly call-by-name. See
  https://gist.github.com/nomeata/e368723d9d236452f97ef7e66e652532
  This code leaves `Nat.succ` as it is, but makes the built-in `Nat` operations normalize
  its argument under `Nat.succ` (see `StackElem.nfNat`)

-/

open Lean

abbrev Env := List Nat

abbrev LMap := Array (List Name × List Level)

def Lean.Expr.instLMap (e : Expr) (lmap : LMap) :=
  -- TODO: foldl or foldr
  lmap.foldl (fun e (us, ls) => e.instantiateLevelParams us ls) e

inductive StackElem
  | app : Nat → StackElem
  | proj : Name → Nat → StackElem
  | upd : Nat → StackElem
  | rec_ : ConstantInfo → List Level → LMap → Array Nat → StackElem
  | nfNat : Nat → StackElem
  | primNat : Name → Option Nat → StackElem
deriving Inhabited

instance : ToString StackElem where
  toString
    | .app n => s!"@{n}"
    | .proj _ n => s!".{n}"
    | .upd n => s!"upd {n}"
    | .rec_ ci _ _ _ => s!"#{ci.name}"
    | .nfNat n => s!"_{n}"
    | .primNat n .none => s!"{n}"
    | .primNat n (.some m) => s!"{n} {m}"

abbrev Stack := Array StackElem

inductive Val
  -- Partial applied constructor, recursor or quotient
  | pap : ConstantInfo → List Level → LMap → (arity : Nat) → Array Nat → Val
  -- Fully applied constructor
  | con : Name → List Level → LMap → (params fields : Array Nat) → Val
  -- | vlam : Nat → Val → Val
  | elam : Name → Expr → Expr → LMap → BinderInfo → Val
  | lit : Lean.Literal → Val
  | primNat : Name → Option Nat → Val

def Val.toString : Val → String
  | .pap ci _ _ _ as => s!"{ci.name} {as}"
  | .con cn _ _ ps as => s!"{cn} {ps ++ as}"
  -- | .vlam n v => s!"λ^{n} ({v.toString})"
  | .elam n _ e _ _ => s!"λ {n}. {e}"
  | .lit l => (repr l).pretty
  | .primNat n .none => s!"{n}"
  | .primNat n (.some m) => s!"{n} {m}"

instance : ToString Val where toString := Val.toString

inductive HeapElem
  | thunk : Expr → LMap → HeapElem
  | value : Val → HeapElem
  | ind : Nat → HeapElem -- mostly a hack to keep step non-mutual
deriving Inhabited

abbrev Heap := Array (HeapElem × Env)

def Lean.ConstructorVal.arity (ci : ConstructorVal) : Nat :=
  ci.numParams + ci.numFields

-- Arity with the major premise
def Lean.RecursorVal.arity (ci : RecursorVal) : Nat :=
  ci.numParams + ci.numMotives + ci.numMinors + ci.numIndices + 1

partial def toVal (genv : Environment) (lmap : LMap) : Expr → MetaM (Option Val)
  | .lam n t e bi => do
    return .some (.elam n t e lmap bi)
  | .const n us => do
      let some ci := genv.find? n | throwError "Did not find {n}"
      match ci with
      | .defnInfo _ | .thmInfo _ =>
        return .none
      | .ctorInfo ctorInfo =>
        if ctorInfo.arity = 0 then
          return .some (.con ci.name us lmap #[] #[])
        else
          return .some (.pap ci us lmap ctorInfo.arity #[])
      | .recInfo ri =>
        return .some (.pap ci us lmap ri.arity #[])
      | .quotInfo qi =>
        let arity := match qi.kind with | .type => 2 | .ctor => 3 | .lift => 6 | .ind => 5
        return .some (.pap ci us lmap arity #[])
      | _ => throwError "Unsupported constant info for {n}"
  | .lit l =>
    return .some (.lit l)
  | _ => return none

mutual
partial def ofVal (heap : Heap) (v : Val) (env : Env) : MetaM Expr := do match v with
  | .con cn us lmap ps args =>
    return mkAppN (Expr.const cn us |>.instLMap lmap) (← (ps ++ args).mapM (ofPos heap ·))
  | .pap ci us lmap _ args =>
    return mkAppN (Expr.const ci.name us |>.instLMap lmap) (← args.mapM (ofPos heap ·))
  | .elam n t b lmap bi =>
    let e := Expr.lam n t b bi
    let e := e.instLMap lmap
    let e := e.instantiate (← env.toArray.mapM (ofPos heap ·))
    return e
  | .lit t => return .lit t
  | .primNat n none => return .const n []
  | .primNat n (some m) => return mkApp (.const n []) (.lit (.natVal m)) -- ofNat?


partial def ofPos (heap : Heap) (p : Nat) : MetaM Expr := do
  let (he, env) := heap[p]!
  match he with
  | .thunk e lmap => return e |>.instLMap lmap |>.instantiate (← env.toArray.mapM (ofPos heap ·))
  | .value v => ofVal heap v env
  | .ind p => ofPos heap p
end

def inStackElem (heap : Heap) (se : StackElem) (e : Expr) : MetaM Expr := match se with
  | .upd _ => return e
  | .app p => return mkApp e (← ofPos heap p)
  | .rec_ ci us lmap args =>
    return mkAppN (Expr.const ci.name us |>.instLMap lmap) ((← args.mapM (ofPos heap ·)) ++ #[e])
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
  | true => .con ``Bool.true [] #[] #[] #[]
  | false => .con ``Bool.false [] #[] #[] #[]

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
  go #[] (HeapElem.thunk e #[]) [] #[]
where
  go (heap : Heap) (he : HeapElem) (env : Env) (stack : Stack) : MetaM Expr := do
  match he with
  | .ind p =>
    let (he, env') := heap[p]!
    if he matches .thunk _ _ then
      let heap' := heap.set! p default -- blackholing
      let stack' := stack.push (.upd p)
      go heap' he env' stack'
    else
      go heap he env' stack

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
        | .pap ci us lmap arity args =>
          assert! args.size + 1 ≤ arity
          if args.size + 1 < arity then
            let args' := args.push p
            go heap (.value (.pap ci us lmap arity args')) env stack
          else
            match ci with
            | .ctorInfo ci =>
              let args' := args.push p
              let ps := args'[:ci.numParams]
              let fs := args'[ci.numParams:]
              go heap (.value (.con ci.name us lmap ps fs)) env stack
            | .quotInfo {kind := .ctor, ..} =>
              assert! arity = 3
              go heap (.value (.con ci.name us lmap args #[p])) env stack
            /-
            This enables cheap “Rule K” support. Unsound without checking the types, though!
            | .recInfo {name := ``Eq.rec,..} =>
              -- Hack: Make Eq.rec ignore the argument
              go heap (.ind args[3]!) env stack
            -/
            | _ =>
              -- all other .paps are strict in their last argument, so evaluate that
              go heap (.ind p) env (stack.push (.rec_ ci us lmap args))
        | .elam _ _ e' lmap _ =>
          go heap (.thunk e' lmap) (p :: env) stack
        | .primNat n a? =>
          go heap (.ind p) env (stack.push (.primNat n a?) |>.push (.nfNat 0))
        | _ => throwError "Cannot apply value {v}"
      | .proj _ idx =>
        match v with
        | .con _cn _us _lmap _ps fs =>
          if let some p := fs[idx]? then
            go heap (.ind p) env stack
          else
            throwError "Projection out of range"
        | _ => throwError "Cannot project value"
      | .rec_ ci us lmap args =>
        match ci with
        | .recInfo ri =>
          assert! ri.arity == args.size + 1
          match v with
          | .lit (.natVal n) =>
            if ri.name = ``Nat.rec then
              if n = 0 then
                let rhs := ri.rules[0]!.rhs
                let lmap := lmap.push (ri.levelParams, us)
                -- let rhs := rhs.instantiateLevelParams ri.levelParams us
                go heap (.thunk rhs lmap) [] (stack ++ args.reverse.map (.app ·))
              else
                let p := heap.size
                let heap' := heap.push (.value (.lit (.natVal (n-1))), [])
                let lmap := lmap.push (ri.levelParams, us)
                let rhs := ri.rules[1]!.rhs
                -- let rhs := rhs.instantiateLevelParams ri.levelParams us
                go heap' (.thunk rhs lmap) [] (stack ++ #[.app p] ++ args.reverse.map (.app ·))
            else
              throwError "Cannot recurse on literal"
          | .con cn _ _ _ps fs =>
            let some rule := ri.rules.find? (·.ctor == cn)
              | throwError "Unexpected constructor {cn} for recursor {ri.name}"
            if ! rule.nfields = fs.size then
              throwError "Arity mismatch: {cn} has {fs.size} but {ri.name} expects {rule.nfields} fields."
            else
              let rargs : Array Nat := args[:ri.numParams + ri.numMotives + ri.numMinors] ++ fs
              let rhs := rule.rhs
                let lmap := lmap.push (ri.levelParams, us)
              -- let rhs := rule.rhs.instantiateLevelParams ri.levelParams us
              -- IO.eprint s!"Applying {ri.name} with args {rargs}\n"
              go heap (.thunk rhs lmap) [] (stack ++ rargs.reverse.map (.app ·))
          | _ => throwError "Cannot recurse with {ri.name} on value {v}"
        | .quotInfo qi =>
          unless qi.kind matches .ind || qi.kind matches .lift do
            throwError "Unexpected quotient kind {qi.name}"
          assert! args.size = 4 || args.size = 5
          match v with
          | .con cn _ _ _ps fs =>
            assert! cn = ``Quot.mk
            assert! fs.size = 1
            go heap (.ind args[3]!) [] (stack.push (.app fs.back))
          | _ => throwError "Cannot recurse with {qi.name} on value {v}"
        | _ => throwError "Unexpected {ci.name} in rec_"
      | .nfNat n =>
        match v with
        | .con cn _us _ _ps fs =>
          if cn = ``Nat.succ then
            assert! fs.size = 1
            go heap (.ind fs[0]!) env (stack.push (.nfNat (n+1)))
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

  | .thunk e lmap =>
    -- IO.eprint s!"⊢ {e}\n"
    -- checkExprConf lctx heap e env stack
    if let some v ← toVal genv lmap e then
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
        let heap' := heap.push (.thunk v lmap, env)
        let env' := p :: env
        go heap' (.thunk b lmap) env' stack
      | .app f a =>
        if let .bvar i := a then
          if let some p := env[i]? then
            go heap (.thunk f lmap) env (stack.push (.app p))
          else
            throwError "Bound variable {i} not supported yet (env: {env})"
        else
          let p := heap.size
          let heap' := heap.push (.thunk a lmap, env)
          go heap' (.thunk f lmap) env (stack.push (.app p))
      | .proj n i b =>
        let stack' := stack.push (.proj n i)
        go heap (.thunk b lmap) env stack'
      | .const n us => do
          let some ci := genv.find? n | throwError "Did not find {n}"
          if primNatFuns.contains n then
            -- IO.eprint s!"Unfolding {n} (primitive)\n"
            go heap (.value (.primNat n none)) [] stack
          else
          /-
          match genv.find? (n ++ `eq_unfold) with
          | some ufci =>
            let .some (_, .const _ _, val) := ufci.type.eq?
              | throwError "Unexpected unfolding lemma : {ufci.name} : {ufci.type}\n"
            let lmap := lmap.push (ci.levelParams, us)
            go heap (.thunk val lmap) [] stack
          | _ =>
          -/
          match ci with
          | .defnInfo ci | .thmInfo ci =>
            -- IO.eprint s!"Unfolding {ci.name}\n"
            let val := ci.value
            let lmap := lmap.push (ci.levelParams, us)
            go heap (.thunk val lmap) [] stack
          | _ => throwError "Unimplemented constant: {e}"
      | .lam .. => unreachable!
      | .mdata _ e => go heap (.thunk e lmap) env stack
      | _ => throwError "Unimplemented: {toString e}"

elab "#lazy_reduce" t:term : command => Lean.Elab.Command.runTermElabM fun _ => do
  let e ← Lean.Elab.Term.elabTermAndSynthesize t none
  let e'' ← lazyWhnf (← Lean.getEnv) (← Lean.getLCtx) e
  -- Meta.check e''
  -- guard (← Meta.isDefEq e e'')
  Lean.logInfo m!"{e''}"

set_option linter.unusedVariables false
set_option pp.funBinderTypes true

/-- info: true -/
#guard_msgs in
#lazy_reduce id true

-- Tests sharing:
-- The `id (fun a => a)` should be reduced once, not twice, and the result
-- should not mention that redex anymore.

/-- info: fun (z : Bool) => (fun (a : Bool → Bool) => a) Bool.not z -/
#guard_msgs in
#lazy_reduce (fun x => x (x (fun z => x Bool.not z))) (id (fun (a : Bool → Bool) => a))

/-- info: List.cons -/
#guard_msgs in
#lazy_reduce @List.cons Nat

/-- info: List.cons (id 1) -/
#guard_msgs in
#lazy_reduce @List.cons Nat (id 1)

/-- info: [id 1] -/
#guard_msgs in
#lazy_reduce List.cons (id 1) List.nil

-- Checks that binders are correctly substituted
/-- info: fun (y : id Bool) => true -/
#guard_msgs in
#lazy_reduce (fun (x : Type) => (fun (y : x) => true)) (id Bool)

/-- info: 2 -/
#guard_msgs in
#lazy_reduce (Bool.rec 1 2 true : Nat)

/-- info: id true :: List.rec [] (fun (x : Bool) (xs ih : List Bool) => id x :: ih) [false] -/
#guard_msgs in
#lazy_reduce (List.rec [] (fun x xs ih => id x :: ih) [true, false] : List Bool)
-- #lazy_reduce List.map id [true, false]

/-- info: some (id true) -/
#guard_msgs in
#lazy_reduce ([id true, false] ++ [false]).head?

/-- info: 22 -/
#guard_msgs in
#lazy_reduce 42 - 20

/-- info: true -/
#guard_msgs in
#lazy_reduce let x := id id; x true

/-- info: 66 -/
#guard_msgs in
#lazy_reduce Nat.add 42 (Nat.succ 23)

/-- info: Nat.add 42 -/
#guard_msgs in
#lazy_reduce Nat.add 42

/-- info: Nat.add 43 -/
#guard_msgs in
#lazy_reduce Nat.add (Nat.succ 42)

opaque aNat : Nat
/-- error: Unsupported constant info for aNat -/
#guard_msgs in
#lazy_reduce Nat.add (Nat.succ 42) (Nat.succ aNat)
