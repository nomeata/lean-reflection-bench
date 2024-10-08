import Lean
import ReflectionBench.TypeChecker

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
* The kernel's `whnf` will backtrack, e.g. if `reduce_proj` fails, it will undo the changes
  to the wrapped expression. We keep the reduced term under the projection, which somehow
  makes type checking fail.

-/

open Lean

namespace LazyWhnf

structure Diagnostics where
  ruleKSuccesses : Nat := 0
  ruleKFailures : Nat := 0

abbrev Env := List Nat

abbrev LMap := Array (List Name × List Level)

def _root_.Lean.Expr.instLMap (e : Expr) (lmap : LMap) :=
  -- TODO: Cheaper to keep just one mapping and apply to its domain eagerly?
  lmap.foldr (fun (us, ls) e => e.instantiateLevelParams us ls) e

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
abbrev RStack := Array StackElem

inductive Val
  -- Partial applied constructor, recursor or quotient
  | pap : ConstantInfo → List Level → LMap → (arity : Nat) → Array Nat → Val
  -- Fully applied constructor
  | con : Name → List Level → LMap → (params fields : Array Nat) → Val
  | elam : Name → Expr → Expr → LMap → BinderInfo → Val
  | lit : Lean.Literal → Val
  | primNat : Name → Option Nat → Val
  | neutral : Expr → LMap → RStack → Val

def Val.toString : Val → String
  | .pap ci _ _ _ as => s!"{ci.name} {as}"
  | .con cn _ _ ps as => s!"{cn} {ps ++ as}"
  | .elam n _ e _ _ => s!"λ {n}. {e}"
  | .lit l => (repr l).pretty
  | .primNat n .none => s!"{n}"
  | .primNat n (.some m) => s!"{n} {m}"
  | .neutral e _ s => s!"{e} {s}"

instance : ToString Val where toString := Val.toString

inductive HeapElem
  | thunk : Expr → LMap → HeapElem
  | value : Val → HeapElem
deriving Inhabited

instance : ToString HeapElem where toString
  | .thunk e _ => s!"{e}"
  | .value v => s!"{v}"

abbrev Heap := Array (HeapElem × Env)

def _root_.Lean.ConstructorVal.arity (ci : ConstructorVal) : Nat :=
  ci.numParams + ci.numFields

def _root_.Lean.InductiveVal.arity (ii : InductiveVal) : Nat :=
  ii.numParams + ii.numIndices

def _root_.Lean.RecursorVal.arity (ci : RecursorVal) : Nat :=
  ci.numParams + ci.numMotives + ci.numMinors + ci.numIndices + 1

partial def toVal (genv : Environment) (lmap : LMap) (e : Expr) : MetaM (Option Val) := match e with
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
      | .inductInfo ii =>
        if ii.arity = 0 then
          return .some (.con ci.name us lmap #[] #[])
        else
          return .some (.pap ci us lmap ii.arity #[])
      | .opaqueInfo _ | .axiomInfo _ =>
        return .some (.neutral e lmap #[])
  | .lit l =>
    return .some (.lit l)
  | .sort .. | .forallE .. =>
    return .some (.neutral e lmap #[])
  | _ => return none

abbrev ReadBackM := ReaderT Heap <| StateT (Array Expr) <| IO

def readBackDummy : Expr := .sort 42

mutual

partial def readBackVal (v : Val) (env : Env) : ReadBackM Expr := do match v with
  | .con cn us lmap ps args =>
    return mkAppN (Expr.const cn us |>.instLMap lmap) (← (ps ++ args).mapM readBackPtr)
  | .pap ci us lmap _ args =>
    return mkAppN (Expr.const ci.name us |>.instLMap lmap) (← args.mapM readBackPtr)
  | .elam n t b lmap bi =>
    let e := Expr.lam n t b bi
    let e := e.instLMap lmap
    let e := e.instantiate (← env.toArray.mapM readBackPtr)
    -- unless e.hasLooseBVars do
    --   IO.eprintln s!"loose bvars: {e}"
    return e
  | .lit t => return .lit t
  | .primNat n none => return .const n []
  | .primNat n (some m) => return mkApp (.const n []) (.lit (.natVal m)) -- ofNat?
  | .neutral e lmap rs =>
    let e := e.instLMap lmap
    let e := e.instantiate (← env.toArray.mapM readBackPtr)
    let e ← readBackStack e rs.reverse
    return e

partial def readBackPtr (p : Nat) : ReadBackM Expr := do
  let eheap ← get
  let e' := eheap[p]!
  if e' == readBackDummy then
    let (he, env) := (← read)[p]!
    let e ←
      match he with
      | .thunk e lmap => pure (e |>.instLMap lmap |>.instantiate (← env.toArray.mapM readBackPtr))
      | .value v => readBackVal v env
    assert! e != readBackDummy
    modify (·.set! p e)
    return e
  else
    return e'

partial def readBackStackElem (se : StackElem) (e : Expr) : ReadBackM Expr := match se with
  | .upd _ => return e
  | .app p => return mkApp e (← readBackPtr p)
  | .rec_ ci us lmap args =>
    return mkAppN (Expr.const ci.name us |>.instLMap lmap) ((← args.mapM readBackPtr) ++ #[e])
  | .proj n i => return e.proj n i
  | .nfNat 0 => return e
  | .nfNat 1 => return mkApp (.const ``Nat.succ []) e
  | .nfNat n => return mkNatAdd e (mkNatLit n)
  | .primNat n none => return mkApp (.const n []) e
  | .primNat n (some m) => return mkApp2 (.const n []) (.lit (.natVal m)) e -- ofNat?

partial def readBackStack (e : Expr) (stack : Stack) : ReadBackM Expr :=
  stack.foldrM readBackStackElem e

end

def ReadBackM.run (heap : Heap) (act : ReadBackM α) : IO α := do
  Prod.fst <$> (ReaderT.run act heap).run (mkArray heap.size readBackDummy)

def ofVal (heap : Heap) (v : Val) (env : Env) : IO Expr := ReadBackM.run heap (readBackVal v env)
def ofPos (heap : Heap) (p : Nat) : IO Expr := ReadBackM.run heap (readBackPtr p)
def ofConf (heap : Heap) (v : Val) (env : Env) (stack : Stack) : MetaM Expr := ReadBackM.run heap do
  readBackStack (← readBackVal v env) stack

-- set_option trace.Meta.isDefEq.constApprox

def Lean4Lean.check (e : Expr) : MetaM Bool := do
  let r ← TypeChecker.M.run (← getEnv) .safe (← getLCtx) do
     TypeChecker.check e .none
  return r.isOk

def checkValConf (heap : Heap) (v : Val) (env : Env) (stack : Stack) : MetaM Unit := do
  let le ← ofConf heap v env stack
  -- IO.eprint s!"Evaluating:\n{le}\nstack: {stack}\nheap: {heap}\n"
  Meta.withTransparency .all <| withCurrHeartbeats <| do
      unless (← Lean4Lean.check le) do
        -- IO.eprint s!"Not typecorrect:\n{le}\nstack: {stack}\nheap: {heap}\n"
        /-
        withOptions (·.set `trace.Meta.isDefEq true) do
        withOptions (·.set `trace.Meta.isDefEq.assign true) do
        withOptions (·.set `trace.Meta.isDefEq.cache true) do
        withOptions (·.set `trace.Meta.isDefEq.delta true) do
        withOptions (·.set `trace.Meta.isDefEq.constApprox true) do
        -/
            Meta.check le

def checkExprConf (heap : Heap) (e : Expr) (lmap : LMap) (env : Env) (stack : Stack) : MetaM Unit := do
  checkValConf heap (.neutral e lmap #[]) env stack

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

-- the lean compiler cannot do tail-call optimization for mutually recursive functions,
-- so instead of three functions we write one `go` function with a “tag” argument,
-- and arguments whose type depends on that. Originally it was a simple inductive data type,
-- but allocating and freeing on every call was a 6% overhead.

inductive GoTag where | exp | value | ptr

def GoArg1 (t : GoTag) := match t with
  | .exp => Expr
  | .value => Val
  | .ptr => Nat

def GoArg2 (t : GoTag) := match t with
  | .exp => LMap
  | .value => Unit
  | .ptr => Unit


partial def lazyWhnf (genv : Environment) (_lctx : LocalContext) (e : Expr)
  (useUnfold := false) : MetaM (Diagnostics × Expr) := do
  go {} #[] .exp e #[] [] #[]
where
  go (diag : Diagnostics) (heap : Heap) (t : GoTag) (x1 : GoArg1 t) (x2 : GoArg2 t) (env : Env)
    (stack : Stack) : MetaM (Diagnostics × Expr) := do
  let goVal diag heap v env stack := go diag heap .value v () env stack
  let goExp diag heap e lmap env stack := go diag heap .exp e lmap env stack
  let goPtr diag heap v stack := go diag heap .ptr v () [] stack --NB env does not matter
  let finish diag heap v env stack := do
      let e ← ofConf heap v env stack
      return (diag, e)
  match t with
  | .ptr =>
    let p : Nat := x1
    let (he, env') := heap[p]!
    match he with
    | .thunk e lm =>
      -- Cannot blackhole if we want to be able abort anytime (neutral values)
      -- let heap' := heap.set! p default
      let stack' := stack.push (.upd p)
      goExp diag heap e lm env' stack'
    | .value v =>
      goVal diag heap v env' stack

  | .value =>
    let v : Val := x1
    -- IO.eprint s!"⊢ {v} (stack empty? {stack.isEmpty})\n"

    if stack.isEmpty then
      finish diag heap v env stack
    else
      -- checkValConf heap v env stack

      let se := stack.back
      let stack := stack.pop
      -- IO.eprint s!"{se} ⊢ ({v})\n"

      match se with
      | .upd p =>
        let heap' := heap.set! p (.value v, env)
        goVal diag heap' v env stack
      | .app p =>
        match v with
        | .pap ci us lmap arity args =>
          assert! args.size + 1 ≤ arity
          if args.size + 1 < arity then
            let args' := args.push p
            goVal diag heap (.pap ci us lmap arity args') env stack
          else
            match ci with
            | .ctorInfo ci =>
              let args' := args.push p
              let ps := args'[:ci.numParams]
              let fs := args'[ci.numParams:]
              goVal diag heap (.con ci.name us lmap ps fs) env stack
            | .inductInfo ii =>
              let args' := args.push p
              let ps := args'[:ii.numParams]
              let fs := args'[ii.numParams:]
              goVal diag heap (.con ci.name us lmap ps fs) env stack
            | .quotInfo {kind := .ctor, ..} =>
              assert! arity = 3
              goVal diag heap (.con ci.name us lmap args #[p]) env stack
            | .quotInfo {kind := .type, ..} =>
              assert! arity = 2
              goVal diag heap (.con ci.name us lmap args #[p]) env stack
            | .recInfo {name := ``Eq.rec,..} =>
              if false then
                -- This implemens the “fast rule K” without conversion checking
                let diag' := { diag with ruleKSuccesses := diag.ruleKSuccesses + 1}
                goPtr diag' heap args[3]! stack
              else
                -- This implements rule K. We have to read back here!
                let (t1, t2) ← ReadBackM.run heap do
                  let t1 ← readBackPtr args[1]!
                  let t2 ← readBackPtr args[4]!
                  return (t1, t2)
                -- IO.println f!"Rule K: {← Meta.ppExpr t1} =?= {← Meta.ppExpr t2}"
                match Kernel.isDefEq genv _lctx t1 t2 with
                | .ok true =>
                  let diag' := { diag with ruleKSuccesses := diag.ruleKSuccesses + 1}
                  goPtr diag' heap args[3]! stack
                | _ =>
                  let diag' := { diag with ruleKFailures := diag.ruleKFailures + 1}
                  -- IO.println f!"Rule K failed:\n{← Meta.ppExpr t1}\n=?=¬{← Meta.ppExpr t2}"
                  goPtr diag' heap p (stack.push (.rec_ ci us lmap args))
            | _ =>
              -- all other .paps are strict in their last argument, so evaluate that
              goPtr diag heap p (stack.push (.rec_ ci us lmap args))
        | .elam _ _ e' lmap _ =>
          goExp diag heap e' lmap (p :: env) stack
        | .primNat n a? =>
          goPtr diag heap p (stack.push (.primNat n a?) |>.push (.nfNat 0))
        | .neutral e lmap rs =>
            goVal diag heap (.neutral e lmap (rs.push se)) env stack
        | _ => throwError "Cannot apply value {v}"
      | .proj _ idx =>
        match v with
        | .con _cn _us _lmap _ps fs =>
          if let some p := fs[idx]? then
            goPtr diag heap p stack
          else
            throwError "Projection out of range"
        | .neutral e lmap rs =>
            goVal diag heap (.neutral e lmap (rs.push se)) env stack
        | _ => throwError "Cannot project value {v}"
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
                goExp diag heap rhs lmap [] (stack ++ args.reverse.map (.app ·))
              else
                let p := heap.size
                let heap' := heap.push (.value (.lit (.natVal (n-1))), [])
                let lmap := lmap.push (ri.levelParams, us)
                let rhs := ri.rules[1]!.rhs
                -- let rhs := rhs.instantiateLevelParams ri.levelParams us
                goExp diag heap' rhs lmap [] (stack ++ #[.app p] ++ args.reverse.map (.app ·))
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
              goExp diag heap rhs lmap [] (stack ++ rargs.reverse.map (.app ·))
          | .neutral e lmap rs =>
            -- This implements eta-expansion of structure like values
            let typeName := ri.all[0]!
            if isStructureLike genv typeName then
              -- Only for non-Props
              let indInfo ← getConstInfoInduct typeName
              if (← Meta.isPropFormerType (← Meta.inferType (mkConst typeName (us.take indInfo.levelParams.length)))) then
                goVal diag heap (.neutral e lmap (rs.push se)) env stack
              else
                let numFields := getStructureLikeNumFields genv typeName
                let heap2 : Array (HeapElem × Env) := Array.ofFn (n := numFields) fun i =>
                  (.value (.neutral e lmap (rs.push (.proj typeName i))), env)
                let p := heap.size
                let heap' := heap ++ heap2
                assert! ri.rules.length = 1
                let rule := ri.rules[0]!
                assert! rule.nfields = numFields
                let rargs : Array Nat := args[:ri.numParams + ri.numMotives + ri.numMinors] ++
                  (Array.range numFields).map (·+p)
                let rhs := rule.rhs
                let lmap := lmap.push (ri.levelParams, us)
                goExp diag heap' rhs lmap [] (stack ++ rargs.reverse.map (.app ·))
            else
              goVal diag heap (.neutral e lmap (rs.push se)) env stack
          | _ => throwError "Cannot recurse with {ri.name} on value {v}"
        | .quotInfo qi =>
          unless qi.kind matches .ind || qi.kind matches .lift do
            throwError "Unexpected quotient kind {qi.name}"
          assert! args.size = 4 || args.size = 5
          match v with
          | .con cn _ _ _ps fs =>
            assert! cn = ``Quot.mk
            assert! fs.size = 1
            goPtr diag heap args[3]! (stack.push (.app fs.back))
          | .neutral e lmap rs =>
              goVal diag heap (.neutral e lmap (rs.push se)) env stack
          | _ => throwError "Cannot recurse with {qi.name} on value {v}"
        | _ => throwError "Unexpected {ci.name} in rec_"
      | .nfNat n =>
        match v with
        | .con cn _us _ _ps fs =>
          if cn = ``Nat.succ then
            assert! fs.size = 1
            goPtr diag heap fs[0]! (stack.push (.nfNat (n+1)))
          else if cn = ``Nat.zero then
            goVal diag heap (.lit (.natVal n)) env stack
          else
            throwError "Unexpected constructor in nfNat: {v}"
        | .lit (.natVal m) =>
            goVal diag heap (.lit (.natVal (m + n))) env stack
        | .neutral .. =>
          if n = 0 then
            goVal diag heap v env stack
          else
            assert! n > 0
            let p := heap.size
            let heap' := heap.push (.value v, env) ++
              Array.ofFn (n := n-1) fun i =>
                (.value (.con ``Nat.succ [] #[] #[] #[p + i]) , [])
            let p' := p + (n-1)
            goVal diag heap' (.con ``Nat.succ [] #[] #[] #[p']) [] stack
        | _ =>
            throwError "Unexpected value in nfNat: {v}"
      | .primNat f none =>
        match v with
        | .lit (.natVal m) =>
            goVal diag heap (.primNat f m) env stack
        | _ =>
          let some ci := genv.find? f | throwError "Did not find {f}"
          let val := ci.value!
          let p := heap.size
          let heap' := heap.push (.value v, env)
          goExp diag heap' val #[] [] (stack.push (.app p))
      | .primNat f (some m) =>
        match v with
        | .lit (.natVal n) =>
            goVal diag heap (evalPrimNat f m n) env stack
        | _ =>
          let some ci := genv.find? f | throwError "Did not find {f}"
          let val := ci.value!
          let p := heap.size
          let heap' := heap ++ #[(.value (.lit (.natVal m)), []), (.value v, env)]
          goExp diag heap' val #[] [] (stack ++ #[.app (p+1), .app p])

  | .exp =>
    let e : Expr := x1
    let lmap : LMap := x2
    -- IO.eprint s!"⊢ {e}\n"
    -- checkExprConf heap e lmap env stack
    if let some v ← toVal genv lmap e then
      goVal diag heap v env stack
    else
      match e with
      | .bvar i =>
        if let some p := env[i]? then
          goPtr diag heap p stack
        else
          throwError "Bound variable {i} out of scope"
      | .letE _n _t v b _ =>
        let p := heap.size
        let heap' := heap.push (.thunk v lmap, env)
        let env' := p :: env
        goExp diag heap' b lmap env' stack
      | .app f a =>
        if let .bvar i := a then
          if let some p := env[i]? then
            goExp diag heap f lmap env (stack.push (.app p))
          else
            throwError "Bound variable {i} out of scope"
        else
          let p := heap.size
          let heap' := heap.push (.thunk a lmap, env)
          goExp diag heap' f lmap env (stack.push (.app p))
      | .proj n i b =>
        let stack' := stack.push (.proj n i)
        goExp diag heap b lmap env stack'
      | .const n us => do
          let some ci := genv.find? n | throwError "Did not find {n}"
          if primNatFuns.contains n then
            -- IO.eprint s!"Unfolding {n} (primitive)\n"
            goVal diag heap (.primNat n none) [] stack
          else
          -- This simulated rewriting with unfolding lemmas, without actually
          -- materializing them
          match useUnfold, Lean.Elab.Structural.eqnInfoExt.find? genv n with
          | true, some eqnInfo =>
            -- IO.eprint s!"Unfolding {ci.name} using eqnInfo\n"
            let lmap := lmap.push (eqnInfo.levelParams, us)
            goExp diag heap eqnInfo.value lmap [] stack
          | _, _=>
          match ci with
          | .defnInfo ci | .thmInfo ci =>
            -- IO.eprint s!"Unfolding {ci.name}\n"
            let val := ci.value
            let lmap := lmap.push (ci.levelParams, us)
            goExp diag heap val lmap [] stack
          | _ => throwError "Unimplemented constant: {e}"
      | .fvar n => do
        match (← n.getDecl) with
        | .ldecl _ _ _ _ value _ _ =>
          goExp diag heap value lmap [] stack
        | _ =>
          goVal diag heap (.neutral e lmap #[]) env stack
      | .lam .. => unreachable!
      | .mdata _ e => goExp diag heap e lmap env stack
      | _ => throwError "Unimplemented: {toString e}"

end LazyWhnf

export LazyWhnf (lazyWhnf)

open Meta in
elab "#lazy_reduce" uf:"unfold"? t:term : command => Lean.Elab.Command.runTermElabM fun _ => do
  let e ← Lean.Elab.Term.elabTermAndSynthesize t none
  lambdaTelescope e fun _ e => do
    let (_diag, e'') ← lazyWhnf (← Lean.getEnv) (← Lean.getLCtx) e (useUnfold := uf.isSome)
    if false then
      withOptions (smartUnfolding.set ·  false) <| withTransparency .all do
        Meta.check e''
        unless (← Meta.isDefEq e e'') do
          throwError "Not defeq"
    Lean.logInfo m!"{e''}"

set_option linter.unusedVariables false
set_option pp.funBinderTypes true

/-- info: true -/
#guard_msgs in
#lazy_reduce id true

-- Tests sharing:
-- The `id (fun a => a)` should be reduced once, not twice, and the result
-- should not mention that redex anymore.

/-- info: fun (z : Bool) => (fun (a : Bool → Bool) => a) not z -/
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
/--
info: ((Nat.rec
        ⟨(fun (x : Nat) (f : Nat.below (motive := fun (x : Nat) => Nat → Nat) x) (x_1 : Nat) =>
              (match (motive := Nat → (x : Nat) → Nat.below (motive := fun (x : Nat) => Nat → Nat) x → Nat) x_1, x with
                | a, Nat.zero => fun (x : Nat.below (motive := fun (x : Nat) => Nat → Nat) Nat.zero) => a
                | a, b.succ => fun (x : Nat.below (motive := fun (x : Nat) => Nat → Nat) b.succ) => (x.1 a).succ)
                f)
            Nat.zero PUnit.unit,
          PUnit.unit⟩
        (fun (n : Nat) (n_ih : (fun (x : Nat) => Nat → Nat) n ×' Nat.below (motive := fun (x : Nat) => Nat → Nat) n) =>
          ⟨(fun (x : Nat) (f : Nat.below (motive := fun (x : Nat) => Nat → Nat) x) (x_1 : Nat) =>
                (match (motive := Nat → (x : Nat) → Nat.below (motive := fun (x : Nat) => Nat → Nat) x → Nat) x_1,
                    x with
                  | a, Nat.zero => fun (x : Nat.below (motive := fun (x : Nat) => Nat → Nat) Nat.zero) => a
                  | a, b.succ => fun (x : Nat.below (motive := fun (x : Nat) => Nat → Nat) b.succ) => (x.1 a).succ)
                  f)
              n.succ n_ih,
            n_ih⟩)
        aNat).1
    43).succ
-/
#guard_msgs in
#lazy_reduce Nat.add (Nat.succ 42) (Nat.succ aNat)

/-- info: true -/
#guard_msgs in
#lazy_reduce Nat.ble 10 (aNat+20)

universe u uu

set_option pp.universes true in
/-- info: List.cons.{uu} c (List.cons.{uu} b (List.cons.{uu} a List.nil.{uu})) -/
#guard_msgs in
#lazy_reduce fun (α : Type uu) (a b c : α) => List.reverse [a,b,c]

namespace Levels
def foo1.{u1} := List.{u1+1}
def foo2.{u2,u3} := foo1.{max u2 u3}

set_option pp.universes true in
/-- info: List.{(max uu u) + 1} -/
#guard_msgs in
#lazy_reduce foo2.{uu,u}

end Levels

-- Tests nat operations on open terms

/-- info: isFalse ⋯ -/
#guard_msgs in
#lazy_reduce fun k => instDecidableEqNat (0 + k + 1) 0


-- The kernel eta-expands the argument to Fin.rec here, so we need to do that too

/-- info: ⟨x.1 + 1, ⋯⟩ -/
#guard_msgs in
#lazy_reduce fun (n : Nat) (x: Fin n) => x.succ

-- The kernel does no such eta-expansion for props

axiom andAx : True ∧ True

/-- info: And.rec (fun (a x : True) => a) andAx -/
#guard_msgs in
#lazy_reduce andAx.rec (motive := fun _ => True) (fun a _ => a)
