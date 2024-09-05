import Lean

open Lean

abbrev Env := List Nat

inductive StackElem
  | app : Nat → StackElem
  | proj : Nat → StackElem
  | upd : Nat → StackElem
  | rec_ : RecursorVal → List Level → Array Nat → StackElem
deriving Inhabited

instance : ToString StackElem where
  toString
    | .app n => s!"@{n}"
    | .proj n => s!".{n}"
    | .upd n => s!"upd {n}"
    | .rec_ ci _ _ => s!"#{ci.name}"

abbrev Stack := Array StackElem

set_option stderrAsMessages false

inductive Val
  | con : ConstructorVal → List Level → Array Nat → Val -- primitive, maybe partially applied
  | rec_ : RecursorVal → List Level → Array Nat → Val -- primitive, maybe partially applied
  -- | vlam : Nat → Val → Val
  | elam : Name → Expr → Expr → BinderInfo → Val
  | lit : Lean.Literal → Val

def Val.toString : Val → String
  | .con ci _ as => s!"{ci.name} {as}"
  -- | .vlam n v => s!"λ^{n} ({v.toString})"
  | .rec_ ci _ as => s!"{ci.name} {as}"
  | .elam n _ e _ => s!"λ {n}. {e}"
  | .lit l => (repr l).pretty

instance : ToString Val where toString := Val.toString

inductive HeapElem
  | thunk : Expr → HeapElem
  | value : Val → HeapElem
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
        return .some (.con ci us #[])
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
  | .con ci us args => return mkAppN (.const ci.name us) (← args.mapM (ofPos heap ·))
  | .rec_ ci us args => return mkAppN (.const ci.name us) (← args.mapM (ofPos heap ·))
  | .elam n t b bi => return (Expr.lam n t b bi).instantiate (← env.toArray.mapM (ofPos heap ·))
  | .lit t => return .lit t

partial def ofPos (heap : Heap) (p : Nat) : MetaM Expr := do
  let (he, env) := heap[p]!
  match he with
  | .thunk e => return e.instantiate (← env.toArray.mapM (ofPos heap ·))
  | .value v => ofVal heap v env
end

mutual

partial def stepPos (genv : Environment) (lctx : LocalContext)
    (heap : Heap) (p : Nat) (stack : Stack) : MetaM Expr := do
  let (he, env') := heap[p]!
  let stack' := stack.push (.upd p)
  match he with
  | .thunk e' => stepExpr genv lctx heap e' env' stack'
  | .value v => stepVal genv lctx heap v env' stack'

partial def stepVal (genv : Environment) (lctx : LocalContext)
  (heap : Heap) (v : Val) (env : Env) (stack : Stack) : MetaM Expr := do
    if stack.isEmpty then
      ofVal heap v env
    else
      let se := stack.back
      IO.eprint s!"{se} ⊢ ({v})\n"
      /-
      IO.eprint s!"{se} ⊢ ({← ofVal heap v env})\n"
      unless (← Meta.withLCtx lctx {} (Meta.isTypeCorrect (← ofVal heap v env))) do
        IO.eprint s!"not typecorrect\n"
        Meta.check (← ofVal heap v env)
      -/
      match se with
      | .upd p =>
        let heap' := heap.set! p (.value v, env)
        stepVal genv lctx heap' v env stack.pop
      | .app p =>
        match v with
        | .con ci us args =>
          if args.size < ci.arity then
            stepVal genv lctx heap (.con ci us (args.push p)) env stack.pop
          else
            throwError "Constructor is over-applied: {← ofVal heap v env}"
        | .rec_ ci us args =>
          if args.size  < ci.arity then
            stepVal genv lctx heap (.rec_ ci us (args.push p)) env stack.pop
          else if args.size == ci.arity then
            stepPos genv lctx heap p (stack.pop.push (.rec_ ci us args))
          else
            throwError "Over-applied recursor?"
        -- | .vlam (n+1) v' =>
        --  stepVal genv lctx heap (.vlam n v') (p :: env) stack.pop
        | .elam _ _ e' _ =>
          stepExpr genv lctx heap e' (p :: env) stack.pop
        | _ => throwError "Cannot apply value {v}"
      | .proj idx =>
        match v with
        | .con ci _ fields =>
          if let some p := fields[ci.numParams + idx]? then
            stepPos genv lctx heap p stack.pop
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
              stepExpr genv lctx heap rhs [] (stack.pop ++ args.reverse.map (.app ·))
            else
              let p := heap.size
              let heap' := heap.push (.value (.lit (.natVal (n-1))), [])
              let rhs := ri.rules[1]!.rhs
              let rhs := rhs.instantiateLevelParams ri.levelParams us
              stepExpr genv lctx heap' rhs [] (stack.pop ++ #[.app p] ++ args.reverse.map (.app ·))
          else
            throwError "Cannot recurse on literal"
        | .con ci _ cargs =>
          let some rule := ri.rules.find? (·.ctor == ci.name)
            | throwError "Unexpected constructor {ci.name} for recursor {ri.name}"
          unless cargs.size = ci.arity do
            throwError "Unsaturated constuctor {ci.name} analyzsed by {ci.name}"
          unless rule.nfields = ci.numFields do
            throwError "Arity mismatch: {ci.name} has {ci.numFields} but {ri.name} expects {rule.nfields}"
          let rargs := args ++ cargs[ci.numParams:]
          let rhs := rule.rhs.instantiateLevelParams ri.levelParams us
          stepExpr genv lctx heap rhs [] (stack.pop ++ rargs.reverse.map (.app ·))
        | _ => throwError "Cannot recurse with {ri.name} on value {v}"


partial def stepExpr (genv : Environment) (lctx : LocalContext)
    (heap : Heap) (e : Expr) (env : Env) (stack : Stack) : MetaM Expr := do
  IO.eprint s!"⊢ {e}\n"
  if let some v ← toVal genv e then
    stepVal genv lctx heap v env stack
  else
    match e with
    | .bvar i =>
      if let some p := env[i]? then
        let (he, env') := heap[p]!
        let stack' := stack.push (.upd p)
        match he with
        | .thunk e' => stepExpr genv lctx heap e' env' stack'
        | .value v => stepVal genv lctx heap v env' stack'
      else
        throwError "Local variable {i} not supported yet (env: {env})"
    | .letE _n _t v b _ =>
      let p := heap.size
      let heap' := heap.push (.thunk v, env)
      let env' := p :: env
      stepExpr genv lctx heap' b env' stack
    | .app f a =>
      let p := heap.size
      let heap' := heap.push (.thunk a, env)
      let stack' := stack.push (.app p)
      stepExpr genv lctx heap' f env stack'
    | .proj _ i b =>
      let stack' := stack.push (.proj i)
      stepExpr genv lctx heap b env stack'
    | .const n us => do
        let some ci := genv.find? n | throwError "Did not find {n}"
        match ci with
        | .defnInfo ci =>
          -- IO.eprint s!"Unfolding {ci.name}\n"
          stepExpr genv lctx heap (ci.value.instantiateLevelParams ci.levelParams us) env stack
        | .thmInfo ci =>
          -- IO.eprint s!"Unfolding {ci.name}\n"
          stepExpr genv lctx heap (ci.value.instantiateLevelParams ci.levelParams us) env stack
        | _ => throwError "Unimplemented constant: {e}"
    | .lam .. => unreachable!
    | _ => throwError "Unimplemented: {e}"

end

def lazyWhnf (genv : Environment) (lctx : LocalContext) (e : Expr) : MetaM Expr := do
  stepExpr genv lctx #[] e [] #[]
