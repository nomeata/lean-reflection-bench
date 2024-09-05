import Lean

open Lean

abbrev Env := List Nat

inductive StackElem
  | app : Nat → StackElem
  | proj : Nat → StackElem
  | upd : Nat → StackElem
  | rec_ : RecursorVal → Array Nat → Env → StackElem
deriving Inhabited

instance : ToString StackElem where
  toString
    | .app n => s!"@{n}"
    | .proj n => s!".{n}"
    | .upd n => s!"#{n}"
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

def Lean.RecursorVal.arity (ci : RecursorVal) : Nat :=
  ci.numParams + ci.numMotives + ci.numMinors + ci.numIndices + 1

partial def toVal (genv : Environment) : Expr → MetaM (Option Val)
  | .lam n t e bi => do
    return .some (.elam n t e bi)
  | .const n us => do
      let some ci := genv.find? n | throwError "Did not find {n}"
      match ci with
      | .defnInfo _ =>
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
partial def ofVal (heap : Heap) (v : Val) (_env : Env) : MetaM Expr := do match v with
  | .con ci us args => return mkAppN (.const ci.name us) (← args.mapM (ofPos heap ·))
  | .rec_ ci us args => return mkAppN (.const ci.name us) (← args.mapM (ofPos heap ·))
  | .elam n t b bi => return .lam n t b bi
  | .lit t => return .lit t

partial def ofPos (heap : Heap) (p : Nat) : MetaM Expr := do
  let (he, env') := heap[p]!
  match he with
  | .thunk e => return e -- TODO: What with env? Need to let-bind perhaps?
  | .value v => ofVal heap v env'
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
      IO.eprint s!"⊢ ({v}) {se}\n"
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
            throwError "Constructor is over-applied"
        | .rec_ ci us args =>
          if args.size + 1 < ci.arity then
            stepVal genv lctx heap (.rec_ ci us (args.push p)) env stack.pop
          else if args.size + 1 == ci.arity then
            stepPos genv lctx heap p (stack.pop.push (.rec_ ci args env))
          else
            throwError "Over-applied recursor?"
        -- | .vlam (n+1) v' =>
        --  stepVal genv lctx heap (.vlam n v') (p :: env) stack.pop
        | .elam _ _ e' _ =>
          stepExpr genv lctx heap e' (p :: env) stack.pop
        | _ => throwError "Cannot apply value"
      | .proj idx =>
        match v with
        | .con ci _ fields =>
          if let some p := fields[ci.numParams + idx]? then
            stepPos genv lctx heap p stack.pop
          else
            throwError "Projection out of range"
        | _ => throwError "Cannot project value"
      | .rec_ ci args env' =>
        match v with
        | .lit (.natVal n) =>
          if ci.name = ``Nat.rec then
            if n = 0 then
              stepExpr genv lctx heap ci.rules[0]!.rhs env' (stack ++ args.map (.app ·))
            else
              let p := heap.size
              let heap' := heap.push (.value (.lit (.natVal (n-1))), [])
              stepExpr genv lctx heap' ci.rules[1]!.rhs env' (stack ++ args.map (.app ·) ++ #[.app p])
          else
            throwError "Cannot recurse on literal"
        | _ => throwError "Cannot recurse on value {v}"



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
    | .app f a =>
      let p := heap.size
      let heap' := heap.push (.thunk a, env)
      let stack' := stack.push (.app p)
      stepExpr genv lctx heap' f env stack'
    | .proj _ i b =>
      let stack' := stack.push (.proj i)
      stepExpr genv lctx heap b env stack'
    | .const n _us => do
        let some ci := genv.find? n | throwError "Did not find {n}"
        match ci with
        | .defnInfo ci =>
          stepExpr genv lctx heap ci.value env stack
        | _ => throwError "Unimplemented constant: {e}"
    | .lam .. => unreachable!
    | _ => throwError "Unimplemented: {e}"

end

def lazyWhnf (genv : Environment) (lctx : LocalContext) (e : Expr) : MetaM Expr := do
  stepExpr genv lctx #[] e [] #[]
