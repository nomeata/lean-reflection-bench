import Lean
-- import ReflectionBench.KernelReduce
-- import ReflectionBench.LazyWHNF

section DecideBang

open Lean Elab Tactic Meta

private def preprocessPropToDecide (expectedType : Expr) : TermElabM Expr := do
  let mut expectedType ← instantiateMVars expectedType
  if expectedType.hasFVar then
    expectedType ← zetaReduce expectedType
  if expectedType.hasFVar || expectedType.hasMVar then
    throwError "expected type must not contain free or meta variables{indentExpr expectedType}"
  return expectedType

private def splitConjs (e : Lean.Expr) : Array (Lean.Expr) := Id.run do
  let mut e := e
  let mut r := #[]
  while e.isAppOf `And do
    r := r.push e.appFn!.appArg!
    e := e.appArg!
  r := r.push e
  return r

private partial def inferDecideFin (p : Expr) : MetaM Expr := do
  let p ← whnfR p
  match p with
  | .forallE i d b bi =>
    match_expr (← whnfR d) with
    | Fin n =>
      let inst ← withLocalDeclD i d fun x => do
        let body := b.instantiate1 x
        let inst ← inferDecideFin body
        mkLambdaFVars #[x] inst
      return mkApp3 (mkConst ``Nat.decidableForallFin) n (.lam i d b bi) inst
    | _ => throwError "Expected Fin n quantifier"
  | _ =>
    match_expr p with
    | Not p' =>
      let inst ← inferDecideFin p'
      return mkApp2 (mkConst ``instDecidableNot) p' inst
    | Eq t l r =>
      match_expr (← whnfR t) with
      | Fin n =>
        return mkApp3 (mkConst ``instDecidableEqFin) n l r
      | _ => throwError "Expected Fin n equality"
    | _ => throwError "Unsupported propositoin"


/-!
Like `decide!`, but only supports goals that are conjunctions of (possibly negations of) goals
of the form `∀ (x … z : Fin n), lhs = rhs`.

Using type class synthesis to infer the decidability instances can be very slow, slower than the
actual proof checking, so this tactic construts the instances very directly.
-/
elab "decideFin!" : tactic => do
  closeMainGoalUsing `decideFin fun expectedType => do
    let expectedType ← preprocessPropToDecide expectedType
    let expectedTypes := splitConjs expectedType
    let proofs ← expectedTypes.mapM fun expectedType => do
      let s ← inferDecideFin expectedType
      let rflPrf ← mkEqRefl (toExpr true)
      return mkApp3 (Lean.mkConst ``of_decide_eq_true) expectedType s rflPrf
    let proof ← proofs.pop.foldrM (mkAppM ``And.intro #[·, ·]) proofs.back
    check proof
    return proof

end DecideBang

universe u

class Magma (α : Type u) where
/-- `a ∘ b` computes a binary operation of `a` and `b`. -/
op : α → α → α

-- We use abbrev here so that type class search, in particular `by decide` can look through them

@[inherit_doc] infixl:65 " ∘ "   => Magma.op
abbrev Equation1 (G: Type _) [Magma G] := ∀ x : G, x = x
abbrev Equation411 (G: Type _) [Magma G] := ∀ x : G, x = x ∘ (x ∘ (x ∘ (x ∘ x)))
abbrev Equation412 (G: Type _) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ (x ∘ (x ∘ y)))
abbrev Equation413 (G: Type _) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ (x ∘ (y ∘ x)))
abbrev Equation429 (G: Type _) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ (x ∘ (y ∘ x)))
abbrev Equation473 (G: Type _) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ (y ∘ (x ∘ x)))



-- from equational_theories/FinitePoly/Refutation212.lean
def M : Magma (Fin 5) where
  op x y := 4 * x*x + 2 * x + 2 * y

theorem MFacts : @Equation411 _ M ∧ @Equation429 _ M ∧ @Equation473 _ M := by
  decide

--#time #lazy_reduce decide (@Equation411 _ M)
--#time #kernel_reduce decide (@Equation411 _ M)
