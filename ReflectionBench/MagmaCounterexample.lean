import Lean
import ReflectionBench.KernelReduce
import ReflectionBench.LazyWHNF
import ReflectionBench.MemoFinOp

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
/-- `a ◇ b` computes a binary operation of `a` and `b`. -/
op : α → α → α

-- We use abbrev here so that type class search, in particular `by decide` can look through them

@[inherit_doc] infixl:65 " ◇ "   => Magma.op
abbrev Equation1 (G: Type _) [Magma G] := ∀ x : G, x = x
abbrev Equation411 (G: Type _) [Magma G] := ∀ x : G, x = x ◇ (x ◇ (x ◇ (x ◇ x)))
abbrev Equation412 (G: Type _) [Magma G] := ∀ x y : G, x = x ◇ (x ◇ (x ◇ (x ◇ y)))
abbrev Equation413 (G: Type _) [Magma G] := ∀ x y : G, x = x ◇ (x ◇ (x ◇ (y ◇ x)))
abbrev Equation429 (G: Type _) [Magma G] := ∀ x y : G, x = x ◇ (y ◇ (x ◇ (y ◇ x)))
abbrev Equation473 (G: Type _) [Magma G] := ∀ x y : G, x = y ◇ (x ◇ (y ◇ (x ◇ x)))
abbrev Equation3167 (G: Type _) [Magma G] := ∀ x y z : G, x = (((y ◇ y) ◇ z) ◇ z) ◇ x
abbrev Equation2531 (G: Type _) [Magma G] := ∀ x y : G, x = (y ◇ ((y ◇ x) ◇ x)) ◇ y


-- from equational_theories/FinitePoly/Refutation212.lean
def M : Magma (Fin 20) where
  op x y := 4 * x*x + 2 * x + 2 * y

def table : Nat := 176572862725894008122698639442158340463570358062018791456284713065412594783123644086682432661794684073102303331486778326370940525772356431236683795848309863276639424307474540043134479302998

def M2 : Magma (Fin 13) where
  op := MemeFinOp.opOfTable table

def exampleComputation : Bool := decide (@Equation2531 _ M2)


def Fin.all {n : Nat} (P : ∀ i < n, Bool) : Bool :=
  Nat.rec true (fun i ih => P i sorry && ih) n

theorem Fin.decideAll_to_Fin.all {n : Nat} {P : Fin n → Prop} [DecidablePred P] :
    decide (∀ x, P x) = Fin.all (fun i h => decide (P ⟨i, h⟩)) := by
  sorry

def Nat.all_below {n : Nat} (P : Nat → Bool) : Bool :=
  Nat.rec true (fun i ih => P i && ih) n

/-- The following makes simp throw a type error! -/
-- @[simp]
theorem foo1' {n : Nat} {P : Fin n → Prop} [DecidablePred P]
  (P' : Nat → Bool) (hP : ∀ i h, decide (P ⟨i, h⟩) = P' i):
    decide (∀ x, P x) = n.all_below P' := by
  sorry

theorem Fin.decideEq_to_Nat {n : Nat} {x y : Fin n} :
  decide (x = y) = decide (x.val = y.val) := by sorry

theorem Nat.decideEq_to_beq {x y : Nat} :
  decide (x = y) = (Nat.beq x y) := by sorry

-- attribute [simp] table

set_option maxRecDepth 2000

open Lean Elab Meta in
elab "optimize" t:term : term  <= expectedType? => do
  let e ← Lean.Elab.Term.elabTermAndSynthesize t expectedType?
  let ctx ← Simp.Context.mkDefault
  let (res, _stats) ← simp e ctx
  return res.expr


-- set_option pp.explicit true


#time #guard_msgs(drop all) in #reduce exampleComputation
#time #guard_msgs(drop all) in #kernel_reduce exampleComputation
#time #guard_msgs(drop all) in #lazy_reduce exampleComputation

attribute [simp] exampleComputation Fin.decideAll_to_Fin.all

def betterComputation1 : Bool := optimize exampleComputation

#time #guard_msgs(drop all) in #reduce betterComputation1
#time #guard_msgs(drop all) in #kernel_reduce betterComputation1
#time #guard_msgs(drop all) in #lazy_reduce betterComputation1

attribute [simp] Magma.op M2 MemeFinOp.opOfTable

def betterComputation2 : Bool := optimize exampleComputation

#time #guard_msgs(drop all) in #reduce betterComputation2
#time #guard_msgs(drop all) in #kernel_reduce betterComputation2
#time #guard_msgs(drop all) in #lazy_reduce betterComputation2

attribute [-simp] Nat.add_eq Nat.pow_eq Nat.mul_eq
attribute [simp] instHAdd instHMul instAddNat instMulNat instHPow instPowNat instNatPowNat
attribute [simp] instHMod Nat.instMod instHDiv Nat.instDiv
attribute [simp] Nat.decideEq_to_beq

def betterComputation3: Bool := optimize exampleComputation
#print betterComputation3

#time #guard_msgs(drop all) in #reduce betterComputation3
#time #guard_msgs(drop all) in #kernel_reduce betterComputation3
#time #guard_msgs(drop all) in #lazy_reduce betterComputation3

attribute [simp] exampleComputation Magma.op M2 MemeFinOp.opOfTable Equation2531
attribute [simp] Fin.decideAll_to_Fin.all Fin.all
