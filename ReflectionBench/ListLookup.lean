import ReflectionBench.KernelReduce
import Lean
import Qq

open Lean

def exp : Nat := 8

def list : List Nat := by
  run_tac
    let goal ← Elab.Tactic.getMainGoal
    let l := List.range (2^exp)
    goal.assign (toExpr l)

set_option maxRecDepth 2000

theorem list_head {l : List Nat} {a} : (a::l).get? 0 = some a := rfl
theorem list_tail {l : List Nat} {n a b} (h : l.get? n = some a) :
  (b::l).get? n.succ = some a := h ▸ rfl

section MariosExample

open Qq

def proveList (n : Nat) (l : Q(List Nat)) : MetaM ((a : Q(Nat)) × Q(($l).get? $n = some $a)) := do
  let .app (.app _ (a : Q(Nat))) (l' : Q(List Nat)) := l | failure
  show MetaM ((b : Q(Nat)) × Q(($a :: $l').get? $n = some $b)) from do
  match n with
  | 0 => pure ⟨a, q(list_head)⟩
  | n+1 =>
    let ⟨b, p⟩ ← proveList n l'
    pure ⟨b, q(list_tail $p)⟩

theorem forall_zero {P : Nat → Prop} : ∀ a < 0, P a := by simp
theorem forall_succ {P : Nat → Prop} {n} (H1 : ∀ a < n, P a) (H2 : P n) :
    ∀ a < n.succ, P a := by
  intro a h
  cases Nat.lt_succ_iff_lt_or_eq.1 h with
  | inl h => exact H1 _ h
  | inr h => exact h ▸ H2

def proveForall (P : Q(Nat → Prop))
    (H : ∀ a : Nat, MetaM Q($P $a)) (n : Nat) : MetaM (Q(∀ n < $n, $P n)) := do
  match n with
  | 0 => pure q(forall_zero)
  | n+1 =>
    let H1 ← proveForall P H n
    let H2 ← H n
    pure q(forall_succ $H1 $H2)

elab "prove_list_tac" : tactic =>
  Elab.Tactic.liftMetaTactic1 fun g => do
  let x : Q(Prop) ← g.getType'
  let ~q(∀ x < $n, List.get? (α := Nat) $l x = some x) := x | failure
  let n ← unsafe Meta.evalExpr Nat q(Nat) n
  let p ← proveForall q(fun x => List.get? (α := Nat) $l x = some x) (fun x => (·.2) <$> proveList x l) n
  g.assign p
  pure none

set_option maxRecDepth 2000

#time
def test_decide : ∀ n < 2^exp, list.get? n = Option.some n := by decide
-- 3.601 s

#time
def test_native_decide : ∀ n < 2^exp, list.get? n = Option.some n := by native_decide
-- 20ms

#time
def testM2 : ∀ n < 2^exp, list.get? n = Option.some n := by unfold list; prove_list_tac

-- #print testM2

end MariosExample


/-
A variant that could (hopefully) be automated.
-/

/-
def get? : (as : List α) → (i : Nat) → Option α
  | a::_,  0   => some a
  | _::as, n+1 => get? as n
  | _,     _   => none
-/

-- An aux defintion to avoid nesting an app in an eq, but does not seem to make a big difference
def List.get?_eq α as i r := @List.get? α as i = r

theorem List.get?_eq_nil : List.get?_eq α [] n none := rfl
theorem List.get?_eq_cons_zero : List.get?_eq α (a::l) 0 (some a) := rfl
-- NB: Writing n.succ instead of n+1 here makes a big difference (22% improvement)
theorem List.get?_eq_cons_succ α a l n r :
  get? l n = r → @get? α (a::l) n.succ = r :=
    fun h => Eq.trans (@get?_cons_succ α a l n) h

def List.get?' (u : Level) (αE asE : Expr) : (as : List α) → (i : Nat) → (Option α × Expr × Expr)
  | a::_,  0  =>
    (some a,
    mkApp2 (.const ``Option.some [u]) αE asE.appFn!.appArg!,
    mkApp3 (.const ``get?_eq_cons_zero [u]) αE asE.appFn!.appArg! asE.appArg!)
  | _::as, n+1 =>
    let (r, rE, p) := get?' u αE asE.appArg! as n
    -- Using mkRawNatLit also important, 18%
    (r, rE, mkApp6 (.const ``List.get?_eq_cons_succ [u]) αE asE.appFn!.appArg! asE.appArg! (mkRawNatLit n) rE p)
  | [],     n   =>
    (none,
    mkApp (.const ``Option.none [u]) αE,
    mkApp2 (.const ``get?_eq_nil [u]) αE (mkRawNatLit n))

def Nat.forall_upto (P : Nat → Prop) : Nat → Prop
  | 0 => True
  | n+1 => P n ∧ Nat.forall_upto P n

theorem Nat.forall_upto_zero P : Nat.forall_upto P 0 := True.intro
theorem Nat.forall_upto_succ P n (hP : P n) (h2 : Nat.forall_upto P n) :
  Nat.forall_upto P (n.succ) := And.intro hP h2

def Nat.forall_upto' (PE : Expr) (mkPE : Nat → Expr) : Nat → Expr
  | 0 => mkApp (.const ``Nat.forall_upto_zero []) PE
  | n+1 =>
    let h1 := mkPE n
    let h2 := Nat.forall_upto' PE mkPE n
    mkApp4 (.const ``Nat.forall_upto_succ []) PE (mkNatLit n) h1 h2

def testUpto (n : Nat) : Prop := Nat.forall_upto (fun i => list.get? i = Option.some i) n

def testUpto_intro (n : Nat)
  (h : Nat.forall_upto (fun i => list.get? i = Option.some i) n) :
  (testUpto n) := h


def testUpto' (n : Nat): Expr :=
  let natE := mkConst ``Nat
  -- let listE := mkConst ``list
  let listVE := toExpr list
  let PE := mkLambda `i .default natE <|
    mkApp3 (mkConst ``Eq [1])
      (mkApp (.const ``Option [0]) natE)
      (mkApp3 (.const ``List.get? [0]) natE listVE (.bvar 0))
      (mkApp2 (.const ``Option.some [0]) natE (.bvar 0))
  let h := Nat.forall_upto' PE (fun i =>
    let (_, _, p) := List.get?' 0 natE listVE list i
    p) n
  mkApp2 (mkConst ``testUpto_intro) (mkNatLit n) h
  -- h

elab "prove_testUpto" : tactic =>
  Elab.Tactic.closeMainGoalUsing `test fun t => do
    let_expr testUpto nE := t | throwError "Unexpected"
    let n ← unsafe Meta.evalExpr Nat (mkConst ``Nat) nE
    return testUpto' n

-- set_option diagnostics true
-- set_option diagnostics.threshold 0
-- set_option trace.profiler true in
#time
theorem test : testUpto (2^exp) := by prove_testUpto

-- #print test

/-
-- Could build the same proof object using tactics, but too slow

set_option trace.profiler true in
def test3 : ∀ n < 2^exp, list.get? n = Option.some n := by
  unfold list
  (repeat apply forall_succ) <;> (try apply forall_zero)
  repeat (first | exact list_head | apply list_tail)
-/

def test2 : Bool := decide (∀ n < 2^exp, list.get? n = Option.some n)


#time #kernel_reduce   test2
#time #lazy_reduce test2
#time #lazy_reduce unfold test2


-- This models what’s achievable using the `rsimp` machinery

def Nat.all_below (n : Nat) (P : Nat → Bool) : Bool :=
  Nat.rec true (fun i ih => P i && ih) n

noncomputable def List.get?_rsimp (as : List α) : Nat → Option α :=
  as.rec
    (fun _ => none)
    (fun a _as ih i => i.rec (some a) (fun n _ => ih n))

noncomputable
def testRSimpType : Bool :=
    Nat.all_below (2^exp) fun i =>
    decide (list.get?_rsimp i = some i)

-- This should be roughly as fast as the following #kernel_reduce
#time
def testRSimp : testRSimpType := by
  run_tac
    Elab.Tactic.closeMainGoalUsing `foo fun _ =>
      Meta.mkEqRefl (mkConst ``true)

#time #kernel_reduce testRSimpType
#time #lazy_reduce testRSimpType
