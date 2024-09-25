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

/-
set_option trace.profiler true in
def test1 : ∀ n < 2^exp, list.get? n = Option.some n := by decide
-- 3.301 s

set_option trace.profiler true in
def test2 : ∀ n < 2^exp, list.get? n = Option.some n := by unfold list; prove_list_tac
-- 0.928 s

-/

/-
-- Could build the same proof object using tactics, but too slow

set_option trace.profiler true in
def test3 : ∀ n < 2^exp, list.get? n = Option.some n := by
  unfold list
  (repeat apply forall_succ) <;> (try apply forall_zero)
  repeat (first | exact list_head | apply list_tail)
-/

def test : Bool := decide (∀ n < 2^exp, list.get? n = Option.some n)

#time #kernel_reduce   test
#time #kernel_reduce   test
#time #lazy_reduce test
#time #lazy_reduce test
#time #lazy_reduce unfold test
#time #lazy_reduce unfold test
