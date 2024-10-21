import Lean
import ReflectionBench.TypeChecker

open Lean

elab "#lean4lean_reduce" t:term : command => Lean.Elab.Command.runTermElabM fun _ => do
  let e ← Lean.Elab.Term.elabTermAndSynthesize t none
  Lean.Meta.lambdaTelescope e fun _ e => do
    let e ← TypeChecker.M.run (← getEnv) .safe  (← getLCtx) do
        TypeChecker.whnf e
    let e' ← Lean.ofExceptKernelException e
    Lean.logInfo m!"{e'}"

/-- info: isFalse ⋯ -/
#guard_msgs in
#lean4lean_reduce fun k => instDecidableEqNat (0 + k + 1) 0

/-- info: ⟨x.1 + 1, ⋯⟩ -/
#guard_msgs in
#lean4lean_reduce fun (n : Nat) (x: Fin n) => x.succ
