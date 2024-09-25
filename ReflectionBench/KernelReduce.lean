import Lean
import ReflectionBench.LazyWHNF
import ReflectionBench.LazyNbE

elab "#kernel_reduce" t:term : command => Lean.Elab.Command.runTermElabM fun _ => do
  let e ← Lean.Elab.Term.elabTermAndSynthesize t none
  Lean.Meta.lambdaTelescope e fun _ e => do
    let e' ← Lean.ofExceptKernelException <| Lean.Kernel.whnf (← Lean.getEnv) (← Lean.getLCtx) e
    Lean.logInfo m!"{e'}"

/-- info: isFalse ⋯ -/
#guard_msgs in
#kernel_reduce fun k => instDecidableEqNat (0 + k + 1) 0
