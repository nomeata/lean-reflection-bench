import Lean
import ReflectionBench.LazyWHNF
import ReflectionBench.LazyNbE

elab "#kernel_reduce" t:term : command => Lean.Elab.Command.runTermElabM fun _ => do
  let e ← Lean.Elab.Term.elabTermAndSynthesize t none
  let e' ← Lean.ofExceptKernelException <| Lean.Kernel.whnf (← Lean.getEnv) (← Lean.getLCtx) e
  Lean.logInfo m!"{e'}"
