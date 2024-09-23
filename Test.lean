import Mathlib.GroupTheory.SpecificGroups.Alternating
import ReflectionBench.LazyWHNF
import ReflectionBench.KernelReduce

set_option stderrAsMessages false

#lazy_reduce decide ((Equiv.swap 0 2 * Equiv.swap 0 1 * (Equiv.swap 0 4 * Equiv.swap 1 3) * (Equiv.swap 0 2 * Equiv.swap 0 1)⁻¹ *
      (Equiv.swap 0 4 * Equiv.swap 1 3)⁻¹ =
    finRotate 5))
