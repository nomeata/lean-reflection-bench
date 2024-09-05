import ReflectionBench.NatFix
import ReflectionBench.KernelReduce

def sqrt2 (n : Nat) : Nat :=
  if n ≤ 1 then n else
  iter (n / 2)
where
  iter : Nat → Nat := Nat.fix (fun guess => guess) (fun guess ih =>
    let next := (guess + n / guess) / 2
    if _h : next < guess then
      ih next (by decreasing_tactic)
    else
      guess
  )

def sqrtTest (n : Nat) : Bool := sqrt2 (n * n) == n

-- #time
-- #kernel_reduce sqrtTest 1000000000000
-- #kernel_reduce sqrtTest 2
#kernel_reduce sqrtTest 2

-- #kernel_reduce (1 : Nat).succ

-- #check Bool.rec

/-
run_meta
  let ci ← Lean.getConstInfoRec ``Nat.rec
  Lean.logInfo m!"{ci.rules[1]!.rhs}"
-/
