import ReflectionBench.Sqrt

theorem minFac_lemma (n k : Nat) (h : ¬n < k * k) : sqrt2 n - k < sqrt2 n + 2 - k :=
  sorry

def minFacAux (n : Nat) : Nat → Nat :=
  Nat.fix (fun k => sqrt2 n + 2 - k) fun k ih =>
    if h : n < k * k then n
    else
      if k ∣ n then k
      else
        ih (k + 2) (by simp_wf; apply minFac_lemma n k; assumption)

#time
#kernel_reduce minFacAux  524287 3
-- #kernel_reduce minFacAux  2147483647 3
