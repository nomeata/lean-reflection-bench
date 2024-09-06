import ReflectionBench.KernelReduce

-- https://leanprover.zulipchat.com/#narrow/stream/239415-metaprogramming-.2F-tactics/topic/An.20interval.20tactic.20for.20constant.20real.20inequalities

def Nat.fix (h : α → Nat) {motive : α → Sort u}  (F : (x : α) → ((y : α) → h y < h x → motive y) → motive x) : (x : α) → motive x :=
  let rec go : ∀ (fuel : Nat) (x : α), (h x < fuel) → motive x := Nat.rec
    (fun _ hfuel => (not_succ_le_zero _ hfuel).elim)
    (fun _ ih x hfuel => F x (fun y hy => ih y (Nat.lt_of_lt_of_le hy (Nat.le_of_lt_add_one hfuel))))
  fun x => go (h x + 1) x (Nat.lt_add_one _)

def Nat.log2' : Nat → Nat := Nat.fix (fun n => n) (fun n ih => if h : n ≥ 2 then ih (n / 2) (log2_terminates _ ‹_›) + 1 else 0)

-- #kernel_reduce Nat.log2' 956588586188586504152503510242497262758674667026601
