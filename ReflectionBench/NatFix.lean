def Nat.fix {motive : α → Sort u} (h : α → Nat) (F : (x : α) → ((y : α) → h y < h x → motive y) → motive x) : (x : α) → motive x :=
  let rec go : ∀ (fuel : Nat) (x : α), (h x < fuel) → motive x := Nat.rec
    (fun _ hfuel => (not_succ_le_zero _ hfuel).elim)
    (fun _ ih x hfuel => F x (fun y hy => ih y (Nat.lt_of_lt_of_le hy (Nat.le_of_lt_add_one hfuel))))
  fun x => go (h x + 1) x (Nat.lt_add_one _)
