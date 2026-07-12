import Mathlib
noncomputable section
universe u
section
variable {G : Type u} [Group G] [Finite G]
-- orderOf (g^q) = m when q*m = orderOf g, q ∣ orderOf g
example (g : G) (q m : ℕ) (hq : q ≠ 0) (hm : m ≠ 0) (hqm : q * m = orderOf g) :
    orderOf ((g : G) ^ q) = m := by
  have hqdvd : q ∣ orderOf g := ⟨m, hqm.symm⟩
  rw [orderOf_pow_of_dvd hq hqdvd, ← hqm, Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hq)]
-- p ∤ orderOf s given orderOf s ∣ m and Coprime p m
example (p m d : ℕ) [Fact p.Prime] (hcop : Nat.Coprime p m) (hdm : d ∣ m) : ¬ p ∣ d := by
  intro hp
  exact (Nat.Prime.coprime_iff_not_dvd (Fact.out)).1 hcop (hp.trans hdm)
end
