import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {p : ℕ}

/- Theorem 1.1.90: for every prime `p`, the multiplicative group `(ℤ/pℤ)∗`, formalized as
`(ZMod p)ˣ`, is cyclic of order `p - 1`; the cyclicity statement is the canonical theorem
`ZMod.isCyclic_units_prime`. -/
recall ZMod.isCyclic_units_prime (hp : Nat.Prime p) : IsCyclic (ZMod p)ˣ

/-- A cyclic unit group modulo a prime contains a generator of order `p - 1`. -/
theorem exists_unit_of_order_prime_sub_one (hp : Nat.Prime p) :
    ∃ g : (ZMod p)ˣ, orderOf g = p - 1 := by
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    rw [← Fintype.card_eq_nat_card, ZMod.card_units]
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp (ZMod.isCyclic_units_prime hp)
  exact ⟨g, hg.trans hcard⟩

end
