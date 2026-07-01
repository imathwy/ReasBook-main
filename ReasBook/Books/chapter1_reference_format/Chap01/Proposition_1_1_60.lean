import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Function

/-
The canonical owner theorem for the nontrivial direction is `Fintype.prod_dvd_of_coprime`.
-/
recall Fintype.prod_dvd_of_coprime {R : Type u} {I : Type v} [CommSemiring R] {z : R} {s : I → R}
    [Fintype I] (Hs : Pairwise (IsCoprime on s)) (Hs1 : ∀ i : I, s i ∣ z) : ∏ x, s x ∣ z

namespace Int

/-- Proposition 1.1.60: for pairwise coprime integers `a₁, …, aₙ`, the product `∏ i, a i` divides
an integer `b` if and only if each factor `a i` divides `b`. -/
-- Proof sketch: the forward implication is immediate from divisibility of a factor into the full
-- product. For the reverse implication, apply the canonical owner theorem
-- `Fintype.prod_dvd_of_coprime` to the pairwise coprime family `a`.
theorem pairwise_isCoprime_prod_dvd_iff {ι : Type*} [Fintype ι] {a : ι → ℤ} {b : ℤ}
    (h_pairwise : Pairwise (IsCoprime on a)) :
    (∏ i, a i) ∣ b ↔ ∀ i, a i ∣ b := by
  constructor
  · intro h_prod i
    -- Each factor divides the full product, so divisibility by the product descends to that factor.
    exact dvd_trans (Finset.dvd_prod_of_mem a (Finset.mem_univ i)) h_prod
  -- The reverse implication is exactly the canonical finite pairwise-coprime product theorem.
  · exact Fintype.prod_dvd_of_coprime h_pairwise

end Int
