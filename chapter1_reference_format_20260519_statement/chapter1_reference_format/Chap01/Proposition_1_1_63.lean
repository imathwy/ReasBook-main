import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Function

namespace Int

-- Proof sketch: apply the canonical owner theorem `Finset.associated_lcm_prod`, using
-- `IsCoprime.isRelPrime` to move from Bezout coprimality to relative primality, and then rewrite
-- the normalized product in `ℤ` as its absolute value via `Int.abs_eq_normalize`.
/-- Proposition 1.1.63: for pairwise coprime integers `a₁, …, aₙ`, the least common multiple of
the family is the absolute value of the product `a₁ ⋯ aₙ`. -/
  theorem pairwise_isCoprime_univ_lcm_eq_abs_prod
    {ι : Type*} [Fintype ι] {a : ι → ℤ}
    (h_pairwise : Pairwise (IsCoprime on a)) :
    Finset.univ.lcm a = |∏ i, a i| := by
  have h_assoc : Associated (Finset.univ.lcm a) (∏ i, a i) :=
    Finset.associated_lcm_prod <| by
      simpa [Set.pairwise_univ, Function.onFun] using
        fun i j hij ↦ (h_pairwise hij).isRelPrime
  have h_norm : normalize (Finset.univ.lcm a) = normalize (∏ i, a i) :=
    normalize_eq_normalize_iff_associated.mpr h_assoc
  calc
    Finset.univ.lcm a = normalize (Finset.univ.lcm a) := (Finset.normalize_lcm).symm
    _ = normalize (∏ i, a i) := h_norm
    _ = |∏ i, a i| := (Int.abs_eq_normalize _).symm

end Int
