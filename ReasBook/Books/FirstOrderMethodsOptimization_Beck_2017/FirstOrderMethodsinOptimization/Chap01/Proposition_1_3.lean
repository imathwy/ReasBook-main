import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

namespace Matrix

section

variable {m n : ℕ}

-- Proof sketch: use the owner map `Matrix.toLpLin 1 1 A`, which is the canonical linear map
-- between `WithLp 1` coordinate spaces associated to `A`. The upper bound follows by expanding
-- `A *ᵥ x` coordinatewise and using the triangle inequality in the `ℓ¹` norm; for the reverse
-- inequality, test the operator on a standard basis vector for a column attaining the finite
-- supremum.
/-- Proposition 1.3: the operator norm of the canonical `ℓ¹ → ℓ¹` linear map induced by a real
matrix is the maximum absolute column sum norm. -/
theorem induced_l1_norm_eq_max_column_sum (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖LinearMap.toContinuousLinearMap (A.toLpLin 1 1)‖ =
      ((Finset.univ : Finset (Fin n)).sup fun j : Fin n ↦
        ∑ i : Fin m, ‖A i j‖₊) := sorry

end

end Matrix
