import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_18_18 (from Chap18) -/
open scoped InnerProductSpace

universe u

namespace ContinuousLinearMap

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: set `f y = ⟪L y, y⟫_ℝ / 2`. Example 2.57 and self-adjointness identify
-- `∇ f = L`, while monotonicity gives convexity of `f`. Apply implication `(i) -> (v)` from
-- Theorem 18.15 with `β = ‖L‖`, then specialize the resulting cocoercivity inequality at `y = 0`.
/-- Corollary 18.18: if a bounded operator `L : H →L[ℝ] H` is self-adjoint and monotone, then
`‖L‖ * ⟪L x, x⟫_ℝ ≥ ‖L x‖^2` for every `x`. -/
theorem norm_mul_inner_apply_ge_sq_norm_of_isSelfAdjoint_of_isMonotone
    (L : H →L[ℝ] H) (hL_self : IsSelfAdjoint L) (hL_mono : L.toLinearMap.IsMonotone) (x : H) :
    ‖L‖ * ⟪L x, x⟫_ℝ ≥ ‖L x‖ ^ (2 : ℕ) := sorry

end ContinuousLinearMap
