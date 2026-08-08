import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

variable {E : Type u} {V : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable (A : E →ₗ[ℝ] V)

/- Definition 1.45 is recall-only: for a linear transformation on a finite-dimensional real normed
space, the textbook norm is the canonical operator norm of the associated continuous linear map
`A.toContinuousLinearMap`. -/
#check (‖A.toContinuousLinearMap‖ : ℝ)

-- Proof sketch: apply `ContinuousLinearMap.unit_le_opNorm` to the continuous linear map
-- `A.toContinuousLinearMap`; this canonical operator norm is exactly the textbook norm of `A`.
/-- Every vector in the closed unit ball is sent to a vector whose norm is bounded by the norm of
the linear transformation. -/
theorem norm_image_le_opNorm_toContinuousLinearMap (A : E →ₗ[ℝ] V) {x : E} (hx : ‖x‖ ≤ 1) :
    ‖A x‖ ≤ ‖A.toContinuousLinearMap‖ := by
  simpa using A.toContinuousLinearMap.unit_le_opNorm x hx

-- Proof sketch: the closed unit ball in the finite-dimensional normed space `E` is compact, and
-- the map `x ↦ ‖A x‖` is continuous. Therefore it attains a maximum on that ball, and the
-- preceding bound identifies that maximum with `‖A.toContinuousLinearMap‖`.
/-- A vector in the closed unit ball realizes the norm of the linear transformation, recovering
the textbook maximum formula. -/
theorem exists_norm_le_one_eq_opNorm_toContinuousLinearMap (A : E →ₗ[ℝ] V) :
    ∃ x : E, ‖x‖ ≤ 1 ∧ ‖A.toContinuousLinearMap‖ = ‖A x‖ := sorry

end
