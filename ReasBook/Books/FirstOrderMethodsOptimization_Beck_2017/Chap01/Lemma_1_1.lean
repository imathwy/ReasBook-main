import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The dual norm of a linear functional, realized as the operator norm of the associated
continuous linear functional. -/
def dualNorm (y : Module.Dual ℝ E) : ℝ :=
  ‖LinearMap.toContinuousLinearMap y‖

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: apply `ContinuousLinearMap.le_opNorm` to the continuous linear functional
-- `LinearMap.toContinuousLinearMap y`; the abbreviation `dualNorm y` is exactly this operator norm,
-- and because the codomain is `ℝ`, the norm of `y x` is `|y x|`.
/-- Lemma 1.1: for a linear functional `y ∈ E* = Module.Dual ℝ E` on a finite-dimensional real
normed space, the canonical dual pairing is bounded by the dual norm times the norm of the
vector. This is the chapter-facing dual-pairing inequality `|y x| ≤ ‖y‖_* ‖x‖` written using
`dualNorm`. -/
theorem abs_apply_le_dual_norm_mul_norm (y : Module.Dual ℝ E) (x : E) :
    |y x| ≤ dualNorm y * ‖x‖ := sorry

end
