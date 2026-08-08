import Mathlib
import ProbabilityTheory_Klenke_2020.Chap23.Example_23_10

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: rewrite the law of `X` as the canonical Gaussian law via `hX` and apply
-- `cgf_gaussianReal`; for the standard normal parameters `μ = 0`, `v = 1`, the resulting
-- quadratic simplifies to `t^2 / 2`.
/-- The cumulant-generating function of a standard normal random variable is `t ↦ t^2 / 2`. -/
theorem cgf_eq_half_sq_of_hasLaw_standardNormal
    {P : Measure Ω} {X : Ω → ℝ} (hX : HasLaw X (gaussianReal 0 1) P) (t : ℝ) :
    cgf X P t = t ^ 2 / 2 := by
  simpa using cgf_gaussianReal hX.map_eq t

-- Proof sketch: use `cgf_eq_half_sq_of_hasLaw_standardNormal` to rewrite the variational
-- expression as `sup_t (t z - t^2 / 2)`, then complete the square:
-- `t z - t^2 / 2 = z^2 / 2 - (t - z)^2 / 2`, whose supremum is attained at `t = z`.
/-- Example 23.4: if `X` has the standard normal law, then the Legendre transform of its
cumulant-generating function is `z ↦ z^2 / 2`. -/
theorem legendreCgfRateFunction_eq_half_sq_of_hasLaw_standardNormal
    {P : Measure Ω} {X : Ω → ℝ} (hX : HasLaw X (gaussianReal 0 1) P) (z : ℝ) :
    legendreCgfRateFunction X P z = z ^ 2 / 2 := sorry

end ProbabilityTheory
