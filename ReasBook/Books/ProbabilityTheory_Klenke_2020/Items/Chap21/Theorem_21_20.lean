import Mathlib
import AchimKlenkeLean.Items.Chap21.Definition_21_8

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The last zero time of a real-valued path on `[0, ∞)` before the horizon `T`. -/
def pathLastZeroBefore (f : NNReal → ℝ) (T : NNReal) : NNReal :=
  sSup {t : NNReal | t ≤ T ∧ f t = 0}

-- Proof sketch: unfold `pathLastZeroBefore`; it is defined as the supremum of the set of times up
-- to `T` at which the path vanishes.
/-- Expanding `pathLastZeroBefore` gives the supremum of the zero times up to `T`. -/
theorem pathLastZeroBefore_eq_sSup (f : NNReal → ℝ) (T : NNReal) :
    pathLastZeroBefore f T = sSup {t : NNReal | t ≤ T ∧ f t = 0} := by
  rfl

/-- The last zero time of the sample path `t ↦ B t ω` before the horizon `T`. -/
def lastZeroBefore (B : NNReal → Ω → ℝ) (T : NNReal) : Ω → NNReal :=
  fun ω ↦ pathLastZeroBefore (fun t ↦ B t ω) T

-- Proof sketch: unfold `lastZeroBefore`; it evaluates `pathLastZeroBefore` on the sample path
-- `t ↦ B t ω`.
omit [MeasurableSpace Ω] in
/-- Evaluating `lastZeroBefore B T` at `ω` gives the last zero time of the sample path
`t ↦ B t ω`. -/
theorem lastZeroBefore_apply (B : NNReal → Ω → ℝ) (T : NNReal) (ω : Ω) :
    lastZeroBefore B T ω = pathLastZeroBefore (fun t ↦ B t ω) T := by
  rfl

-- Proof sketch: combine `lastZeroBefore_apply` with `pathLastZeroBefore_eq_sSup`.
omit [MeasurableSpace Ω] in
/-- Expanding `lastZeroBefore` gives the supremum of the zero times up to `T`. -/
theorem lastZeroBefore_eq_sSup (B : NNReal → Ω → ℝ) (T : NNReal) (ω : Ω) :
    lastZeroBefore B T ω = sSup {t : NNReal | t ≤ T ∧ B t ω = 0} := by
  rw [lastZeroBefore_apply, pathLastZeroBefore_eq_sSup]

namespace IsBrownianMotion

-- Proof sketch: reduce by Brownian scaling to the case `T = 1`, condition on the value `B_t`,
-- rewrite the event of having no further zero after time `t` using the reflection principle, and
-- then compute the resulting Gaussian integral in polar coordinates.
/-- Theorem 21.20: Lévy's arcsine law identifies the distribution function of the last zero of a
Brownian path before time `T`. -/
theorem lastZeroBefore_cdf_eq_arcsineLaw
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {T t : NNReal} (hT : 0 < T) (ht : t ≤ T) :
    cdf (μ.map fun ω ↦ (lastZeroBefore B T ω : ℝ)) t =
      (2 / Real.pi) * Real.arcsin (Real.sqrt ((t : ℝ) / (T : ℝ))) := sorry

-- Proof sketch: derive the probability-measure instance on `μ` from the positive-time Gaussian
-- marginal of Brownian motion, then rewrite the cdf in
-- `lastZeroBefore_cdf_eq_arcsineLaw` using `cdf_eq_real_preimage_Iic`.
/-- The cdf formula for `lastZeroBefore B T` rewritten in the textbook preimage-`Iic` form. -/
theorem lastZeroBefore_real_preimage_Iic_eq_arcsineLaw
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {T t : NNReal} (hT : 0 < T) (ht : t ≤ T) :
    μ.real ((fun ω ↦ (lastZeroBefore B T ω : ℝ)) ⁻¹' Set.Iic t) =
      (2 / Real.pi) * Real.arcsin (Real.sqrt ((t : ℝ) / (T : ℝ))) := sorry

end IsBrownianMotion

end ProbabilityTheory
