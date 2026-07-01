import Mathlib
import AchimKlenkeLean.Items.Chap21.Definition_21_8

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

namespace IsBrownianMotion

-- Proof sketch: first prove the unit-time identity by stopping at the first hitting time of the
-- level `a` and reflecting the post-stopping Brownian increment, which gives
-- `μ {ω | ∃ t ∈ [0,1], a < B t ω} = 2 * μ {ω | a < B 1 ω}`. Then apply the Brownian scaling
-- property to pass from time `1` to general `T`, and estimate the Gaussian upper tail
-- `μ {ω | a < B T ω}` by the standard integral bound.
/-- Theorem 21.19: reflection principle for Brownian motion. For every `a > 0` and `T > 0`, the
probability that a Brownian path exceeds level `a` somewhere on `[0,T]` is twice the one-time tail
probability at time `T`, and this common quantity satisfies the stated Gaussian tail bound. -/
theorem reflection_principle_runningMaximum
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {a : ℝ} (ha : 0 < a) {T : NNReal} (hT : 0 < T) :
    μ {ω | ∃ t ∈ Set.Icc (0 : NNReal) T, a < B t ω} = 2 * μ {ω | a < B T ω} ∧
      μ {ω | ∃ t ∈ Set.Icc (0 : NNReal) T, a < B t ω} ≤
        ENNReal.ofReal
          ((2 * Real.sqrt (T : ℝ) / Real.sqrt (2 * Real.pi)) * (1 / a) *
            Real.exp (-(a ^ 2) / (2 * (T : ℝ)))) := sorry

end IsBrownianMotion

end ProbabilityTheory
