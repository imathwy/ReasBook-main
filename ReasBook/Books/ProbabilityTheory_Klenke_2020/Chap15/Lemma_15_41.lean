import ProbabilityTheory_Klenke_2020.Chap15.Definition_15_40

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ProbabilityTheory

universe u

noncomputable section

variable {Ω : Type u} [MeasurableSpace Ω]

namespace RealRandomVariableArray

namespace SatisfiesLyapunovCondition

-- Proof sketch: fix `ε > 0` and use the pointwise inequality
-- `x^2 1_{|x| > ε √Var[Sₙ]} ≤ ε^{-δ} Var[Sₙ]^{-δ / 2} |x|^(2 + δ)` termwise inside the row sum.
-- After dividing by `Var[Sₙ]`, the Lindeberg quantity is bounded by `ε^{-δ}` times the
-- Lyapunov quantity of order `2 + δ`, so the assumed convergence to `0` implies the
-- Lindeberg convergence.
/-- Lemma 15.41: every centered square-integrable array satisfying the Lyapunov condition also
satisfies the Lindeberg condition. -/
theorem satisfiesLindebergCondition
    {A : RealRandomVariableArray Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hA : A.SatisfiesLyapunovCondition μ) :
    A.SatisfiesLindebergCondition μ where
  toIsCentered := hA.toIsCentered
  memLp_two := hA.memLp_two
  lindeberg_tendsto := by
    sorry

end SatisfiesLyapunovCondition

end RealRandomVariableArray
