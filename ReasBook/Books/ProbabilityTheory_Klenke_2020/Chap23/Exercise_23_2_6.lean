import Mathlib
import ProbabilityTheory_Klenke_2020.Chap23.Definition_23_6
import ProbabilityTheory_Klenke_2020.Chap23.Definition_23_7

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

noncomputable section

namespace ProbabilityTheory

private def poissonScaling (ε : PositiveParameter) : ℕ → ℝ :=
  fun n ↦ ε * (n : ℝ)

private theorem poissonScaling_measurable (ε : PositiveParameter) :
    Measurable (poissonScaling ε) :=
  measurable_of_countable (poissonScaling ε)

/-- The family `μ_ε` obtained by pushing forward the Poisson law with parameter `λ / ε` under the
scaling map `n ↦ ε n`. -/
def poissonScaledLaw (lam : ℝ) : PositiveProbabilityFamily ℝ :=
  fun ε ↦
    ProbabilityMeasure.map
      (⟨poissonMeasure (Real.toNNReal (lam / (ε : ℝ))), inferInstance⟩ : ProbabilityMeasure ℕ)
      (poissonScaling_measurable ε).aemeasurable

/-- The Poisson Cramér rate function `x log (x / λ) + λ - x` on `[0, ∞)` and `∞` on `(-∞, 0)`. -/
def poissonScaledRateFunction (lam : ℝ) (x : ℝ) : ENNReal :=
  if 0 ≤ x then ENNReal.ofReal (x * Real.log (x / lam) + lam - x) else ⊤

-- Proof sketch: unfold `poissonScaledRateFunction`; under the hypothesis `0 ≤ x`, the defining
-- `if` takes its finite branch.
/-- On `[0, ∞)`, `poissonScaledRateFunction` is given by the explicit Poisson entropy formula. -/
theorem poissonScaledRateFunction_of_nonneg (lam : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    poissonScaledRateFunction lam x = ENNReal.ofReal (x * Real.log (x / lam) + lam - x) := sorry

-- Proof sketch: verify lower semicontinuity of the explicit formula on `[0, ∞)`, show that every
-- finite sublevel set is closed and bounded, and conclude compactness by Heine-Borel.
/-- The explicit Poisson Cramér rate function is a good rate function for every positive
parameter `λ`. -/
theorem poissonScaledRateFunction_isGoodRateFunction {lam : ℝ} (hlam : 0 < lam) :
    IsGoodRateFunction (poissonScaledRateFunction lam) := sorry

-- Proof sketch: compute the logarithmic moment generating function of `ε X_(λ / ε)` from the
-- Poisson law, identify its Legendre transform as `poissonScaledRateFunction lam`, and then apply
-- the chapter's large-deviation theorem for exponentially tilted logarithmic moment generating
-- functions.
/-- Exercise 23.2.6: for `λ > 0`, the laws `μ_ε = P_(ε X_(λ / ε))` satisfy the large deviations
principle on `ℝ` with rate function `x log (x / λ) + λ - x` for `x ≥ 0` and `∞` for `x < 0`. -/
theorem poissonScaledLaw_satisfiesLDPWithRate {lam : ℝ} (hlam : 0 < lam) :
    HasLargeDeviationsPrinciple
      (poissonScaledLaw lam)
      (poissonScaledRateFunction lam) := sorry

end ProbabilityTheory
