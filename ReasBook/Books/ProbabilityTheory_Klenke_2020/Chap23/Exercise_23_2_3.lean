import Mathlib
import ProbabilityTheory_Klenke_2020.Chap23.Definition_23_6
import ProbabilityTheory_Klenke_2020.Chap23.Definition_23_7

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Topology

noncomputable section

universe u

namespace ProbabilityTheory

/-- The Gaussian-mixture family
`μ_ε = (1 / 2) N(-1, ε) + (1 / 2) N(1, ε)` from the exercise, indexed by `ε > 0`. -/
def twoPointGaussianMixtureMeasureFamily (ε : PositiveParameter) : Measure ℝ :=
  (1 / 2 : ℝ≥0∞) • gaussianReal (-1) (Real.toNNReal ε) +
    (1 / 2 : ℝ≥0∞) • gaussianReal 1 (Real.toNNReal ε)

/-- The rate function `x ↦ (1 / 2) min ((x + 1)^2, (x - 1)^2)` from the exercise, valued in
`ℝ≥0∞`. -/
def twoWellQuadraticRateFunction (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (((1 : ℝ) / 2) * min ((x + 1) ^ (2 : ℕ)) ((x - 1) ^ (2 : ℕ)))

-- Proof sketch: unfold `twoPointGaussianMixtureMeasureFamily`; this is exactly the textbook definition of the
-- Gaussian mixture `μ_ε`.
/-- Expanding `twoPointGaussianMixtureMeasureFamily` gives the explicit symmetric mixture of the two Gaussian
laws centered at `-1` and `1` with variance parameter `ε`. -/
theorem twoPointGaussianMixtureMeasureFamily_def (ε : PositiveParameter) :
    twoPointGaussianMixtureMeasureFamily ε =
      (1 / 2 : ℝ≥0∞) • gaussianReal (-1) (Real.toNNReal ε) +
        (1 / 2 : ℝ≥0∞) • gaussianReal 1 (Real.toNNReal ε) := sorry

/-- Each Gaussian mixture `μ_ε` is a probability measure. -/
theorem twoPointGaussianMixtureMeasureFamily_isProbabilityMeasure (ε : PositiveParameter) :
    IsProbabilityMeasure (twoPointGaussianMixtureMeasureFamily ε) := by
  refine ⟨by
    simp [twoPointGaussianMixtureMeasureFamily, one_div, ENNReal.inv_two_add_inv_two]
  ⟩

-- Proof sketch: unfold `twoWellQuadraticRateFunction`; the statement is exactly the explicit formula
-- displayed in the exercise, rewritten as an `ℝ≥0∞`-valued function.
/-- Expanding `twoWellQuadraticRateFunction` gives the explicit formula
`x ↦ (1 / 2) min ((x + 1)^2, (x - 1)^2)`. -/
theorem twoWellQuadraticRateFunction_def (x : ℝ) :
    twoWellQuadraticRateFunction x =
      ENNReal.ofReal (((1 : ℝ) / 2) * min ((x + 1) ^ (2 : ℕ)) ((x - 1) ^ (2 : ℕ))) := sorry

/-- The two-well quadratic rate function is a good rate function on `ℝ`. -/
instance instIsGoodRateFunctionTwoWellQuadraticRateFunction :
    IsGoodRateFunction twoWellQuadraticRateFunction := sorry

-- Proof sketch: on each side of the origin, the family is a small-variance Gaussian perturbation
-- of one of the two atoms `-1` and `1`, so the local Gaussian LDP gives the quadratic costs
-- `(x + 1)^2 / 2` and `(x - 1)^2 / 2`; exponential asymptotics for the symmetric mixture are then
-- governed by the larger exponential term, which yields the minimum of the two costs.
/-- Exercise 23.2.3: the family
`μ_ε = (1 / 2) N(-1, ε) + (1 / 2) N(1, ε)` satisfies the large deviations principle on `ℝ` as
`ε ↓ 0`, with rate function `x ↦ (1 / 2) min ((x + 1)^2, (x - 1)^2)`. -/
theorem gaussianMixture_smallVariance_satisfiesLDP :
    HasLargeDeviationsPrinciple
      (fun ε ↦
        ⟨twoPointGaussianMixtureMeasureFamily ε,
          twoPointGaussianMixtureMeasureFamily_isProbabilityMeasure ε⟩)
      twoWellQuadraticRateFunction := sorry

end ProbabilityTheory
