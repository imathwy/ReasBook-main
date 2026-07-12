import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap09.Definition_9_7
import ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_4

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Definition 21.8: a real-valued process on `[0,∞)` is a Brownian motion under `μ` if it starts
from `0`, has independent stationary increments, each positive-time marginal is the centered
Gaussian law with variance `t`, and its sample paths are almost surely continuous. -/
class IsBrownianMotion (μ : Measure Ω) (B : NNReal → Ω → ℝ) : Prop where
  /-- A Brownian motion starts at the constant value `0`. -/
  zero : B 0 = 0
  /-- Brownian motion has independent increments. -/
  indepIncrements : HasIndepIncrements B μ
  /-- Brownian motion has stationary increments. -/
  stationaryIncrements : HasStationaryIncrements B μ
  /-- For every positive time, the marginal law is centered Gaussian with variance `t`. -/
  gaussian_marginal : ∀ ⦃t : NNReal⦄, 0 < t → HasLaw (B t) (gaussianReal 0 t) μ
  /-- Brownian motion has almost surely continuous sample paths. -/
  continuous_paths : HasAlmostSurelyContinuousPaths μ B

namespace IsBrownianMotion

/-- Every time marginal of a Brownian motion is strongly measurable. -/
theorem stronglyMeasurable
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) (t : NNReal) :
    StronglyMeasurable (B t) := sorry

/-- A Brownian motion is carried by a probability measure. -/
theorem isProbabilityMeasure
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) :
    IsProbabilityMeasure μ := by
  let h₁ : HasLaw (B 1) (gaussianReal 0 1) μ := hB.gaussian_marginal (by positivity)
  have hgauss : IsProbabilityMeasure (gaussianReal 0 1) := inferInstance
  exact h₁.isProbabilityMeasure_iff.mpr hgauss

end IsBrownianMotion

end ProbabilityTheory
