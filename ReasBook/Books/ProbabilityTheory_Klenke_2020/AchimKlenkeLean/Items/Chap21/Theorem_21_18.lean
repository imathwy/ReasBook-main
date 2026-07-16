import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap17.Definition_17_12
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap21.Definition_21_8

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Brownian motion under `μ` started from `x`: the process starts at `x` almost surely, has
independent stationary increments, each positive-time marginal is Gaussian with mean `x` and
variance `t`, and its sample paths are almost surely continuous. -/
class IsBrownianMotionStartedAt (μ : Measure Ω) (B : NNReal → Ω → ℝ) (x : ℝ) : Prop where
  /-- The process starts from the state `x` almost surely. -/
  start : μ (B 0 ⁻¹' {x}) = 1
  /-- Brownian motion has independent increments. -/
  indepIncrements : HasIndepIncrements B μ
  /-- Brownian motion has stationary increments. -/
  stationaryIncrements :
    ∀ r s t : NNReal,
      IdentDistrib
        (fun ω ↦ B ((s + t) + r) ω - B (t + r) ω)
        (fun ω ↦ B (s + r) ω - B r ω)
        μ μ
  /-- For every positive time, the time-`t` marginal is Gaussian with mean `x` and variance `t`. -/
  gaussian_marginal : ∀ ⦃t : NNReal⦄, 0 < t → HasLaw (B t) (gaussianReal x t) μ
  /-- Brownian motion has almost surely continuous sample paths. -/
  continuous_paths : HasAlmostSurelyContinuousPaths μ B

namespace IsBrownianMotionStartedAt

/-- A Brownian motion started at `x` is carried by a probability measure. -/
theorem isProbabilityMeasure
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} {x : ℝ}
    (hB : IsBrownianMotionStartedAt μ B x) :
    IsProbabilityMeasure μ := by
  let h₁ : HasLaw (B 1) (gaussianReal x 1) μ := hB.gaussian_marginal (by positivity)
  have hgauss : IsProbabilityMeasure (gaussianReal x 1) := inferInstance
  exact h₁.isProbabilityMeasure_iff.mpr hgauss

end IsBrownianMotionStartedAt

-- Proof sketch: if `B` is standard Brownian motion, then `B 0 = 0` pointwise, so the starting
-- law at time `0` is the Dirac mass at `0`; the remaining Brownian fields are exactly the
-- corresponding fields already stored in `IsBrownianMotion`.
/-- A standard Brownian motion is Brownian motion started from `0`. -/
instance {μ : Measure Ω} {B : NNReal → Ω → ℝ} [IsBrownianMotion μ B] :
    IsBrownianMotionStartedAt μ B 0 := sorry

-- Proof sketch: fix an initial point `x` and apply the dyadic stopping-time approximation from
-- the textbook proof under the law `P x`. On the countable dyadic-time skeleton, use the Chapter
-- 17 strong Markov theorem, then pass to the limit with almost sure continuity of Brownian paths
-- and the continuity of the Brownian transition expectations.
/-- Theorem 21.18: if `B` is Brownian motion under each initial law `P x`, started from `x`, and
`κ` is its path-law kernel, then the family `(P x)` satisfies the strong Markov property for `B`.
-/
theorem brownianMotionFamily_hasStrongMarkovProperty
    (P : ℝ → ProbabilityMeasure Ω) (B : NNReal → Ω → ℝ) (κ : Kernel ℝ (NNReal → ℝ))
    (hκ : ∀ x : ℝ, κ x = (P x : Measure Ω).map (fun ω ↦ fun t : NNReal ↦ B t ω))
    (hB : ∀ x : ℝ, IsBrownianMotionStartedAt (P x : Measure Ω) B x) :
    HasStrongMarkovProperty P B κ := sorry

end ProbabilityTheory
