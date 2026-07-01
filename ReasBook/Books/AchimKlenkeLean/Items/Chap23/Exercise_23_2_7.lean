import Mathlib
import AchimKlenkeLean.Items.Chap05.Definition_5_33
import AchimKlenkeLean.Items.Chap23.Definition_23_6
import AchimKlenkeLean.Items.Chap23.Definition_23_7

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set
open scoped ENNReal

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

private def rescaledWalkTime (ε : PositiveParameter) : NNReal :=
  Real.toNNReal ε⁻¹

/-- The rescaled position map `ω ↦ ε X_{1 / ε}(ω)` of the continuous-time symmetric walk. -/
def continuousTimeSymmetricRandomWalkRescaled
    (X : NNReal → Ω → ℤ) (ε : PositiveParameter) : Ω → ℝ :=
  fun ω ↦ ε * (X (rescaledWalkTime ε) ω : ℝ)

/-- The increment law at time `t` of the continuous-time symmetric random walk on `ℤ`, realized as
the difference of two independent Poisson variables with common parameter `t / 2`. -/
def continuousTimeSymmetricRandomWalkIncrementLaw (t : NNReal) : ProbabilityMeasure ℤ :=
  ⟨((poissonPMF (t / 2)).bind fun n ↦
      (poissonPMF (t / 2)).map fun m ↦ (n : ℤ) - m).toMeasure,
    inferInstance⟩

/-- A process on `ℤ` is the continuous-time symmetric random walk when it starts at `0`, has
independent increments, and each increment over `(s,t]` has the canonical symmetric
difference-of-Poisson law with jump rates `1 / 2` to the right and left. -/
class IsContinuousTimeSymmetricRandomWalk
    (μ : Measure Ω) (X : NNReal → Ω → ℤ) : Prop where
  /-- The walk is a stochastic process. -/
  stochastic : IsStochasticProcess X
  /-- The walk starts from the origin. -/
  zero : X 0 = 0
  /-- The walk has independent increments. -/
  indepIncrements : HasIndepIncrements X μ
  /-- The increment over `(s,t]` has the canonical symmetric continuous-time random-walk law. -/
  increment_law :
    ∀ ⦃s t : NNReal⦄, s ≤ t →
      HasLaw
        (fun ω ↦ X t ω - X s ω)
        (continuousTimeSymmetricRandomWalkIncrementLaw (t - s))
        μ

namespace IsContinuousTimeSymmetricRandomWalk

/-- Every time slice of a continuous-time symmetric random walk is measurable. -/
theorem measurable
    {μ : Measure Ω} {X : NNReal → Ω → ℤ}
    (hX : IsContinuousTimeSymmetricRandomWalk μ X) (t : NNReal) :
    Measurable (X t) :=
  hX.stochastic t

/-- The increment law forces the underlying measure of a continuous-time symmetric random walk to
be a probability measure. -/
theorem isProbabilityMeasure
    {μ : Measure Ω} {X : NNReal → Ω → ℤ}
    (hX : IsContinuousTimeSymmetricRandomWalk μ X) :
    IsProbabilityMeasure μ := by
  exact (hX.increment_law (show (0 : NNReal) ≤ 1 by norm_num)).isProbabilityMeasure

end IsContinuousTimeSymmetricRandomWalk

/-- The rescaled position map `ω ↦ ε X_{1 / ε}(ω)` is measurable when the coordinate maps of `X`
are measurable. -/
theorem measurable_continuousTimeSymmetricRandomWalkRescaled
    (X : NNReal → Ω → ℤ) (hXmeas : ∀ t, Measurable (X t)) (ε : PositiveParameter) :
    Measurable (continuousTimeSymmetricRandomWalkRescaled X ε) := by
  have hcast : Measurable (fun z : ℤ ↦ (z : ℝ)) :=
    measurable_of_countable (fun z : ℤ ↦ (z : ℝ))
  simpa [continuousTimeSymmetricRandomWalkRescaled] using
    measurable_const.mul (hcast.comp <| hXmeas (rescaledWalkTime ε))

/-- The law family `ε ↦ P_{ε X_{1/ε}}` of the rescaled continuous-time walk on the positive
parameter space `ε > 0`, built from the source-facing owner
`IsContinuousTimeSymmetricRandomWalk μ X`. -/
def continuousTimeSymmetricRandomWalkRescaledLaw
    (μ : Measure Ω) (X : NNReal → Ω → ℤ)
    (hX : IsContinuousTimeSymmetricRandomWalk μ X) :
    PositiveProbabilityFamily ℝ :=
  letI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  fun ε ↦
    ProbabilityMeasure.map ⟨μ, inferInstance⟩
      (measurable_continuousTimeSymmetricRandomWalkRescaled X hX.measurable ε).aemeasurable

/-- The candidate good rate function
`x ↦ 1 + x arsinh(x) - sqrt (1 + x^2)`, viewed as an `ℝ≥0∞`-valued map. -/
def continuousTimeSymmetricRandomWalkRateFunction (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 + x * Real.arsinh x - Real.sqrt (1 + x ^ (2 : ℕ)))

-- Proof sketch: unfold `continuousTimeSymmetricRandomWalkRescaledLaw`; it is the pushforward of
-- `P` by the map `ω ↦ ε * X_(1 / ε)(ω)` with the chapter's `NNReal` time parameter
-- `rescaledWalkTime ε`.
/-- Expanding `continuousTimeSymmetricRandomWalkRescaledLaw` gives the pushforward law of the
rescaled position `ε X_{1/ε}`. -/
theorem continuousTimeSymmetricRandomWalkRescaledLaw_def
    (μ : Measure Ω) (X : NNReal → Ω → ℤ)
    (hX : IsContinuousTimeSymmetricRandomWalk μ X) (ε : PositiveParameter) :
    continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε =
      ProbabilityMeasure.map ⟨μ, hX.isProbabilityMeasure⟩
        (measurable_continuousTimeSymmetricRandomWalkRescaled X hX.measurable ε).aemeasurable := by
  letI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  rfl

-- Proof sketch: unfold `continuousTimeSymmetricRandomWalkRateFunction`; this is exactly the
-- explicit formula displayed in the exercise, rewritten as an `ℝ≥0∞`-valued map.
/-- Expanding `continuousTimeSymmetricRandomWalkRateFunction` gives the explicit textbook formula
`x ↦ 1 + x arsinh(x) - sqrt (1 + x^2)`. -/
theorem continuousTimeSymmetricRandomWalkRateFunction_def (x : ℝ) :
    continuousTimeSymmetricRandomWalkRateFunction x =
      ENNReal.ofReal (1 + x * Real.arsinh x - Real.sqrt (1 + x ^ (2 : ℕ))) := rfl

-- Proof sketch: the real-valued branch is continuous and coercive, so the `ℝ≥0∞`-valued rate
-- function is lower semicontinuous and its finite sublevel sets are compact in `ℝ`.
/-- The explicit rate function of the rescaled continuous-time symmetric walk is a good rate
function on `ℝ`. -/
instance continuousTimeSymmetricRandomWalkRateFunction_isGoodRateFunction :
    IsGoodRateFunction continuousTimeSymmetricRandomWalkRateFunction := sorry

-- Proof sketch: compute the second derivative of the real-valued branch
-- `x ↦ 1 + x arsinh(x) - sqrt (1 + x^2)` as `(1 + x^2)^(-1/2)`, which is nonnegative on `ℝ`,
-- and conclude convexity on the whole line.
/-- The finite real-valued branch of the rate function is convex on `ℝ`. -/
theorem continuousTimeSymmetricRandomWalkRateFunction_convex :
    ConvexOn ℝ univ
      (fun x : ℝ ↦ 1 + x * Real.arsinh x - Real.sqrt (1 + x ^ (2 : ℕ))) := sorry

/-- A Poisson right/left decomposition is a bridge to the intrinsic owner
`IsContinuousTimeSymmetricRandomWalk`. -/
theorem isContinuousTimeSymmetricRandomWalk_of_eq_poissonDifference
    (μ : Measure Ω) (X : NNReal → Ω → ℤ)
    {Nright Nleft : NNReal → Ω → ℕ}
    (hNright : IsPoissonProcess (1 / 2 : NNReal) μ Nright)
    (hNleft : IsPoissonProcess (1 / 2 : NNReal) μ Nleft)
    (hindep : IndepFun (fun ω t ↦ Nright t ω) (fun ω t ↦ Nleft t ω) μ)
    (hX : X = fun t ω ↦ (Nright t ω : ℤ) - Nleft t ω) :
    IsContinuousTimeSymmetricRandomWalk μ X := sorry

-- Proof sketch: compute the logarithmic moment generating function of the canonical increment law,
-- identify its Legendre transform as the explicit rate function below, and apply the chapter's
-- large-deviation theorem to the rescaled one-time marginals of the continuous-time symmetric
-- random walk.
/-- Exercise 23.2.7: for a continuous-time symmetric random walk on `ℤ` with jump rates `1 / 2`
to the right and left, the family of laws `P_{ε X_{1/ε}}` satisfies the large deviations
principle as `ε ↓ 0`, with rate function
`I(x) = 1 + x arsinh(x) - sqrt (1 + x^2)`. -/
theorem continuousTimeSymmetricRandomWalk_rescaled_satisfiesLDP
    (μ : Measure Ω)
    (X : NNReal → Ω → ℤ)
    (hX : IsContinuousTimeSymmetricRandomWalk μ X) :
    HasLargeDeviationsPrinciple
      (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX)
      continuousTimeSymmetricRandomWalkRateFunction := sorry

/-- Bridge form of Exercise 23.2.7: a Poisson right/left decomposition yields the intrinsic
continuous-time symmetric random-walk hypothesis, so the LDP follows from the source-facing owner
theorem. -/
theorem continuousTimeSymmetricRandomWalk_rescaled_satisfiesLDP_of_eq_poissonDifference
    (μ : Measure Ω)
    (X : NNReal → Ω → ℤ)
    {Nright Nleft : NNReal → Ω → ℕ}
    (hNright : IsPoissonProcess (1 / 2 : NNReal) μ Nright)
    (hNleft : IsPoissonProcess (1 / 2 : NNReal) μ Nleft)
    (hindep : IndepFun (fun ω t ↦ Nright t ω) (fun ω t ↦ Nleft t ω) μ)
    (hX : X = fun t ω ↦ (Nright t ω : ℤ) - Nleft t ω) :
    HasLargeDeviationsPrinciple
      (continuousTimeSymmetricRandomWalkRescaledLaw μ X
        (isContinuousTimeSymmetricRandomWalk_of_eq_poissonDifference
          μ X hNright hNleft hindep hX))
      continuousTimeSymmetricRandomWalkRateFunction := by
  exact continuousTimeSymmetricRandomWalk_rescaled_satisfiesLDP
    μ X
    (isContinuousTimeSymmetricRandomWalk_of_eq_poissonDifference
      μ X hNright hNleft hindep hX)

end ProbabilityTheory
