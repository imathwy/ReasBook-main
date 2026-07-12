import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_1
import ProbabilityTheory_Klenke_2020.Items.Chap24.Corollary_24_9
import ProbabilityTheory_Klenke_2020.Items.Chap24.Definition_24_3

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- A Poisson point process on `ℝ≥0` with intensity measure `ν` is a random measure with
independent increments whose bounded measurable-set counts have the corresponding Poisson laws. -/
def IsPoissonPointProcessOnNNReal
    (ν : Measure NNReal) (P : ProbabilityMeasure Ω) (X : Ω → Measure NNReal) : Prop :=
  IsRandomMeasure P X ∧
    HasIndependentIncrements P X ∧
    IsLocallyFiniteMeasure ν ∧
    ∀ ⦃A : Set NNReal⦄, MeasurableSet A → Bornology.IsBounded A → ν A ≠ ∞ →
      HasLaw (fun ω ↦ X ω A)
        (Measure.map (fun n : ℕ ↦ (n : ℝ≥0∞)) (poissonMeasure (ν A).toNNReal))
        (P : Measure Ω)

-- Proof sketch: unfold `IsPoissonPointProcessOnNNReal`; the statement is exactly the conjunction
-- of the random-measure property, independent increments, local finiteness of `ν`, and the
-- Poisson law for every bounded measurable-set count.
/-- Unfolding `IsPoissonPointProcessOnNNReal` gives the random-measure, independent-increments,
local-finiteness, and Poisson marginal clauses. -/
theorem isPoissonPointProcessOnNNReal_iff
    (ν : Measure NNReal) (P : ProbabilityMeasure Ω) (X : Ω → Measure NNReal) :
    IsPoissonPointProcessOnNNReal ν P X ↔
      IsRandomMeasure P X ∧
        HasIndependentIncrements P X ∧
        IsLocallyFiniteMeasure ν ∧
        ∀ ⦃A : Set NNReal⦄, MeasurableSet A → Bornology.IsBounded A → ν A ≠ ∞ →
          HasLaw (fun ω ↦ X ω A)
            (Measure.map (fun n : ℕ ↦ (n : ℝ≥0∞)) (poissonMeasure (ν A).toNNReal))
            (P : Measure Ω) := sorry

/-- The Poisson stochastic integral `∫ x X(dx)` of a random measure on `ℝ≥0` with respect to the
identity integrand. -/
def poissonPointIntegral (X : Ω → Measure NNReal) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ x, (x : ℝ≥0∞) ∂X ω

-- Proof sketch: unfold `poissonPointIntegral`; it is exactly the `lintegral` of the identity
-- function against the random measure `X ω`.
/-- Unfolding `poissonPointIntegral` gives the textbook random sum `∫ x X(dx)` as a nonnegative
Lebesgue integral. -/
theorem poissonPointIntegral_def (X : Ω → Measure NNReal) (ω : Ω) :
    poissonPointIntegral X ω = ∫⁻ x, (x : ℝ≥0∞) ∂X ω := sorry

-- Proof sketch: decompose the integral into the large-jump and small-jump parts as in the
-- textbook proof, use the Poisson law on `[1, ∞)` for the large jumps, and control the small-jump
-- piece by its first moment and variance. This yields the implications `(iii) → (ii)`, `(ii) →
-- (i)`, and `(i) → (iii)`, which are then packaged as a TFAE.
/-- Theorem 24.17: for a Poisson point process `X ∼ PPP_ν` on `ℝ≥0`, the following are
equivalent: (i) the Poisson stochastic integral `∫ x X(dx)` is finite with positive probability;
(ii) it is finite almost surely; and (iii) the Lévy integrability condition
`∫ min (1, x) dν < ∞` holds. -/
theorem poissonPointIntegral_finite_tfae
    {P : ProbabilityMeasure Ω} {ν : Measure NNReal} {X : Ω → Measure NNReal}
    (hX : IsPoissonPointProcessOnNNReal ν P X) :
    List.TFAE
      [ 0 < (P : Measure Ω) {ω | poissonPointIntegral X ω < ∞}
      , (P : Measure Ω) {ω | poissonPointIntegral X ω < ∞} = 1
      , Integrable (fun x : NNReal ↦ min (1 : ℝ) (x : ℝ)) ν
      ] := sorry

-- Proof sketch: apply the Poisson random-measure Laplace formula with the identity test function
-- `x ↦ t x` to compute the Laplace transform of `∫ x X(dx)` and identify the exponent with the
-- standard Poisson/Lévy integral `∫ (e^{-tx} - 1) ν(dx)`.
/-- The Laplace transform of the Poisson stochastic integral is given by the canonical exponential
formula determined by the intensity measure `ν`. -/
theorem poissonPointIntegral_laplaceFormula
    {P : ProbabilityMeasure Ω} {ν : Measure NNReal} {X : Ω → Measure NNReal}
    (hX : IsPoissonPointProcessOnNNReal ν P X) :
    ∀ t : NNReal,
      ∫ ω,
          Real.exp (-((t : ℝ) * (poissonPointIntegral X ω).toReal))
        ∂(P : Measure Ω) =
        Real.exp (∫ x : NNReal, (Real.exp (-((t : ℝ) * (x : ℝ))) - 1) ∂ν) := sorry

-- Proof sketch: use the Laplace-transform identity from `poissonPointIntegral_laplaceFormula` to
-- identify the law of the almost surely finite integral with a nonnegative infinitely divisible
-- law, and realize infinite divisibility at the random-variable level through the definition from
-- Chapter 16.
/-- If the Poisson stochastic integral is almost surely finite, then its real-valued version is an
infinitely divisible nonnegative random variable. -/
theorem poissonPointIntegral_toReal_isInfinitelyDivisible
    {P : ProbabilityMeasure Ω} {ν : Measure NNReal} {X : Ω → Measure NNReal}
    (hX : IsPoissonPointProcessOnNNReal ν P X)
    (hfinite : (P : Measure Ω) {ω | poissonPointIntegral X ω < ∞} = 1) :
    IsInfinitelyDivisibleRandomVariable
      (P : Measure Ω) (fun ω ↦ (poissonPointIntegral X ω).toReal) := sorry

end ProbabilityTheory
