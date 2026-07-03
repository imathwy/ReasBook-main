import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_16_14 (from Items/Chap16) -/
open MeasureTheory
open scoped MeasureTheory

noncomputable section

universe u

namespace MeasureTheory.ProbabilityMeasure

-- Proof sketch: for the Dirac mass at `x`, take the `n`th root `δ_{x / n}` and use the additive
-- convolution law for Dirac measures on `NNReal`.
/-- Every Dirac probability measure on `[0, ∞)` is infinitely divisible. -/
instance diracProba_isInfinitelyDivisibleOnNNReal (x : NNReal) :
    IsInfinitelyDivisible (diracProba x : ProbabilityMeasure NNReal) := sorry

/-- The log-Laplace transform of a probability measure on `[0, ∞)`. -/
def logLaplaceTransform (μ : ProbabilityMeasure NNReal) (t : NNReal) : ℝ :=
  -Real.log (∫ x, Real.exp (-((t : ℝ) * (x : ℝ))) ∂(μ : Measure NNReal))

-- Proof sketch: this is the definition of `logLaplaceTransform`, obtained by unfolding the
-- integral formula against the probability measure `μ`.
/-- The log-Laplace transform is `-log` of the ordinary Laplace transform. -/
theorem logLaplaceTransform_def (μ : ProbabilityMeasure NNReal) (t : NNReal) :
    μ.logLaplaceTransform t =
      -Real.log (∫ x, Real.exp (-((t : ℝ) * (x : ℝ))) ∂(μ : Measure NNReal)) := sorry

/-- The pair `(α, ν)` gives a Lévy--Khinchin representation of a probability measure on
`[0, ∞)` when `ν` has no atom at `0`, has finite truncated first moment
`∫ min (1, x) ν(dx)`, and satisfies the usual Bernstein-function formula for the
log-Laplace transform. -/
def HasSubordinatorLevyKhinchinRepresentation
    (μ : ProbabilityMeasure NNReal) (α : NNReal) (ν : Measure NNReal) : Prop :=
  ν {0} = 0 ∧
    Integrable (fun x : NNReal ↦ min (1 : ℝ) (x : ℝ)) ν ∧
    ∀ t : NNReal,
      μ.logLaplaceTransform t =
        ((α : ℝ) * (t : ℝ)) +
          ∫ x : NNReal, (1 - Real.exp (-((t : ℝ) * (x : ℝ)))) ∂ν
-- Proof sketch: this is the defining package of conditions appearing in the subordinator
-- Lévy--Khinchin formula: vanishing at `0`, truncated first-moment integrability, and the
-- Bernstein representation of the log-Laplace transform.
/-- A Lévy--Khinchin representation on `[0, ∞)` is exactly the combination of the support,
truncated first-moment integrability, and log-Laplace identity conditions. -/
theorem hasSubordinatorLevyKhinchinRepresentation_iff
    (μ : ProbabilityMeasure NNReal) (α : NNReal) (ν : Measure NNReal) :
    HasSubordinatorLevyKhinchinRepresentation μ α ν ↔
      ν {0} = 0 ∧
        Integrable (fun x : NNReal ↦ min (1 : ℝ) (x : ℝ)) ν ∧
        ∀ t : NNReal,
          μ.logLaplaceTransform t =
            ((α : ℝ) * (t : ℝ)) +
              ∫ x : NNReal, (1 - Real.exp (-((t : ℝ) * (x : ℝ)))) ∂ν := sorry

-- Proof sketch: the truncated first-moment condition implies that each tail set
-- `Set.Ici (1 / n)` has finite `ν`-mass, and these sets together with `{0}` form a countable
-- measurable cover of `[0, ∞)`. Hence `ν` is σ-finite.
/-- In a subordinator Lévy--Khinchin representation, σ-finiteness of `ν` is a derived property of
the truncated first-moment condition. -/
theorem HasSubordinatorLevyKhinchinRepresentation.sigmaFinite
    {μ : ProbabilityMeasure NNReal} {α : NNReal} {ν : Measure NNReal}
    (hrep : HasSubordinatorLevyKhinchinRepresentation μ α ν) :
    SigmaFinite ν := sorry

-- Proof sketch: for the forward direction, approximate an infinitely divisible law on `[0, ∞)` by
-- compound-Poisson laws, extract the weak limit of the tilted jump measures, and recover the
-- Bernstein representation of the log-Laplace transform. For the reverse direction, decompose the
-- Lévy measure into annuli, realize each piece as a compound-Poisson summand, and sum the
-- independent nonnegative jumps to obtain an infinitely divisible law with the prescribed
-- exponent. Uniqueness follows from the uniqueness of the Bernstein representation.
/-- Theorem 16.14: a probability measure on `[0, ∞)` is infinitely divisible if and only if its
log-Laplace transform admits a unique Lévy--Khinchin representation by a deterministic part
`α ≥ 0` and a Lévy measure on `(0, ∞)`. -/
theorem isInfinitelyDivisibleOnNNReal_iff_exists_unique_levyKhinchin_pair
    (μ : ProbabilityMeasure NNReal) :
    IsInfinitelyDivisible μ ↔
      ∃! p : NNReal × Measure NNReal,
        HasSubordinatorLevyKhinchinRepresentation μ p.1 p.2 := sorry

end MeasureTheory.ProbabilityMeasure
