import AchimKlenkeLean.Items.Chap08.Example_8_27
import AchimKlenkeLean.Items.Chap09.Definition_9_10
import AchimKlenkeLean.Items.Chap14.Definition_14_6
import AchimKlenkeLean.Items.Chap17.Definition_17_16
import AchimKlenkeLean.Items.Chap17.Theorem_17_8
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u v w

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]

-- Proof sketch: `hp` upgrades the source-facing stochastic matrix `p` to the owner abstraction
-- `IsMarkovKernel (discreteMatrixKernel p)` via `discreteMatrixKernel_isMarkovKernel`. Then apply
-- `isMarkovProcessRealization_of_oneStepKernel` to the path space `ℕ → E` and the canonical
-- coordinate process `Function.eval`; the hypothesis `hstep` is exactly the required one-step
-- conditional law.
/-- Theorem 17.17 (1): if `P x` is the path-space law on `E^ℕ` started from `x` whose canonical
coordinate process has one-step transition matrix `p`, then the canonical process is the discrete
Markov chain with transition matrix `p`. -/
theorem canonicalProcess_isMarkovProcessRealization_of_stochasticMatrix
    (p : E → E → ENNReal) (hp : IsStochasticMatrix p)
    (P : E → ProbabilityMeasure (ℕ → E))
    (hstart : ∀ x : E, (P x : Measure (ℕ → E)).map (Function.eval 0) = Measure.dirac x)
    (hstep :
      ∀ x : E, ∀ ⦃A : Set E⦄, MeasurableSet A → ∀ n : ℕ,
        (P x)⟦Function.eval (n + 1) ⁻¹' A | generatedFiltrationSpace Function.eval n⟧ =ᵐ[
            (P x : Measure (ℕ → E))]
          fun ω ↦ ((discreteMatrixKernel p) (Function.eval n ω)).real A) :
    IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P Function.eval := sorry

section

variable {Ω : Type v} [MeasurableSpace Ω]
variable {Ω' : Type w} [MeasurableSpace Ω']

-- Proof sketch: apply `finiteDimensionalDistribution_eq_of_sameSemigroup` to the common semigroup
-- `n ↦ discreteMatrixKernel p ^ n`; this identifies all ordered finite-dimensional distributions
-- of realizations with the same transition matrix.
/-- Theorem 17.17 (2): in particular, a stochastic matrix determines the finite-dimensional
distributions of a discrete Markov chain uniquely. -/
theorem finiteDimensionalDistribution_eq_of_same_stochasticMatrix
    (p : E → E → ENNReal)
    {P : E → ProbabilityMeasure Ω} {Q : E → ProbabilityMeasure Ω'}
    {X : ℕ → Ω → E} {Y : ℕ → Ω' → E}
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) Q Y]
    (x : E) {n : ℕ} (times : Fin (n + 1) → ℕ)
    (h_zero : times 0 = 0) (htimes : StrictMono times) :
    (P x : Measure Ω).map (fun ω i ↦ X (times i) ω) =
      (Q x : Measure Ω').map (fun ω i ↦ Y (times i) ω) := sorry

end

end ProbabilityTheory
