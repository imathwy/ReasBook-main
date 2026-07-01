import AchimKlenkeLean.Items.Chap17.Definition_17_30
import AchimKlenkeLean.Items.Chap17.Definition_17_43
import AchimKlenkeLean.Items.Chap17.Theorem_17_17
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]
variable {Ω : Type v} [MeasurableSpace Ω]

-- Proof sketch: for a transient chain, the Green-function series is finite at every state, so the
-- transition probabilities `(discreteMatrixKernel p ^ n) x {y}` tend to `0` as `n → ∞`. If an
-- invariant distribution `μ` existed, then the singleton masses of `(discreteMatrixKernel p ^ n)
-- ∘ₘ μ` would stay equal to the singleton masses of `μ`, forcing all of them to vanish and
-- contradicting that `μ` is a probability measure. Thus the invariant-distribution set is empty.
/-- Theorem 17.46: if every state of the discrete Markov chain with transition matrix `p` is
transient, then the invariant-distribution set of `discreteMatrixKernel p` is empty. -/
theorem not_exists_invariantDistribution_of_all_states_transient
    (p : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (htransient : ∀ x : E, IsTransientState P X x) :
    invariantDistributions (discreteMatrixKernel p) = ∅ := sorry

end ProbabilityTheory
