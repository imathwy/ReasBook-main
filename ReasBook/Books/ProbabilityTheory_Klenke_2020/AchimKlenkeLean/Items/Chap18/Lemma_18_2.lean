import ProbabilityTheory_Klenke_2020.Items.Chap18.Definition_18_1
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]

-- Proof sketch: choose finitely many positive return times whose gcd is `statePeriod κ x`; the
-- Chapman-Kolmogorov semigroup law makes the positive return-time set at `x` closed under
-- addition, and the Frobenius coin-problem argument then shows that every sufficiently large
-- multiple of `statePeriod κ x` is a nonnegative combination of those return times and hence again
-- lies in `positiveTransitionStepSet κ x x`.
/-- Lemma 18.2: all sufficiently large multiples of the period `statePeriod κ x` are positive
self-return times of `x`, that is, they eventually belong to
`positiveTransitionStepSet κ x x`. By `mem_positiveTransitionStepSet_iff`, this is equivalent to
the positivity of the corresponding self-return probabilities. -/
theorem eventually_positive_self_return_probability_at_period_multiples
    (κ : Kernel E E) (x : E) :
    ∃ n_x : ℕ, ∀ ⦃n : ℕ⦄, n_x ≤ n →
      n * statePeriod κ x ∈ positiveTransitionStepSet κ x x :=
  sorry

end ProbabilityTheory
