import AchimKlenkeLean.Items.Chap17.Definition_17_30
import AchimKlenkeLean.Items.Chap17.Definition_17_36
import AchimKlenkeLean.Items.Chap17.Definition_17_43
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]
variable {Ω : Type v} [MeasurableSpace Ω]
variable {p : E → E → ℝ≥0∞} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
variable [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]

/- Layering for Theorem 17.51:
- the equivalence with the nonempty set `I` of invariant distributions is the source-facing
  textbook statement.
- `Kernel.Invariant` is the core/canonical owner predicate for a specific invariant distribution.
- `invariantDistributions (discreteMatrixKernel p)` is the bridge/view packaging of that owner
  predicate into the textbook set `I`. -/

-- Proof sketch: use Corollary 17.48 for the forward implication. For the converse, start from an
-- invariant distribution `π`, use irreducibility to show that every singleton has positive `π`
-- mass, and then identify these masses with the reciprocals of the expected first return times;
-- this makes every state positive recurrent.
/-- Theorem 17.51: for an irreducible discrete Markov chain with transition matrix `p`, the chain
is positive recurrent if and only if the set `I` of invariant distributions of
`discreteMatrixKernel p` is nonempty. -/
theorem isPositiveRecurrentMarkovChain_iff_invariantDistributions_ne_empty
    (hirr : IsIrreducibleMarkovChain P X) :
    IsPositiveRecurrentMarkovChain P X ↔ invariantDistributions (discreteMatrixKernel p) ≠ ∅ :=
  sorry

-- Proof sketch: let `π₁` and `π₂` be invariant distributions. The irreducibility hypothesis and
-- the singleton-mass formula from Theorem 17.51 force both measures to have the same value on
-- every singleton `{x}`; on a discrete state space, equality on singletons implies equality of
-- probability measures, so the whole invariant-distribution set is `{π}`.
/-- If an irreducible chain admits an invariant distribution `π`, then that distribution is the
unique element of the invariant-distribution set. -/
theorem invariantDistributions_eq_singleton_of_mem
    (hirr : IsIrreducibleMarkovChain P X) {π : ProbabilityMeasure E}
    (hπ : π ∈ invariantDistributions (discreteMatrixKernel p)) :
    invariantDistributions (discreteMatrixKernel p) = {π} := sorry

-- Proof sketch: use the invariant-measure identity from Theorem 17.47 for the return-cycle
-- occupation measure and compare singleton masses under an irreducible invariant distribution.
-- Summing the last-visit probabilities yields the renewal identity
-- `π {x} * expectedFirstReturnTime P X x = 1`, which rearranges to the stated formula.
/-- If `π` is an invariant distribution of an irreducible chain, then the singleton mass of `π`
at `x` is the reciprocal of the expected first return time to `x`. -/
theorem invariantDistribution_apply_singleton_eq_one_div_expectedFirstReturnTime
    (hirr : IsIrreducibleMarkovChain P X) {π : ProbabilityMeasure E}
    (hπ : Kernel.Invariant (discreteMatrixKernel p) π) (x : E) :
    π {x} = 1 / expectedFirstReturnTime P X x := sorry

-- Proof sketch: irreducibility forces an invariant distribution to charge every singleton
-- positively, since positive mass at one state propagates along positive-probability paths to all
-- others; equivalently, use the reciprocal-return-time formula and finiteness of return times from
-- positive recurrence.
/-- Any invariant distribution of an irreducible chain assigns strictly positive mass to every
singleton. -/
theorem invariantDistribution_apply_singleton_pos
    (hirr : IsIrreducibleMarkovChain P X) {π : ProbabilityMeasure E}
    (hπ : Kernel.Invariant (discreteMatrixKernel p) π) (x : E) :
    0 < π {x} := sorry

end ProbabilityTheory
