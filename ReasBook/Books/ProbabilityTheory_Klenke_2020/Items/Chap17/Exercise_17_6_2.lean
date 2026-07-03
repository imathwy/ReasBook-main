import AchimKlenkeLean.Items.Chap14.Definition_14_40
import AchimKlenkeLean.Items.Chap17.Theorem_17_25
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

section

variable {E : Type u} [MeasurableSpace E]

/- Layering for Exercise 17.6.2:
- `Kernel.Invariant` is the `core/canonical` owner notion for a measure fixed by one kernel.
- `IsInvariantDistributionForSemigroup` is the `source-facing` semigroup predicate obtained by
  quantifying that owner notion over all times `t`.
- `isInvariantDistributionForSemigroup_iff_qMatrixBalance` is the bridge from this semigroup-level
  invariance predicate to the generator-matrix balance equation. -/

/-- A probability measure is invariant for a Markov semigroup if it is invariant for every
time-`t` transition kernel. -/
def IsInvariantDistributionForSemigroup
    (κ : NNReal → Kernel E E) (π : ProbabilityMeasure E) : Prop :=
  ∀ t : NNReal, Kernel.Invariant (κ t) (π : Measure E)

-- Proof sketch: unfold `IsInvariantDistributionForSemigroup`; it is defined exactly by requiring
-- invariance for each time slice `κ t`.
/-- Semigroup invariance means invariance under each transition kernel `κ t`. -/
theorem isInvariantDistributionForSemigroup_iff
    (κ : NNReal → Kernel E E) (π : ProbabilityMeasure E) :
    IsInvariantDistributionForSemigroup κ π ↔
      ∀ t : NNReal, Kernel.Invariant (κ t) (π : Measure E) :=
  Iff.rfl

end

section

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]

-- Proof sketch: write invariance as `π.bind (κ t) = π`, evaluate both sides on the singleton
-- `{y}`, and differentiate at `t = 0` using the assumed right-derivative formula for the
-- singleton transition probabilities. For the converse, use the balance equation as the vanishing
-- derivative of the singleton masses under the forward equation, then deduce that the law started
-- from `π` is constant in time.
/-- Exercise 17.6.2: for a continuous-time Markov chain with Q-matrix `q`, a probability measure
`π` is invariant exactly when for every state `y` the weighted generator column sum
`∑' x, π {x} * q x y` exists and vanishes. -/
theorem isInvariantDistributionForSemigroup_iff_qMatrixBalance
    (κ : NNReal → Kernel E E) [IsMarkovSemigroup κ]
    (q : E → E → ℝ)
    (hκq : HasGeneratorMatrix κ q)
    (π : ProbabilityMeasure E) :
    IsInvariantDistributionForSemigroup κ π ↔
      ∀ y : E, Summable (fun x : E ↦ (π {x} : ℝ) * q x y) ∧
        (∑' x : E, (π {x} : ℝ) * q x y) = 0 := sorry

end

end ProbabilityTheory
