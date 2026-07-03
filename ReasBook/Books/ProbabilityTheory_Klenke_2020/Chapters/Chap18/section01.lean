import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_18_1 (from Items/Chap18) -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]

/-- Definition 18.1 (1): for states `x` and `y`, `positiveTransitionStepSet κ x y` is the set of
times `n ∈ ℕ₀` for which the `n`-step transition probability from `x` to `y` is strictly
positive. -/
def positiveTransitionStepSet (κ : Kernel E E) (x y : E) : Set ℕ :=
  {n : ℕ | 0 < (κ ^ n) x {y}}

/-- Definition 18.1 (2): the period of the state `x` is the greatest common divisor of the
positive-probability return times from `x` to itself. -/
def statePeriod (κ : Kernel E E) (x : E) : ℕ :=
  sSup {d : ℕ | ∀ n ∈ positiveTransitionStepSet κ x x, d ∣ n}

/-- Definition 18.1 (3): a discrete Markov chain has period `d` when every state has period `d`.
-/
def HasPeriod (κ : Kernel E E) (d : ℕ) : Prop :=
  ∀ x : E, statePeriod κ x = d

/-- Definition 18.1 (4): a discrete Markov chain is aperiodic when every state has period `1`. -/
def IsAperiodic (κ : Kernel E E) : Prop :=
  HasPeriod κ 1

-- Proof sketch: this is immediate from the definition of `positiveTransitionStepSet`.
/-- Membership in `positiveTransitionStepSet κ x y` means exactly that the `n`-step transition
probability from `x` to `y` is strictly positive. -/
theorem mem_positiveTransitionStepSet_iff (κ : Kernel E E) (x y : E) (n : ℕ) :
    n ∈ positiveTransitionStepSet κ x y ↔ 0 < (κ ^ n) x {y} := sorry

-- Proof sketch: `statePeriod κ x` is defined as the supremum of the common divisors of all
-- positive-probability return times to `x`, so it divides each such return time.
/-- The period of a state divides every time at which the chain can return to that state with
positive probability. -/
theorem statePeriod_dvd_of_mem_positiveTransitionStepSet
    (κ : Kernel E E) (x : E) {n : ℕ} (hn : n ∈ positiveTransitionStepSet κ x x) :
    statePeriod κ x ∣ n := sorry

-- Proof sketch: specialize the defining equalities in `HasPeriod κ d` at the states `x` and `y`.
/-- If a chain has period `d`, then all states have the same period. -/
theorem statePeriod_eq_of_hasPeriod
    {κ : Kernel E E} {d : ℕ} (hκ : HasPeriod κ d) (x y : E) :
    statePeriod κ x = statePeriod κ y := sorry

section

variable {F : Type u} [MeasurableSpace F]

-- Proof sketch: unfold `IsAperiodic` and `HasPeriod`; both say exactly that every state period is
-- equal to `1`.
/-- A chain is aperiodic exactly when it has period `1`. -/
theorem isAperiodic_iff_hasPeriod_one (κ : Kernel F F) :
    IsAperiodic κ ↔ HasPeriod κ 1 :=
  Iff.rfl

end

end ProbabilityTheory
