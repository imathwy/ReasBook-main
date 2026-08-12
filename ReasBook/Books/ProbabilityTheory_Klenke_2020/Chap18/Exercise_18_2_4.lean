import ProbabilityTheory_Klenke_2020.Chap17.Definition_17_30
import ProbabilityTheory_Klenke_2020.Chap17.Definition_17_36
import ProbabilityTheory_Klenke_2020.Chap17.Theorem_17_17
import ProbabilityTheory_Klenke_2020.Chap18.Definition_18_1
import ProbabilityTheory_Klenke_2020.Chap18.Definition_18_5
import ProbabilityTheory_Klenke_2020.Chap18.Example_18_6
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

local notation "AxisState" => ℤ × ℤ

private abbrev isHorizontalNeighbor (x y : AxisState) : Prop :=
  (y.1 = x.1 + 1 ∧ y.2 = x.2) ∨ (y.1 = x.1 - 1 ∧ y.2 = x.2)

private abbrev isVerticalNeighbor (x y : AxisState) : Prop :=
  (y.1 = x.1 ∧ y.2 = x.2 + 1) ∨ (y.1 = x.1 ∧ y.2 = x.2 - 1)

private abbrev isAxisNeighbor (x y : AxisState) : Prop :=
  isHorizontalNeighbor x y ∨ isVerticalNeighbor x y

/-- The transition matrix of the walk on `ℤ²` whose vertical moves are blocked away from the
vertical axis: on the axis it is the symmetric nearest-neighbor walk, while off the axis it moves
horizontally by `±1` with probability `1 / 4` each and otherwise stays put with probability
`1 / 2`. -/
def vertical_axis_blocked_walk_transition_matrix : AxisState → AxisState → ℝ≥0∞
  | x, y =>
      if x.1 = 0 then
        if isAxisNeighbor x y then
          1 / 4
        else
          0
      else if isHorizontalNeighbor x y then
        1 / 4
      else if y = x then
        1 / 2
      else
        0

-- Proof sketch: this is just the defining case split for
-- `vertical_axis_blocked_walk_transition_matrix`.
/-- The axis-blocked walk transition matrix is given by the stated axis and off-axis cases. -/
theorem vertical_axis_blocked_walk_transition_matrix_apply (x y : AxisState) :
    vertical_axis_blocked_walk_transition_matrix x y =
      if x.1 = 0 then
        if (y.1 = x.1 + 1 ∧ y.2 = x.2) ∨
            (y.1 = x.1 - 1 ∧ y.2 = x.2) ∨
            (y.1 = x.1 ∧ y.2 = x.2 + 1) ∨
            (y.1 = x.1 ∧ y.2 = x.2 - 1) then
          1 / 4
        else
          0
      else if (y.1 = x.1 + 1 ∧ y.2 = x.2) ∨ (y.1 = x.1 - 1 ∧ y.2 = x.2) then
        1 / 4
      else if y = x then
        1 / 2
      else
        0 := by
  simp [vertical_axis_blocked_walk_transition_matrix, isAxisNeighbor,
    isHorizontalNeighbor, isVerticalNeighbor, or_assoc]

section RealizationResults

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : AxisState → ProbabilityMeasure Ω} {X : ℕ → Ω → AxisState}
variable [IsMarkovProcessRealization
  (fun n : ℕ ↦ (discreteMatrixKernel vertical_axis_blocked_walk_transition_matrix) ^ n) P X]

-- Proof sketch: project the chain to its first coordinate. Away from the axis this coordinate is
-- a lazy nearest-neighbor walk on `ℤ` and it returns to `0` almost surely, while each visit to
-- the axis restarts a recurrent vertical excursion. The chain is therefore recurrent, but the
-- expected return time is infinite as in the two-dimensional simple random walk regime.
/-- Exercise 18.2.4 (1): every realization of the axis-blocked walk on `ℤ²` is null recurrent. -/
theorem vertical_axis_blocked_walk_isNullRecurrentMarkovChain :
    IsNullRecurrentMarkovChain P X := sorry

-- Proof sketch: the horizontal coordinate can always be moved one step toward `0`, along the
-- axis the walk can change the vertical coordinate by nearest-neighbor moves, and then the
-- horizontal coordinate can be moved away from the axis again. Concatenating such paths gives a
-- positive-probability route between any two states.
/-- Exercise 18.2.4 (2): every realization of the axis-blocked walk on `ℤ²` is irreducible. -/
theorem vertical_axis_blocked_walk_isIrreducibleMarkovChain :
    IsIrreducibleMarkovChain P X := sorry

end RealizationResults

-- Proof sketch: every off-axis state has a one-step self-loop of probability `1 / 2`, so its
-- period is `1`. Irreducibility then forces all states, including those on the vertical axis, to
-- have period `1`.
/-- Exercise 18.2.4 (3): the axis-blocked walk on `ℤ²` is aperiodic. -/
theorem vertical_axis_blocked_walk_isAperiodic :
    IsAperiodic (discreteMatrixKernel vertical_axis_blocked_walk_transition_matrix) := sorry

section IndependentCoalescence

variable {Ω : Type v} [MeasurableSpace Ω]
variable {Pcouple : AxisState × AxisState → ProbabilityMeasure Ω}
variable {Z : ℕ → Ω → AxisState × AxisState}
variable [IsMarkovProcessRealization
  (fun n : ℕ ↦
    discreteMatrixKernel
      (independentCoalescentMatrix vertical_axis_blocked_walk_transition_matrix) ^ n)
  Pcouple Z]

-- Proof sketch: before coalescence the difference of the two coordinates evolves like the
-- difference of two independent copies of the axis-blocked walk. The null-recurrent structure lets
-- the pair separate repeatedly, so the diagonal is not trapped quickly enough for the tail
-- disagreement probabilities to tend to `0`. Exercise 18.2.2 already identifies the independent
-- coalescent realization as a Markov coupling, so this tail-condition failure is exactly the
-- negation of the canonical Chapter 18 owner `IsSuccessfulMarkovCoupling`.
/-- Exercise 18.2.4 (4): the independent coalescent chain built from the axis-blocked walk is not
a successful Markov coupling. -/
theorem independentCoalescentChain_not_isSuccessfulMarkovCoupling :
    ¬ IsSuccessfulMarkovCoupling vertical_axis_blocked_walk_transition_matrix Pcouple Z := sorry

-- Proof sketch: unpack `IsSuccessfulMarkovCoupling`; the failure comes from its tail-disagreement
-- field.
/-- For the axis-blocked walk, some initial pair has tail disagreement probabilities that do not
converge to `0`. -/
theorem independentCoalescentChain_tail_disagreement_not_tendsto_zero :
    ∃ x y : AxisState,
      ¬ Filter.Tendsto
        (fun n : ℕ ↦
          (Pcouple (x, y) : Measure Ω) (⋃ m ≥ n, {ω | (Z m ω).1 ≠ (Z m ω).2}))
        Filter.atTop (nhds 0) := sorry

end IndependentCoalescence

end ProbabilityTheory
