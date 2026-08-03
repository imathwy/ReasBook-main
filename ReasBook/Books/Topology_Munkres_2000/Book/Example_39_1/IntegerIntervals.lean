module

public import Mathlib.Topology.Instances.Real.Lemmas

public section

/-- The open interval with integer left endpoint `n` and right endpoint `n + 2`. -/
def integerShiftedInterval (n : ℤ) : Set ℝ :=
  Set.Ioo (n : ℝ) ((n : ℝ) + 2)

/-- Membership in `integerShiftedInterval n` means lying strictly between `n`
and `n + 2`. -/
@[simp]
theorem mem_integerShiftedInterval {n : ℤ} {x : ℝ} :
    x ∈ integerShiftedInterval n ↔ (n : ℝ) < x ∧ x < (n : ℝ) + 2 := by
  rfl

/-- Each `integerShiftedInterval n` is open in `ℝ`. -/
theorem isOpen_integerShiftedInterval (n : ℤ) :
    IsOpen (integerShiftedInterval n) := by
  simpa only [integerShiftedInterval] using isOpen_Ioo

/-- The collection of open intervals `(n, n + 2)` indexed by integers. -/
def integerLengthTwoIntervals : Set (Set ℝ) :=
  Set.range integerShiftedInterval

/-- A set belongs to `integerLengthTwoIntervals` exactly when it is one of the
intervals `integerShiftedInterval n`. -/
theorem mem_integerLengthTwoIntervals {U : Set ℝ} :
    U ∈ integerLengthTwoIntervals ↔ ∃ n : ℤ, integerShiftedInterval n = U := by
  rfl
