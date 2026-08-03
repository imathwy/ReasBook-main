module

public import Mathlib.Data.PNat.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

public section

/-- The open interval from `0` to the reciprocal of a positive integer. -/
def reciprocalInitialInterval (n : ℕ+) : Set ℝ :=
  Set.Ioo 0 (1 / (n : ℝ))

/-- Membership in `reciprocalInitialInterval n` means lying strictly between
`0` and `1 / n`. -/
@[simp]
theorem mem_reciprocalInitialInterval {n : ℕ+} {x : ℝ} :
    x ∈ reciprocalInitialInterval n ↔ 0 < x ∧ x < 1 / (n : ℝ) := by
  rfl

/-- Each `reciprocalInitialInterval n` is open in `ℝ`. -/
theorem isOpen_reciprocalInitialInterval (n : ℕ+) :
    IsOpen (reciprocalInitialInterval n) := by
  simpa only [reciprocalInitialInterval] using isOpen_Ioo

/-- The collection of intervals `(0, 1 / n)` indexed by positive integers. -/
def reciprocalInitialIntervals : Set (Set ℝ) :=
  Set.range reciprocalInitialInterval

/-- A set belongs to `reciprocalInitialIntervals` exactly when it is one of the
intervals `reciprocalInitialInterval n`. -/
theorem mem_reciprocalInitialIntervals {U : Set ℝ} :
    U ∈ reciprocalInitialIntervals ↔ ∃ n : ℕ+, reciprocalInitialInterval n = U := by
  rfl

/-- The collection `reciprocalInitialIntervals`, viewed in the subspace `(0, 1)`. -/
def reciprocalInitialIntervalsUnit : Set (Set (Set.Ioo (0 : ℝ) 1)) :=
  Set.range fun n : ℕ+ ↦
    (Subtype.val : Set.Ioo (0 : ℝ) 1 → ℝ) ⁻¹' reciprocalInitialInterval n

/-- A set belongs to `reciprocalInitialIntervalsUnit` exactly when it is the
subspace view of an interval `reciprocalInitialInterval n`. -/
theorem mem_reciprocalInitialIntervalsUnit {U : Set (Set.Ioo (0 : ℝ) 1)} :
    U ∈ reciprocalInitialIntervalsUnit ↔
      ∃ n : ℕ+,
        (Subtype.val : Set.Ioo (0 : ℝ) 1 → ℝ) ⁻¹' reciprocalInitialInterval n = U := by
  rfl

/-- The open interval between the reciprocals of consecutive positive integers. -/
def reciprocalAdjacentInterval (n : ℕ+) : Set ℝ :=
  Set.Ioo (1 / ((n : ℝ) + 1)) (1 / (n : ℝ))

/-- Membership in `reciprocalAdjacentInterval n` means lying strictly between
`1 / (n + 1)` and `1 / n`. -/
@[simp]
theorem mem_reciprocalAdjacentInterval {n : ℕ+} {x : ℝ} :
    x ∈ reciprocalAdjacentInterval n ↔
      1 / ((n : ℝ) + 1) < x ∧ x < 1 / (n : ℝ) := by
  rfl

/-- Each `reciprocalAdjacentInterval n` is open in `ℝ`. -/
theorem isOpen_reciprocalAdjacentInterval (n : ℕ+) :
    IsOpen (reciprocalAdjacentInterval n) := by
  simpa only [reciprocalAdjacentInterval] using isOpen_Ioo

/-- The collection of intervals `(1 / (n + 1), 1 / n)` indexed by positive integers. -/
def reciprocalAdjacentIntervals : Set (Set ℝ) :=
  Set.range reciprocalAdjacentInterval

/-- A set belongs to `reciprocalAdjacentIntervals` exactly when it is one of the
intervals `reciprocalAdjacentInterval n`. -/
theorem mem_reciprocalAdjacentIntervals {U : Set ℝ} :
    U ∈ reciprocalAdjacentIntervals ↔ ∃ n : ℕ+, reciprocalAdjacentInterval n = U := by
  rfl

/-- The collection `reciprocalAdjacentIntervals`, viewed in the subspace `(0, 1)`. -/
def reciprocalAdjacentIntervalsUnit : Set (Set (Set.Ioo (0 : ℝ) 1)) :=
  Set.range fun n : ℕ+ ↦
    (Subtype.val : Set.Ioo (0 : ℝ) 1 → ℝ) ⁻¹' reciprocalAdjacentInterval n

/-- A set belongs to `reciprocalAdjacentIntervalsUnit` exactly when it is the
subspace view of an interval `reciprocalAdjacentInterval n`. -/
theorem mem_reciprocalAdjacentIntervalsUnit {U : Set (Set.Ioo (0 : ℝ) 1)} :
    U ∈ reciprocalAdjacentIntervalsUnit ↔
      ∃ n : ℕ+,
        (Subtype.val : Set.Ioo (0 : ℝ) 1 → ℝ) ⁻¹' reciprocalAdjacentInterval n = U := by
  rfl
