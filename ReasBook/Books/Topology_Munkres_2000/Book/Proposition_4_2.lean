module

public import Topology_Munkres_2000.Book.Definition_4_6

public section

namespace Real

/-- First assertion of Proposition 4.2: The set of positive real numbers is inductive. -/
theorem isInductive_Ioi_zero : IsInductive (Set.Ioi 0) := by
  -- The base point is positive, and adding one preserves positivity.
  rw [isInductive_iff]
  constructor
  · norm_num
  · intro x hx
    exact hx.trans (lt_add_of_pos_right x zero_lt_one)

/-- Second assertion of Proposition 4.2: Every positive integer is a positive real number. -/
theorem positiveIntegers_subset_Ioi_zero : ℤ₊ ⊆ Set.Ioi 0 := by
  -- Membership in `ℤ₊` places an element in every inductive set.
  intro x hx
  exact (mem_positiveIntegers_iff x).mp hx (Set.Ioi 0) isInductive_Ioi_zero

/-- Helper for Proposition 4.2: the real numbers at least one form an inductive set. -/
lemma isInductive_Ici_one : IsInductive (Set.Ici 1) := by
  -- One lies in the interval, and adding one preserves its lower bound.
  rw [isInductive_iff]
  constructor
  · exact Set.mem_Ici.mpr le_rfl
  · intro x hx
    exact Set.mem_Ici.mpr
      ((Set.mem_Ici.mp hx).trans (le_add_of_nonneg_right zero_le_one))

/-- Proposition 4.2: One is the least positive integer. -/
theorem isLeast_one_positiveIntegers : IsLeast ℤ₊ 1 := by
  constructor
  · -- Every inductive set contains its base point `1`.
    rw [mem_positiveIntegers_iff]
    intro A hA
    exact (isInductive_iff A).mp hA |>.1
  · -- Specializing to `[1, ∞)` gives the universal lower bound.
    intro x hx
    exact (mem_positiveIntegers_iff x).mp hx (Set.Ici 1) isInductive_Ici_one

end Real
