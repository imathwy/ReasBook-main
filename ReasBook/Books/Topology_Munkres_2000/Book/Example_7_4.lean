module

public import Mathlib.Data.PNat.Basic
public import Mathlib.Order.Bounds.Defs

public section

/-- Example 7.4. For any proposed recursion `h : ℕ+ → C`, the value `h i`
cannot be the least element outside the image through index `i + 1`. -/
theorem not_isLeast_unusedThroughNext
    (C : Set ℕ+) (h : ℕ+ → C) (i : ℕ+) :
    ¬ IsLeast (Set.univ \ h '' Set.Iic (i + 1)) (h i) := by
  intro hi
  exact hi.1.2 ⟨i, le_of_lt (PNat.lt_add_right i 1), rfl⟩
