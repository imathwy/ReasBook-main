module

public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Interval.Set.Defs

public section

universe u

/- Notation 1.3. The notation `a ≠ b` means that `a` and `b` are different
objects; the same notation applies to different sets. -/
#check fun {α : Type u} (a b : α) ↦ a ≠ b

/-- The set of nonnegative real numbers differs from the set of positive real numbers. -/
theorem nonnegativeReals_ne_positiveReals :
    Set.Ici (0 : ℝ) ≠ Set.Ioi (0 : ℝ) := by
  intro h
  have h_zero : (0 : ℝ) ∈ Set.Ioi 0 := h ▸ Set.mem_Ici.2 le_rfl
  exact lt_irrefl 0 (Set.mem_Ioi.1 h_zero)
