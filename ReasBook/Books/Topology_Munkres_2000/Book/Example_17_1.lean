module

public import Mathlib.Topology.Instances.Real.Lemmas

public section

/- Example 17.1 (1): Every closed interval `Set.Icc a b` in `ℝ` is closed. -/
#check (fun a b : ℝ ↦ (isClosed_Icc : IsClosed (Set.Icc a b)))

/- Example 17.1 (2): Every closed ray `Set.Ici a` in `ℝ` is closed. -/
#check (fun a : ℝ ↦ (isClosed_Ici : IsClosed (Set.Ici a)))

namespace Real

/-- Example 17.1 (3): If `a < b`, then `Set.Ico a b` is not open in `ℝ`. -/
theorem not_isOpen_Ico (a b : ℝ) (hab : a < b) : ¬ IsOpen (Set.Ico a b) := by
  intro h
  have ha : a ∈ Set.Ioo a b := by
    rw [← interior_Ico, h.interior_eq]
    exact ⟨le_rfl, hab⟩
  exact (lt_irrefl a) ha.1

/-- Example 17.1 (4): If `a < b`, then `Set.Ico a b` is not closed in `ℝ`. -/
theorem not_isClosed_Ico (a b : ℝ) (hab : a < b) : ¬ IsClosed (Set.Ico a b) := by
  simpa only [isClosed_Ico_iff, not_le] using hab

end Real
