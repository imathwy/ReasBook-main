module

public import Topology_Munkres_2000.Book.Definition_4_8

public section

/- Solution 4.1. The set `ℤ₊` of positive integers has no upper bound in `ℝ`. -/
#check Real.not_bddAbove_positiveIntegers

/-- For every real number, some positive integer is strictly larger. -/
theorem exists_pnat_gt (x : ℝ) : ∃ n : ℕ+, x < n := by
  have h := Real.not_bddAbove_positiveIntegers
  rw [Real.positiveIntegers_eq_range_pnatCast, not_bddAbove_iff] at h
  obtain ⟨_, ⟨n, rfl⟩, hn⟩ := h x
  exact ⟨n, hn⟩
