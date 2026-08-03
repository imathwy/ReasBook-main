module

public import Mathlib.Analysis.Normed.Module.Connected

public section

/-- Exercise 24.9: If `A` is a countable subset of the real plane `ℝ × ℝ`, then
its complement is path connected. -/
theorem Set.Countable.isPathConnected_compl_realPlane {A : Set (ℝ × ℝ)}
    (hA : A.Countable) : IsPathConnected Aᶜ := by
  apply hA.isPathConnected_compl_of_one_lt_rank
  rw [← Module.finrank_eq_rank, Module.finrank_prod]
  norm_num
