module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Connected

public section

/-- Example 24.5: If `n > 1`, the unit sphere in `ℝⁿ` is path connected. -/
theorem isPathConnected_unitSphere (n : ℕ) (hn : 1 < n) :
    IsPathConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  apply isPathConnected_sphere ?_ 0 (by positivity)
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
  exact_mod_cast hn
