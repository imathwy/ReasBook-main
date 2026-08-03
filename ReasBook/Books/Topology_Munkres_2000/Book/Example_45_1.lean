module

public import Topology_Munkres_2000.Book.Proposition_43_2.Convergence

public import Topology_Munkres_2000.Book.Proposition_20_2.BoundedSpace
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.Basic

public section

/- Example 45.1 (1): Total boundedness implies boundedness. -/
#check TotallyBounded.isBounded

/- Example 45.1 (2): The real line with its standard bounded metric is bounded. -/
#check MetricSpace.standardBounded.boundedSpace (inferInstance : MetricSpace ℝ)

/-- Example 45.1 (3): The real line with distance `min |a - b| 1` is not totally bounded. -/
theorem standardBoundedReal_not_totallyBounded :
    ¬ (inferInstance : MetricSpace ℝ).standardBounded.IsTotallyBounded Set.univ := by
  -- Transfer total boundedness back to the ordinary real metric.
  rw [MetricSpace.standardBounded.totallyBounded_iff (inferInstance : MetricSpace ℝ)]
  intro h
  -- Total boundedness would give a uniform bound on all pairwise real distances.
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp h.isBounded
  have hzero : (0 : ℝ) ∈ Set.univ := Set.mem_univ 0
  have hsum : C + 1 ∈ Set.univ := Set.mem_univ (C + 1)
  have hdist : dist (0 : ℝ) (C + 1) ≤ C := hC hzero hsum
  have habs : |C + 1| ≤ C := by
    simpa only [Real.dist_eq, zero_sub, abs_neg] using hdist
  -- The absolute-value lower bound contradicts the strict increase from adding one.
  have hle : C + 1 ≤ C := (le_abs_self (C + 1)).trans habs
  exact (not_le_of_gt (lt_add_of_pos_right C zero_lt_one)) hle
