module

public import Topology_Munkres_2000.Book.Example_43_2
public import Mathlib.Topology.MetricSpace.Bounded

public section

/- The standard metric on `ℝ` in Example 45.2 is `dist a b = |a - b|`. -/
#check Real.dist_eq

/- Example 45.2 (1): The real line with its standard metric is complete. -/
#synth CompleteSpace ℝ

/-- Example 45.2 (2): The real line with its standard metric is not totally bounded. -/
theorem real_not_totallyBounded :
    ¬ TotallyBounded (Set.univ : Set ℝ) := by
  -- Total boundedness would place the whole line inside one closed ball about zero.
  intro hTotallyBounded
  obtain ⟨radius, hSubset⟩ := hTotallyBounded.isBounded.subset_closedBall (0 : ℝ)
  -- Since zero lies in that ball, its radius must be nonnegative.
  have hRadiusNonnegative : 0 ≤ radius := by
    have hZeroMem := hSubset (Set.mem_univ (0 : ℝ))
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_zero] using hZeroMem
  -- The point just beyond the radius cannot satisfy the resulting distance bound.
  have hBeyondMem := hSubset (Set.mem_univ (radius + 1))
  have hBeyondNonnegative : 0 ≤ radius + 1 := by
    linarith
  have hImpossible : radius + 1 ≤ radius := by
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero,
      abs_of_nonneg hBeyondNonnegative] using hBeyondMem
  linarith

/- Example 45.2 (3): The open unit interval is totally bounded. -/
#check (totallyBounded_Ioo (-1 : ℝ) 1 : TotallyBounded (Set.Ioo (-1 : ℝ) 1))

/- Example 45.2 (4): The open unit interval with its inherited metric is not complete. -/
#check not_completeSpace_openUnitInterval

/- Example 45.2 (5): The closed unit interval with its inherited metric is complete. -/
#synth CompleteSpace (Set.Icc (-1 : ℝ) 1)

/- Example 45.2 (6): The closed unit interval is totally bounded. -/
#check (totallyBounded_Icc (-1 : ℝ) 1 : TotallyBounded (Set.Icc (-1 : ℝ) 1))

end
