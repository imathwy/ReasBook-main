module

public import Topology_Munkres_2000.Book.Example_26_2.Sequence
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Compactness.Compact

public section

/-- Example 26.2: The subspace of `ℝ` consisting of `0` and the reciprocals of positive
integers is compact. -/
theorem reciprocalSequenceSubspace_isCompact : IsCompact reciprocalSequenceSubspace := by
  -- Rewrite the positive-integer reciprocals as a sequence indexed by `ℕ`.
  rw [reciprocalSequenceSubspace_eq_insert_range_nat]
  -- The sequence converges to its adjoined limit point, so their union is compact.
  exact (tendsto_one_div_add_atTop_nhds_zero_nat :
    Filter.Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0)).isCompact_insert_range
