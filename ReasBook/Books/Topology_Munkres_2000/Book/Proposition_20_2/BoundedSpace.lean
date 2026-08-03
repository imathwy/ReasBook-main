module

public import Topology_Munkres_2000.Book.Theorem_20_1.BoundedMetric
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

universe u

public section

namespace MetricSpace.standardBounded

variable {X : Type u}

/-- The bornology induced by the standard bounded metric is bounded. -/
instance boundedSpace (m : MetricSpace X) : @BoundedSpace X m.standardBounded.toBornology := by
  -- Use the standard bounded metric so the inferred bornology matches the target bornology.
  letI : MetricSpace X := m.standardBounded
  -- Its diameter is at most `1`, giving a uniform bound for all pairs of points.
  rw [Metric.boundedSpace_iff]
  exact ⟨1, MetricSpace.standardBounded_dist_le_one m⟩

end MetricSpace.standardBounded

end
