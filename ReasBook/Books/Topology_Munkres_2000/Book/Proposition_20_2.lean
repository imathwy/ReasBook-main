module

public import Topology_Munkres_2000.Book.Theorem_20_1.BoundedMetric
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

public section

universe u

namespace MetricSpace.standardBounded

variable {X : Type u}

/-- Proposition 20.2: The bornology induced by the standard bounded metric is bounded. -/
theorem boundedSpace (m : MetricSpace X) : @BoundedSpace X m.standardBounded.toBornology := by
  -- Use the standard bounded metric so the inferred bornology matches the target bornology.
  letI : MetricSpace X := m.standardBounded
  -- Its diameter is at most `1`, giving a uniform bound for all pairs of points.
  rw [Metric.boundedSpace_iff]
  exact ⟨1, MetricSpace.standardBounded_dist_le_one m⟩

end MetricSpace.standardBounded

/- Proposition 20.2: The standard bounded metric corresponding to a metric induces
the same topology, and every subset is bounded relative to this metric. -/
#check MetricSpace.standardBounded
#check MetricSpace.standardBounded_toTopologicalSpace
#check MetricSpace.standardBounded.boundedSpace
