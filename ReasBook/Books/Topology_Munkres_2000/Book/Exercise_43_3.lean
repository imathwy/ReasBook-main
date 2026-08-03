module

public import Topology_Munkres_2000.Book.Exercise_43_3.MetricEquivalence
public import Topology_Munkres_2000.Book.Theorem_20_1.BoundedMetric
import Topology_Munkres_2000.Book.Proposition_43_2.Convergence

public section

universe u

/- Exercise 43.3 (1): two metrics are metrically equivalent when the identity map is uniformly
continuous in both directions. -/
#check MetricSpace.Equivalent

namespace MetricSpace.standardBounded

variable {X : Type u}

/-- Exercise 43.3 (2): every metric is metrically equivalent to its standard bounded metric. -/
theorem equivalent (m : MetricSpace X) : m.Equivalent m.standardBounded := by
  rw [MetricSpace.equivalent_iff_toUniformSpace_eq, toUniformSpace_eq]

end MetricSpace.standardBounded

/- Exercise 43.3 (3): completeness is invariant under metric equivalence. -/
#check MetricSpace.Equivalent.completeSpace_iff

end
