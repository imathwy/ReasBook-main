module

import Topology_Munkres_2000.Book.Exercise_43_6.Subspace
public import Mathlib.Topology.Instances.Irrational
public import Mathlib.Topology.Metrizable.CompletelyMetrizable

public section

namespace Irrational

/-- The subtype of irrational real numbers is completely metrizable. -/
instance instIsCompletelyMetrizableSpace :
    TopologicalSpace.IsCompletelyMetrizableSpace {x : ℝ // Irrational x} :=
  IsGδ.setOf_irrational.isCompletelyMetrizableSpace

end Irrational
