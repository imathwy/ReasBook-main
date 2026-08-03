module

public import Topology_Munkres_2000.Book.Example_13_1.CircularRegions
public import Topology_Munkres_2000.Book.Example_13_2

public section

namespace EuclideanPlane

/-- Example 13.4: Circular regions and rectangular regions generate the same topology
on the Euclidean plane. -/
theorem generateFrom_circularRegions_eq_rectangularRegions :
    TopologicalSpace.generateFrom circularRegions =
      TopologicalSpace.generateFrom rectangularRegions :=
  by
    rw [← isTopologicalBasis_circularRegions.eq_generateFrom,
      ← isTopologicalBasis_rectangularRegions.eq_generateFrom]

end EuclideanPlane
