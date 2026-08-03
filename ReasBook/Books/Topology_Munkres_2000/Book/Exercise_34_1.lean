module

public import Topology_Munkres_2000.Book.Exercise_34_1.RealLine

public section

/- Exercise 34.1: The real line with the `K`-topology is a Hausdorff space with a
countable basis that is not metrizable. -/
#check (inferInstance : T2Space RealKLine)
#check (inferInstance : SecondCountableTopology RealKLine)

namespace RealKLine

/-- Exercise 34.1: `RealKLine` is not metrizable. -/
theorem notMetrizable : ¬ TopologicalSpace.MetrizableSpace RealKLine := by
  -- A compatible metric would make the `K`-topology regular, contradicting the earlier result.
  intro h
  letI : TopologicalSpace.MetrizableSpace RealKLine := h
  exact RealTopology.kNotRegularSpace (inferInstance : RegularSpace RealKLine)

end RealKLine
