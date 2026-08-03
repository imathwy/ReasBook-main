module

public import Topology_Munkres_2000.Book.Exercise_36_1.Separation
public import Mathlib.Topology.Metrizable.Urysohn

public section

universe u v

namespace ChartedSpace

/-- A Hausdorff second-countable space charted by a locally compact space is metrizable. -/
theorem metrizableSpace (H : Type u) {M : Type v} [TopologicalSpace H] [TopologicalSpace M]
    [ChartedSpace H M] [LocallyCompactSpace H] [T2Space M]
    [SecondCountableTopology M] : TopologicalSpace.MetrizableSpace M := by
  -- First obtain regularity from the chart model and Hausdorffness.
  letI : T3Space M := ChartedSpace.t3Space H
  -- Urysohn metrization now follows from regularity and second countability.
  infer_instance

end ChartedSpace
