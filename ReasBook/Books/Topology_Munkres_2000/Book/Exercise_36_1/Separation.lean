module

public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Topology.Separation.Regular

public section

universe u v

namespace ChartedSpace

/-- A Hausdorff space charted by a locally compact space is a `T3Space`. -/
theorem t3Space (H : Type u) {M : Type v} [TopologicalSpace H] [TopologicalSpace M]
    [ChartedSpace H M] [LocallyCompactSpace H] [T2Space M] : T3Space M := by
  -- Transfer local compactness through the charts to the manifold.
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  -- Hausdorffness supplies the remaining separation properties for regularity.
  infer_instance

end ChartedSpace
