module

public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Topology.Separation.Regular

public section

universe u v

namespace ChartedSpace

/-- A normal space charted by a `T1Space` is Hausdorff. -/
theorem t2SpaceOfNormal (H : Type u) {M : Type v} [TopologicalSpace H] [TopologicalSpace M]
    [T1Space H] [ChartedSpace H M] [NormalSpace M] : T2Space M := by
  rw [t2Space_iff_disjoint_nhds]
  intro x y hxy
  have hT1 := ChartedSpace.t1Space H M
  simpa only [nhdsSet_singleton] using
    (normal_separation (hT1.t1 x) (hT1.t1 y)
      (Set.disjoint_singleton_left.mpr hxy)).disjoint_nhdsSet

end ChartedSpace
