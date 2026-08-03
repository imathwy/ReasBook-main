module

public import Mathlib.Topology.Separation.Hausdorff

public section

/-- Remark 29.2: In a Hausdorff space, having some compact neighborhood at every
point is equivalent to having arbitrarily small compact neighborhoods. -/
theorem weaklyLocallyCompactSpace_iff_locallyCompactSpace {X : Type u}
    [TopologicalSpace X] [T2Space X] :
    WeaklyLocallyCompactSpace X ↔ LocallyCompactSpace X :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩
