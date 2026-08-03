module

public import Mathlib.Analysis.Complex.Circle

public section

universe u

namespace Topology

/-- A simple closed curve is a topological space homeomorphic to the unit circle. -/
class IsSimpleClosedCurve (X : Type u) [TopologicalSpace X] : Prop where
  /-- A simple closed curve admits a homeomorphism to the unit circle. -/
  homeomorphic_circle : Nonempty (X ≃ₜ Circle)

namespace IsSimpleClosedCurve

/-- A space is a simple closed curve exactly when it is homeomorphic to the unit circle. -/
theorem iff_nonempty_homeomorph_circle (X : Type u) [TopologicalSpace X] :
    IsSimpleClosedCurve X ↔ Nonempty (X ≃ₜ Circle) := by
  constructor
  · exact fun h ↦ h.homeomorphic_circle
  · exact fun h ↦ ⟨h⟩

end IsSimpleClosedCurve

end Topology

namespace Circle

/-- The unit circle is a simple closed curve. -/
instance instIsSimpleClosedCurve : Topology.IsSimpleClosedCurve Circle :=
  ⟨⟨Homeomorph.refl Circle⟩⟩

end Circle
