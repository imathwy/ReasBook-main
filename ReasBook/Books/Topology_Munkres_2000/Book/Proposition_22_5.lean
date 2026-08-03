module

public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Separation.Basic

public section

universe u v

namespace Topology.IsQuotientMap

/-- Proposition 22.5: For a quotient map, the quotient space is a `T₁` space
exactly when every fiber, equivalently every element of the associated partition, is closed. -/
theorem t1Space_iff_isClosed_fiber {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {p : X → Y} (hp : IsQuotientMap p) :
    T1Space Y ↔ ∀ y : Y, IsClosed (p ⁻¹' ({y} : Set Y)) := by
  have h_coinducing := hp.isCoinducing
  constructor
  · intro hY y
    exact h_coinducing.isClosed_preimage.mpr (hY.t1 y)
  · intro h
    exact ⟨fun y ↦ h_coinducing.isClosed_preimage.mp (h y)⟩

end Topology.IsQuotientMap
