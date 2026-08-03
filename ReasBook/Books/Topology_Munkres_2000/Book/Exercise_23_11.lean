module

public import Mathlib.Topology.Connected.Clopen

public section

namespace Topology.IsQuotientMap

universe u v

variable {X : Type u} {Y : Type v}
variable [TopologicalSpace X] [TopologicalSpace Y]

/-- Exercise 23.11: If a quotient map has connected point fibers and its codomain is
connected, then its domain is connected. -/
theorem connectedSpace_of_connected_fibers {p : X → Y} (hp : IsQuotientMap p)
    (h_fibers : ∀ y : Y, IsConnected (p ⁻¹' ({y} : Set Y))) [ConnectedSpace Y] :
    ConnectedSpace X := by
  rw [connectedSpace_iff_univ]
  simpa using hp.isCoinducing.isConnected_preimage_of_isClosed h_fibers isClosed_univ
    isConnected_univ

end Topology.IsQuotientMap
