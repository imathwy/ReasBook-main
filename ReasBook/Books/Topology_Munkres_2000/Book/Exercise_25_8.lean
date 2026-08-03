module

public import Mathlib.Topology.Connected.LocallyConnected

public section

open Set Topology

namespace Topology.IsQuotientMap

/-- Exercise 25.8: The codomain of a quotient map from a locally connected space is
locally connected. -/
theorem locallyConnectedSpace {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] [LocallyConnectedSpace X] {p : X → Y} (hp : IsQuotientMap p) :
    LocallyConnectedSpace Y := by
  rw [locallyConnectedSpace_iff_connectedComponentIn_open]
  intro U hU y hy
  apply (IsCoinducing.isOpen_preimage hp.isCoinducing).mp
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  have hxp : p x ∈ connectedComponentIn U y := hx
  have hxU : x ∈ p ⁻¹' U := connectedComponentIn_subset U y hxp
  refine ⟨connectedComponentIn (p ⁻¹' U) x, ?_,
    (hp.continuous.isOpen_preimage U hU).connectedComponentIn, mem_connectedComponentIn hxU⟩
  intro z hz
  rw [connectedComponentIn_eq hxp]
  have hpreconnected : IsPreconnected (p '' connectedComponentIn (p ⁻¹' U) x) :=
    isPreconnected_connectedComponentIn.image p hp.continuous.continuousOn
  have himage : p '' connectedComponentIn (p ⁻¹' U) x ⊆ U :=
    (image_mono (connectedComponentIn_subset (p ⁻¹' U) x)).trans (image_preimage_subset p U)
  exact hpreconnected.subset_connectedComponentIn ⟨x, mem_connectedComponentIn hxU, rfl⟩ himage
    ⟨z, hz, rfl⟩

end Topology.IsQuotientMap
