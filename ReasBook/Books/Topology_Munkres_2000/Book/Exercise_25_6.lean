module

public import Topology_Munkres_2000.Book.Exercise_25_6.WeaklyLocallyConnected

public section

open Set Topology
open scoped Topology

universe u

/-- Exercise 25.6: Every weakly locally connected space is locally connected. -/
instance WeaklyLocallyConnectedSpace.toLocallyConnectedSpace
    (X : Type u) [TopologicalSpace X] [WeaklyLocallyConnectedSpace X] :
    LocallyConnectedSpace X :=
  locallyConnectedSpace_iff_connected_subsets.2 fun x U hU ↦ by
    have hx := WeaklyLocallyConnectedSpace.weaklyLocallyConnectedAt x
    rw [weaklyLocallyConnectedAt_iff] at hx
    obtain ⟨C, hCx, hC, hCU⟩ := hx U hU
    exact ⟨C, hCx, hC.isPreconnected, hCU⟩
