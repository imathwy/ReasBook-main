module

public import Topology_Munkres_2000.Book.Definition_25_4.Neighborhoods

public section

/-- Exercise 25.4: Every connected open subset of a locally path-connected space is
path connected. This is the forward direction of
`IsOpen.isConnected_iff_isPathConnected`. -/
theorem IsOpen.isPathConnected_of_isConnected {X : Type u} [TopologicalSpace X]
    [LocallyPathConnectedSpace X] {U : Set X} (h_open : IsOpen U)
    (h_connected : IsConnected U) : IsPathConnected U :=
  h_open.isConnected_iff_isPathConnected.mp h_connected
