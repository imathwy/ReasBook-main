module

public import Mathlib.Topology.Connected.LocallyPathConnected

/- Theorem 25.5 (1): Each path component of a topological space is contained in
the connected component indexed by the same point. -/
#check pathComponent_subset_component

/- Theorem 25.5 (2): In a locally path connected space, the path component and
connected component indexed by any point coincide. -/
#check pathComponent_eq_connectedComponent
