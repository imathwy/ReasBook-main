module

public import Mathlib.Topology.Bases

public section

/- Lemma 13.1: If `B` is a basis for the topology on `X`, then a set is open
exactly when it is a union of elements of `B`. -/
#check TopologicalSpace.IsTopologicalBasis.open_iff_eq_sUnion
