module

public import Mathlib.Topology.Bases

public section

/- Lemma 16.1: If `ℬ` is a basis for the topology on `X`, then its inverse
images under `Subtype.val : Y → X`, representing the intersections `B ∩ Y`,
form a basis for the canonical subspace topology on `Y`. -/
#check isTopologicalBasis_subtype
