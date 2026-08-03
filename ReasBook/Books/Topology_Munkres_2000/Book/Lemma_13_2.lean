module

public import Mathlib.Topology.Bases

public section

/- Lemma 13.2. A collection `𝒞` of open subsets of a topological space is a
basis when every open neighborhood of each point contains a member of `𝒞`
containing that point. -/
#check TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
