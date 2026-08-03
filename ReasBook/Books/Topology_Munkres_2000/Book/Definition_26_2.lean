module

public import Mathlib.Topology.Compactness.Compact

/- Definition 26.2. A topological space `X` is compact if every open covering of
`X` contains a finite subcollection that also covers `X`. -/
#check CompactSpace
#check isCompact_univ_iff
#check isCompact_iff_finite_subcover
