module

public import Topology_Munkres_2000.Book.Definition_17_4

/- Definition 17.5: A topological space `X` is Hausdorff if every pair of
distinct points has disjoint neighborhoods. Mathlib records this as the
`T2Space X` property. -/
#check T2Space

/- The source definition in terms of disjoint neighborhoods of distinct points. -/
#check t2Space_iff_nhds
