module

public import Topology_Munkres_2000.Book.Remark_41_3

public section

/- Exercise 41.9. A locally compact, connected topological group is paracompact.
The canonical instance proves the stronger result without connectedness. Munkres includes the
`T₁` axiom in the definition of a topological group, while mathlib records it separately. -/
#check IsTopologicalGroup.paracompactSpace
