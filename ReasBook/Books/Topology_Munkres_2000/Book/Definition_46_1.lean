module

public import Topology_Munkres_2000.Book.Definition_46_1.PointwiseTopology

public section

/- Definition 46.1: For `x : X` and an open set `U ⊆ Y`, the sets
`pointwiseSubbasicSet x U` form a subbasis for the topology of pointwise convergence,
also called the point-open topology, on `X → Y`. -/
#check pointwiseSubbasicSet
#check pointwiseSubbasicSet_eq_preimage
#check pointwiseTopology_eq_generateFrom
