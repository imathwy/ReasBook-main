module

public import Topology_Munkres_2000.Book.Definition_46_1.PointwiseTopology

public section

universe u v

variable (X : Type u) (Y : Type v) [TopologicalSpace Y]

/- Remark 46.1. Finite intersections of the pointwise subbasic sets
`pointwiseSubbasicSet x U` form a basis for the topology of pointwise convergence. -/
#check TopologicalSpace.isTopologicalBasis_of_subbasis (pointwiseTopology_eq_generateFrom X Y)
