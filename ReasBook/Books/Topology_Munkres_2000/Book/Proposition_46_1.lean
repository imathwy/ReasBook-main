module

public import Topology_Munkres_2000.Book.Proposition_46_1.Topologies

public section

universe u v

variable (X : Type u) (Y : Type v) [TopologicalSpace X] [UniformSpace Y]

/- Proposition 46.1. The three topologies on `X → Y` compared in Theorem 46.7 are
pointwise convergence, compact convergence, and uniform convergence. -/
#check (Pi.topologicalSpace : TopologicalSpace (X → Y))
#check FunctionTopology.compact X Y
#check FunctionTopology.uniform X Y

