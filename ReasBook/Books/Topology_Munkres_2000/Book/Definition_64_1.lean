module

public import Topology_Munkres_2000.Book.Example_50_6.LinearGraph

public section

/- Definition 64.1: A finite linear graph is a Hausdorff space presented as a finite
union of embedded arcs such that two distinct arcs meet in at most one common endpoint.
The arc images are its edges, and their endpoint images are its vertices. -/
#check FiniteLinearGraph
#check FiniteLinearGraph.edgeSet
#check FiniteLinearGraph.vertexSet
