module

public import Topology_Munkres_2000.Book.Example_50_6

public section

/- Example 64.1: After labeling its `n` vertices by `Fin n`, a graph having one edge
between every pair of distinct vertices is `SimpleGraph.completeGraph (Fin n)`, denoted
`Gₙ` in the source. In particular, the complete graph on five vertices has no linear
realization embedding in `ℝ × ℝ`. -/
#check (fun n : ℕ ↦ SimpleGraph.completeGraph (Fin n))
#check SimpleGraph.top_adj
#check completeGraphFive_not_isEmbedding
