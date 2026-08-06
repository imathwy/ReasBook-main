import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Definition_4_1_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Definition_4_2_8
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.CollapseSubsetPair

open scoped ContinuousMap

noncomputable section

namespace SimpleGraph

variable {V : Type}

/-- A connected simple graph with a chosen maximal subtree and a chosen oriented realization of
each edge. The realization uses `graph.edgeSet` itself as the edge index type, and
`boundary_edge` records that each chosen parameterization has the prescribed underlying edge. -/
structure MaximalTreeQuotientContext (V : Type) where
  graph : SimpleGraph V
  boundary : graph.edgeSet ↪ Fin 2 → V
  boundary_edge (e : graph.edgeSet) : s(boundary e 0, boundary e 1) = e
  connected : graph.Connected
  tree : graph.Subgraph
  maximalTree : IsMaximalSubtree tree

namespace MaximalTreeQuotientContext

/-- The chosen topological realization of the ambient graph. -/
abbrev realization (X : MaximalTreeQuotientContext V) : TopCat :=
  TopCat.of (graphRealization X.boundary)

/-- The edges of `X.graph` belonging to the chosen maximal subtree, viewed as a set of ambient
edge parameters. -/
abbrev treeEdges (X : MaximalTreeQuotientContext V) : Set X.graph.edgeSet :=
  { e | (e : Sym2 V) ∈ X.tree.edgeSet }

/-- The index type of edges of `X.graph` that do not belong to the chosen maximal subtree. -/
abbrev nonTreeEdges (X : MaximalTreeQuotientContext V) :=
  { e : X.graph.edgeSet // e ∉ X.treeEdges }

/-- The realized maximal-tree subspace inside the chosen realization of `X.graph`: all vertices
and exactly the edges belonging to `X.tree`. -/
def treeSubspace (X : MaximalTreeQuotientContext V) : Set X.realization :=
  Set.range (graphVertex X.boundary) ∪
    { x |
        ∃ e : X.graph.edgeSet,
          e ∈ X.treeEdges ∧ x ∈ graphEdge X.boundary e }

/-- The quotient space obtained from the chosen realization of `X.graph` by collapsing the
realized maximal tree to a point. -/
abbrev quotientSpace (X : MaximalTreeQuotientContext V) :=
  collapseSubsetType X.realization X.treeSubspace

/-- The quotient `X / T` viewed as a topological space object. -/
abbrev quotientTopCat (X : MaximalTreeQuotientContext V) : TopCat :=
  TopCat.of X.quotientSpace

/-- The quotient map from the chosen realization of `X.graph` to the quotient collapsing the
realized maximal tree. -/
abbrev quotientMap (X : MaximalTreeQuotientContext V) : C(X.realization, X.quotientTopCat) :=
  collapseSubsetQuotientMap X.treeSubspace

end MaximalTreeQuotientContext

end SimpleGraph
