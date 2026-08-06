import Mathlib.Combinatorics.SimpleGraph.Subgraph

universe u

-- Semantic recall: the canonical mathlib owner for subgraphs of `X` is the type expression
-- `X.Subgraph`, and `SimpleGraph.toSubgraph` is the canonical bridge from an inclusion `A ≤ X`.

section

variable {V : Type u} (X A : SimpleGraph V) (h : A ≤ X)

/- Definition 4.1.6. A subgraph of a graph `X` is formalized by `X.Subgraph`
(equivalently `SimpleGraph.Subgraph X`). It records a set of vertices together with an adjacency
relation contained in `X`, so it is exactly the choice of some vertices and some edges of `X`.
When a graph `A` on the same vertex type satisfies `A ≤ X`, the canonical bridge
`SimpleGraph.toSubgraph A h : X.Subgraph` keeps the edge relation of `A` and regards it as a
spanning subgraph of `X`. -/
#check X.Subgraph
#check SimpleGraph.toSubgraph A h
#check SimpleGraph.toSubgraph.isSpanning A h

end
