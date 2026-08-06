import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Lemma_4_2_10

universe u

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

/-- Principle 4.3.1. If `T` is a maximal subtree of a connected graph `G`, then the spanning
graph determined by `T` has the same reachability relation as `G`. Equivalently, maximal
subtrees of connected graphs are spanning trees. -/
theorem Connected.reachable_eq_of_isMaximalSubtree (hG : G.Connected) {T : G.Subgraph}
    (hT : IsMaximalSubtree T) :
    T.spanningCoe.Reachable = G.Reachable := by
  have hT_tree : T.coe.IsTree := hT.isTree
  have hT_spanning : T.IsSpanning := hT.isSpanning hG
  have hT_spanningTree : T.spanningCoe.IsTree :=
    (T.spanningCoeEquivCoeOfSpanning hT_spanning).isTree_iff.mpr hT_tree
  exact G.reachable_eq_of_maximal_isAcyclic T.spanningCoe
    ((hG.maximal_le_isAcyclic_iff_isTree T.spanningCoe_le).2 hT_spanningTree)

/-- Principle 4.3.1. Every connected graph has a maximal subtree; the finite connected case is a
special case of this connected-graph statement. -/
theorem Connected.exists_isMaximalSubtree (hG : G.Connected) :
    ∃ T : G.Subgraph, T.IsSpanning ∧ IsMaximalSubtree T := by
  obtain ⟨T, hT_le, hT_tree⟩ := hG.exists_isTree_le
  let T' : G.Subgraph := SimpleGraph.toSubgraph T hT_le
  have hT'_spanning : T'.IsSpanning := SimpleGraph.toSubgraph.isSpanning T hT_le
  have hT'_spanningTree : T'.spanningCoe.IsTree := by
    simpa [T'] using hT_tree
  have hT'_tree : T'.coe.IsTree :=
    (T'.spanningCoeEquivCoeOfSpanning hT'_spanning).isTree_iff.mp hT'_spanningTree
  exact ⟨T', hT'_spanning, IsMaximalSubtree.of_isSpanning hG hT'_tree hT'_spanning⟩

end SimpleGraph
