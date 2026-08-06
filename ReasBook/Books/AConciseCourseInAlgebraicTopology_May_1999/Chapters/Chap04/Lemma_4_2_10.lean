import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Definition_4_2_8
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Lemma_4_2_9

universe u

variable {V : Type u}

namespace SimpleGraph

-- Semantic recall via `lean_leansearch`: `SimpleGraph.Subgraph.IsSpanning`,
-- `SimpleGraph.Subgraph.isSpanning_iff`, and
-- `SimpleGraph.Connected.maximal_le_isAcyclic_iff_isTree` identify the canonical spanning-subgraph
-- surface for the textbook phrase "contains all vertices of `X`".

/-- Helper for Lemma 4.2.10: a spanning tree subgraph stays a tree after passing to
`spanningCoe`. -/
lemma Subgraph.isTree_spanningCoe_of_isSpanning {X : SimpleGraph V} {T : X.Subgraph}
    (hT : T.coe.IsTree) (hT_spanning : T.IsSpanning) : T.spanningCoe.IsTree := by
  -- Transport the tree structure across the spanning equivalence.
  simpa using (T.spanningCoeEquivCoeOfSpanning hT_spanning).isTree_iff.mpr hT

/-- Helper for Lemma 4.2.10: a tree simple graph below `X` becomes a tree subgraph of `X`. -/
lemma isTree_coe_toSubgraph {X F : SimpleGraph V} (hFX : F ≤ X) (hF : F.IsTree) :
    (SimpleGraph.toSubgraph F hFX).coe.IsTree := by
  have hF_spanning : (SimpleGraph.toSubgraph F hFX).IsSpanning :=
    SimpleGraph.toSubgraph.isSpanning F hFX
  have hF_spanningCoe : (SimpleGraph.toSubgraph F hFX).spanningCoe.IsTree := by
    -- `toSubgraph` is spanning, so its `spanningCoe` is definitionally the original graph `F`.
    simpa using hF
  -- Transport the tree structure back from the spanning ambient graph to the subgraph carrier.
  simpa using
    ((SimpleGraph.toSubgraph F hFX).spanningCoeEquivCoeOfSpanning hF_spanning).isTree_iff.mp
      hF_spanningCoe

/-- Helper for Lemma 4.2.10: a spanning subgraph is determined by its `spanningCoe`. -/
lemma Subgraph.eq_of_le_of_isSpanning_of_spanningCoe_eq {X : SimpleGraph V} {T U : X.Subgraph}
    (hTU : T ≤ U) (hT_spanning : T.IsSpanning) (hEq : T.spanningCoe = U.spanningCoe) : T = U := by
  have hU_spanning : U.IsSpanning := by
    intro v
    exact hTU.1 (hT_spanning v)
  -- Spanning identifies the vertex sets with `Set.univ`, so `spanningCoe` equality fixes the rest.
  refine Subgraph.ext (hT_spanning.verts_eq_univ.trans hU_spanning.verts_eq_univ.symm) ?_
  exact Subgraph.spanningCoe_inj.mp hEq

/-- Lemma 4.2.10. If `X` is connected, then a tree subgraph `T` of `X` is maximal if and only if
it is spanning, i.e. it contains all vertices of `X`. -/
theorem isMaximalSubtree_iff_isSpanning_of_isTree {X : SimpleGraph V} (hX : X.Connected)
    {T : X.Subgraph} (hT : T.coe.IsTree) :
    IsMaximalSubtree T ↔ T.IsSpanning := by
  constructor
  · intro hMax
    have hT_acyclic : T.spanningCoe.IsAcyclic := Subgraph.IsAcyclic.spanningCoe hT.isAcyclic
    -- Extend the ambient forest `T.spanningCoe` to a spanning tree of the connected graph `X`.
    obtain ⟨F, hTF, hFX, hF⟩ := hX.exists_isTree_le_of_le_of_isAcyclic T.spanningCoe_le hT_acyclic
    let U : X.Subgraph := SimpleGraph.toSubgraph F hFX
    have hTU : T ≤ U := by
      refine ⟨?_, ?_⟩
      · intro v hv
        simp [U, SimpleGraph.toSubgraph]
      · intro v w hvw
        simpa [U, SimpleGraph.toSubgraph] using hTF hvw
    have hU_tree : U.coe.IsTree := isTree_coe_toSubgraph hFX hF
    have hTU_eq : T = U := hMax.eq_of_le hTU hU_tree
    -- Maximality forces the extension to collapse back to `T`, hence `T` is spanning.
    rw [hTU_eq]
    simpa [U] using SimpleGraph.toSubgraph.isSpanning F hFX
  · intro hT_spanning
    have hT_spanningTree : T.spanningCoe.IsTree :=
      Subgraph.isTree_spanningCoe_of_isSpanning hT hT_spanning
    have hT_max :
        Maximal (fun H : SimpleGraph V ↦ H ≤ X ∧ H.IsAcyclic) T.spanningCoe :=
      (hX.maximal_le_isAcyclic_iff_isTree T.spanningCoe_le).2 hT_spanningTree
    rw [IsMaximalSubtree, maximal_iff]
    refine ⟨hT, ?_⟩
    intro U hU hTU
    have hU_spanning : U.IsSpanning := by
      intro v
      exact hTU.1 (hT_spanning v)
    have hU_spanningTree : U.spanningCoe.IsTree :=
      Subgraph.isTree_spanningCoe_of_isSpanning hU hU_spanning
    -- Compare `T` and `U` in the ambient simple-graph order, then pull equality back to subgraphs.
    have hEq_spanningCoe : T.spanningCoe = U.spanningCoe :=
      Maximal.eq_of_le hT_max ⟨U.spanningCoe_le, hU_spanningTree.isAcyclic⟩
        (Subgraph.spanningCoe_le_of_le hTU)
    exact Subgraph.eq_of_le_of_isSpanning_of_spanningCoe_eq hTU hT_spanning hEq_spanningCoe

namespace IsMaximalSubtree

/-- In a connected graph, a maximal subtree is spanning. -/
theorem isSpanning {X : SimpleGraph V} {T : X.Subgraph} (hT : IsMaximalSubtree T)
    (hX : X.Connected) : T.IsSpanning :=
  (isMaximalSubtree_iff_isSpanning_of_isTree hX hT.isTree).mp hT

/-- In a connected graph, a spanning tree subgraph is maximal. -/
theorem of_isSpanning {X : SimpleGraph V} (hX : X.Connected) {T : X.Subgraph}
    (hT : T.coe.IsTree) (hT_spanning : T.IsSpanning) :
    IsMaximalSubtree T :=
  (isMaximalSubtree_iff_isSpanning_of_isTree hX hT).mpr hT_spanning

end IsMaximalSubtree

end SimpleGraph
