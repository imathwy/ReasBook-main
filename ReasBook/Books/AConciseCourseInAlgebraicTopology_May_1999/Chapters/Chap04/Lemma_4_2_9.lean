import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Definition_4_2_8

universe u

variable {V : Type u}

namespace SimpleGraph

-- Semantic recall via mathlib's connectivity and acyclicity API: a maximal subtree containing `T`
-- is obtained by extending `T` inside the connected component of `X` determined by `T`, then
-- viewing a spanning tree of that component as a maximal tree subgraph of `X`.

/-- Helper for Lemma 4.2.9: adding isolated vertices via `spanningCoe` preserves acyclicity of a
subgraph. -/
lemma Subgraph.IsAcyclic.spanningCoe {X : SimpleGraph V} {H : X.Subgraph}
    (hH : H.coe.IsAcyclic) : H.spanningCoe.IsAcyclic := by
  intro u p hp
  have hpn : ¬ p.Nil := hp.not_nil
  have hsupp : ∀ x ∈ p.support, x ∈ H.verts := by
    intro x hx
    -- Every vertex on the cycle is incident to one of its edges, hence lies in `H.verts`.
    rw [Walk.mem_support_iff_exists_mem_edges_of_not_nil hpn] at hx
    rcases hx with ⟨e, he, hx⟩
    rcases Sym2.mem_iff_exists.mp hx with ⟨y, rfl⟩
    have hadj : H.coe.spanningCoe.Adj x y := by
      simpa [Subgraph.spanningCoe_coe] using
        (p.toSubgraph.adj_sub <| (p.adj_toSubgraph_iff_mem_edges).2 he)
    exact Subgraph.mem_of_adj_spanningCoe H.coe hadj
  let q := p.induce H.verts hsupp
  have hqmap : q.map (Embedding.induce H.verts).toHom = p := by
    simp [q]
  let f : (H.spanningCoe.induce H.verts) →g H.spanningCoe := (Embedding.induce H.verts).toHom
  have hfinj : Function.Injective f := by
    intro a b hab
    exact Subtype.ext hab
  have hqcycle : q.IsCycle := by
    -- Inducing the cycle to `H.verts` recovers a genuine cycle in `H.coe`.
    refine (Walk.map_isCycle_iff_of_injective (p := q) (f := f) hfinj).1 ?_
    simpa [f, hqmap] using hp
  exact hH _ (by simpa [q, Subgraph.spanningCoe_coe] using hqcycle)

/-- Helper for Lemma 4.2.9: a nonempty directed supremum of connected subgraphs is connected. -/
lemma connectedCoe_sSup_of_nonempty_of_directedOn {X : SimpleGraph V} {c : Set X.Subgraph}
    (hcne : c.Nonempty) (hdir : DirectedOn (· ≤ ·) c)
    (hconn : ∀ H ∈ c, H.coe.Connected) :
    (sSup c).coe.Connected := by
  have hSup : (sSup c).Connected := by
    rw [Subgraph.connected_iff_forall_exists_walk_subgraph]
    constructor
    · obtain ⟨H, hH⟩ := hcne
      have hHconn : H.Connected := ⟨hconn H hH⟩
      obtain ⟨v, hv⟩ := hHconn.nonempty
      exact ⟨v, by
        rw [Subgraph.verts_sSup]
        exact Set.mem_iUnion.2 ⟨H, Set.mem_iUnion.2 ⟨hH, hv⟩⟩⟩
    · intro u v hu hv
      -- Move both endpoints into one chain member, then reuse its connecting walk.
      simp only [Subgraph.verts_sSup, Set.mem_iUnion, exists_prop] at hu hv
      rcases hu with ⟨Hu, hHu, hu⟩
      rcases hv with ⟨Hv, hHv, hv⟩
      rcases hdir Hu hHu Hv hHv with ⟨H, hH, hHuH, hHvH⟩
      have hHconn : H.Connected := ⟨hconn H hH⟩
      obtain ⟨p, hp⟩ := (Subgraph.connected_iff_forall_exists_walk_subgraph H).1 hHconn |>.2
        (hHuH.1 hu) (hHvH.1 hv)
      exact ⟨p, hp.trans (le_sSup hH)⟩
  exact hSup.coe

/-- Helper for Lemma 4.2.9: a directed supremum of acyclic subgraphs is acyclic. -/
lemma isAcyclicCoe_sSup_of_directedOn {X : SimpleGraph V} {c : Set X.Subgraph}
    (hdir : DirectedOn (· ≤ ·) c) (hacyc : ∀ H ∈ c, H.coe.IsAcyclic) :
    (sSup c).coe.IsAcyclic := by
  have hdir' : DirectedOn (· ≤ ·) (Subgraph.spanningCoe '' c) := by
    intro A hA B hB
    rcases hA with ⟨HA, hHA, rfl⟩
    rcases hB with ⟨HB, hHB, rfl⟩
    rcases hdir HA hHA HB hHB with ⟨K, hK, hHAK, hHBK⟩
    exact ⟨K.spanningCoe, ⟨K, hK, rfl⟩,
      Subgraph.spanningCoe_le_of_le hHAK, Subgraph.spanningCoe_le_of_le hHBK⟩
  have hsSup : sSup (Subgraph.spanningCoe '' c) = (sSup c).spanningCoe := by
    -- On edges, the supremum of `spanningCoe` graphs is exactly the ambient supremum subgraph.
    ext u v
    constructor
    · intro huv
      rcases (SimpleGraph.sSup_adj).1 huv with ⟨G, hG, huvG⟩
      rcases hG with ⟨H, hH, rfl⟩
      exact (Subgraph.sSup_adj).2 ⟨H, hH, huvG⟩
    · intro huv
      rcases (Subgraph.sSup_adj).1 huv with ⟨H, hH, huvH⟩
      exact (SimpleGraph.sSup_adj).2 ⟨H.spanningCoe, ⟨H, hH, rfl⟩, huvH⟩
  have hsp : (sSup c).spanningCoe.IsAcyclic := by
    -- Reduce to mathlib's directed-sup acyclicity theorem on simple graphs.
    rw [← hsSup]
    exact SimpleGraph.isAcyclic_sSup_of_isAcyclic_directedOn (Subgraph.spanningCoe '' c)
      (by
        intro G hG
        rcases hG with ⟨H, hH, rfl⟩
        exact Subgraph.IsAcyclic.spanningCoe (hacyc H hH))
      hdir'
  exact hsp.embedding ((sSup c).coeEmbeddingSpanningCoe)

/-- Helper for Lemma 4.2.9: a nonempty directed supremum of tree subgraphs is a tree. -/
lemma isTreeCoe_sSup_of_nonempty_of_directedOn {X : SimpleGraph V} {c : Set X.Subgraph}
    (hcne : c.Nonempty) (hdir : DirectedOn (· ≤ ·) c)
    (htree : ∀ H ∈ c, H.coe.IsTree) :
    (sSup c).coe.IsTree := by
  -- A tree is exactly a connected acyclic graph, so combine the two structural lemmas above.
  refine ⟨?_, ?_⟩
  · exact connectedCoe_sSup_of_nonempty_of_directedOn hcne hdir
      (fun H hH => (htree H hH).connected)
  · exact isAcyclicCoe_sSup_of_directedOn hdir
      (fun H hH => (htree H hH).isAcyclic)

/-- Lemma 4.2.9. Every tree subgraph `T` of a graph `X` is contained in a maximal subtree of `X`.
-/
theorem exists_isMaximalSubtree_of_isTree {X : SimpleGraph V} {T : X.Subgraph}
    (hT : T.coe.IsTree) :
    ∃ U : X.Subgraph, T ≤ U ∧ IsMaximalSubtree U := by
  classical
  let S : Set X.Subgraph := {U | T ≤ U ∧ U.coe.IsTree}
  obtain ⟨U, hTU, hUmax⟩ := zorn_le_nonempty₀ S
    (fun c hcS hc y hy => by
      -- The directed supremum stays in `S`, so it serves as the Zorn upper bound.
      refine ⟨sSup c, ?_, fun z hz => le_sSup hz⟩
      constructor
      · exact (hcS hy).1.trans (le_sSup hy)
      · exact isTreeCoe_sSup_of_nonempty_of_directedOn ⟨y, hy⟩ hc.directedOn
          (fun H hH => (hcS hH).2))
    T ⟨le_rfl, hT⟩
  refine ⟨U, hTU, ?_⟩
  refine ⟨hUmax.prop.2, ?_⟩
  intro W hW hUW
  -- Any larger tree still lies in the Zorn set because it contains `T`.
  exact hUmax.2 ⟨hTU.trans hUW, hW⟩ hUW

end SimpleGraph
