module

public import Topology_Munkres_2000.Book.Remark_64_2.Incidence

public section

universe v

namespace SimpleGraph.LinearRealization

/-- Helper for Remark 64.2: edge-critical planarity produces either a plane embedding or an
internally disjoint path-system certificate for one of Kuratowski's two graphs. -/
lemma edgeCriticalIncidenceGraph_hasKuratowskiPathSystem
    {X : Type v} [TopologicalSpace X]
    (L : FiniteLinearGraph.{v, v} X) (s : Set L.Edge)
    (hproper : ∀ {t : Set L.Edge}, t ⊂ s →
      ∃ f : edgeUnion L t → ℝ × ℝ, Topology.IsEmbedding f) :
    (∃ f : edgeUnion L s → ℝ × ℝ, Topology.IsEmbedding f) ∨
      Nonempty (KuratowskiPathSystem (completeBipartiteGraph (Fin 3) (Fin 3))
        (selectedIncidenceGraph L s)) ∨
      Nonempty (KuratowskiPathSystem (SimpleGraph.completeGraph (Fin 5))
        (selectedIncidenceGraph L s)) := by
  -- Route correction: incidence and realization transport are now separate modules. The
  -- remaining proof must construct a deleted-ear bridge certificate, then use an unblocked
  -- side for a plane embedding or two conflicting sides for a Kuratowski path system.
  -- TODO: formalize the finite deleted-ear/cycle-bridge classification described above.
  sorry

end SimpleGraph.LinearRealization
