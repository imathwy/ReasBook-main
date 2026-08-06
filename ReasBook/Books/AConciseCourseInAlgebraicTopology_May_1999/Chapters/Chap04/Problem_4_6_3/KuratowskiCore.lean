import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Problem_4_6_3.Obstruction
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Problem_4_6_3.Monotonicity
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Problem_4_6_3.Planarity
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Definition_4_1_4

open scoped unitInterval

universe u

/-- Helper for Problem 4.6.3: a graph is free of realized Kuratowski obstructions exactly when
it contains neither a realized `K₅` nor a realized `K_{3,3}`. -/
def noRealizedKuratowskiObstruction
    {V : Type u} (graph : SimpleGraph V) : Prop :=
  ¬ graph.containsSubgraphRealizationHomeomorphicTo (SimpleGraph.completeGraph (Fin 5)) ∧
    ¬ graph.containsSubgraphRealizationHomeomorphicTo
      (completeBipartiteGraph (Fin 3) (Fin 3))

/-- Helper for Problem 4.6.3: the packaged obstruction-free predicate unfolds to the two concrete
realized-obstruction clauses appearing in the textbook statement. -/
theorem noRealizedKuratowskiObstruction_iff
    {V : Type u} (graph : SimpleGraph V) :
    noRealizedKuratowskiObstruction graph ↔
      ¬ graph.containsSubgraphRealizationHomeomorphicTo (SimpleGraph.completeGraph (Fin 5)) ∧
        ¬ graph.containsSubgraphRealizationHomeomorphicTo
          (completeBipartiteGraph (Fin 3) (Fin 3)) := by
  -- Unfold the packaged predicate before returning to the source-facing pair of clauses.
  rfl

/-- Helper for Problem 4.6.3: once the graph-theoretic owner theorem is stated using the packaged
obstruction-free predicate, the textbook-facing criterion follows by a single rewrite. -/
theorem canonicalKuratowskiCriterionCore_of_noRealizedKuratowskiObstruction
    {V : Type u} (graph : SimpleGraph V)
    (hOwner :
      embeddableInPlane (SimpleGraph.realizationBoundary graph) ↔
        noRealizedKuratowskiObstruction graph) :
    embeddableInPlane (SimpleGraph.realizationBoundary graph) ↔
      ¬ graph.containsSubgraphRealizationHomeomorphicTo (SimpleGraph.completeGraph (Fin 5)) ∧
        ¬ graph.containsSubgraphRealizationHomeomorphicTo
          (completeBipartiteGraph (Fin 3) (Fin 3)) := by
  -- Rewrite the packaged obstruction-free predicate back to the two explicit obstruction clauses.
  simpa [noRealizedKuratowskiObstruction] using hOwner

/-- Helper for Problem 4.6.3: the canonical owner theorem is exactly the pair of graph-theoretic
implications between plane embeddability of the canonical realization and the packaged absence of
realized Kuratowski obstructions. -/
theorem planarRealizationBoundary_iff_of_directions
    {V : Type u} (graph : SimpleGraph V)
    [FiniteGraph (SimpleGraph.realizationBoundary graph)]
    (hDirections :
      (embeddableInPlane (SimpleGraph.realizationBoundary graph) →
          noRealizedKuratowskiObstruction graph) ∧
        (noRealizedKuratowskiObstruction graph →
          embeddableInPlane (SimpleGraph.realizationBoundary graph))) :
    embeddableInPlane (SimpleGraph.realizationBoundary graph) ↔
      noRealizedKuratowskiObstruction graph := by
  -- Unpack the two graph-theoretic directions and reassemble them as the owner equivalence.
  rcases hDirections with ⟨hForward, hBackward⟩
  constructor
  · -- Plane embeddability rules out the packaged realized obstructions.
    exact hForward
  · -- Conversely, obstruction-freeness should recover a plane embedding.
    exact hBackward

/-- Helper for Problem 4.6.3: once the two base obstruction realizations and the converse
graph-theoretic implication are supplied, the owner equivalence is immediate. -/
theorem planarRealizationBoundary_iff_noRealizedKuratowskiObstruction_of_prerequisites
    {V : Type u} (graph : SimpleGraph V)
    [FiniteGraph (SimpleGraph.realizationBoundary graph)]
    (hK5 :
      ¬ embeddableInPlane
        (SimpleGraph.realizationBoundary (SimpleGraph.completeGraph (Fin 5))))
    (hK33 :
      ¬ embeddableInPlane
        (SimpleGraph.realizationBoundary (completeBipartiteGraph (Fin 3) (Fin 3))))
    (hBackward :
      noRealizedKuratowskiObstruction graph →
        embeddableInPlane (SimpleGraph.realizationBoundary graph)) :
    embeddableInPlane (SimpleGraph.realizationBoundary graph) ↔
      noRealizedKuratowskiObstruction graph := by
  -- Route correction: after extracting the shared realization monotonicity API, the owner theorem
  -- now reduces to the two fixed obstruction facts and the canonical converse implication.
  -- First isolate the forward implication as the reusable monotonicity consequence of the two
  -- fixed non-embeddable obstructions.
  have hForward :
      embeddableInPlane (SimpleGraph.realizationBoundary graph) →
        noRealizedKuratowskiObstruction graph := by
    intro hEmb
    -- Specialize the generic obstruction-monotonicity theorem to the two classical obstructions.
    let _ : Finite (Fin 5) := Finite.of_fintype (Fin 5)
    let _ : Finite (Fin 3 ⊕ Fin 3) := Finite.of_fintype (Fin 3 ⊕ Fin 3)
    let _ : FiniteGraph (SimpleGraph.realizationBoundary (SimpleGraph.completeGraph (Fin 5))) :=
      finiteGraph_realizationBoundary_ofFinite (SimpleGraph.completeGraph (Fin 5))
    let _ :
        FiniteGraph
          (SimpleGraph.realizationBoundary (completeBipartiteGraph (Fin 3) (Fin 3))) :=
      finiteGraph_realizationBoundary_ofFinite (completeBipartiteGraph (Fin 3) (Fin 3))
    simpa [noRealizedKuratowskiObstruction] using
      noKuratowskiObstruction_of_embeddableInPlane_of_nonembeddableObstructions
        graph hEmb hK5 hK33
  -- Then package that forward direction with the supplied converse implication.
  exact planarRealizationBoundary_iff_of_directions graph ⟨hForward, hBackward⟩

/-- Helper for Problem 4.6.3: once the two fixed obstruction realizations are known to be
non-embeddable, the forward implication to packaged obstruction-freeness is just the generic
obstruction monotonicity theorem specialized to `K₅` and `K_{3,3}`. -/
theorem noRealizedKuratowskiObstruction_of_embeddableInPlane_of_prerequisites
    {V : Type u} (graph : SimpleGraph V)
    [FiniteGraph (SimpleGraph.realizationBoundary graph)]
    (hK5 :
      ¬ embeddableInPlane
        (SimpleGraph.realizationBoundary (SimpleGraph.completeGraph (Fin 5))))
    (hK33 :
      ¬ embeddableInPlane
        (SimpleGraph.realizationBoundary (completeBipartiteGraph (Fin 3) (Fin 3))))
    (hEmb : embeddableInPlane (SimpleGraph.realizationBoundary graph)) :
    noRealizedKuratowskiObstruction graph := by
  -- Reuse the prerequisite assembly's forward half without reopening any downstream owner theorem.
  let _ : Finite (Fin 5) := Finite.of_fintype (Fin 5)
  let _ : Finite (Fin 3 ⊕ Fin 3) := Finite.of_fintype (Fin 3 ⊕ Fin 3)
  let _ : FiniteGraph (SimpleGraph.realizationBoundary (SimpleGraph.completeGraph (Fin 5))) :=
    finiteGraph_realizationBoundary_ofFinite (SimpleGraph.completeGraph (Fin 5))
  let _ :
      FiniteGraph (SimpleGraph.realizationBoundary (completeBipartiteGraph (Fin 3) (Fin 3))) :=
    finiteGraph_realizationBoundary_ofFinite (completeBipartiteGraph (Fin 3) (Fin 3))
  -- Apply monotonicity directly to the two canonical Kuratowski obstructions.
  simpa [noRealizedKuratowskiObstruction] using
    noKuratowskiObstruction_of_embeddableInPlane_of_nonembeddableObstructions
      graph hEmb hK5 hK33

/-- Helper for Problem 4.6.3: once the two fixed obstruction realizations and the converse
implication are available, the textbook-facing explicit `K₅`/`K_{3,3}` criterion is a rewrite of
the packaged owner theorem. -/
theorem canonicalKuratowskiCriterionCore_of_prerequisites
    {V : Type u} (graph : SimpleGraph V)
    [FiniteGraph (SimpleGraph.realizationBoundary graph)]
    (hK5 :
      ¬ embeddableInPlane
        (SimpleGraph.realizationBoundary (SimpleGraph.completeGraph (Fin 5))))
    (hK33 :
      ¬ embeddableInPlane
        (SimpleGraph.realizationBoundary (completeBipartiteGraph (Fin 3) (Fin 3))))
    (hBackward :
      noRealizedKuratowskiObstruction graph →
        embeddableInPlane (SimpleGraph.realizationBoundary graph)) :
    embeddableInPlane (SimpleGraph.realizationBoundary graph) ↔
      ¬ graph.containsSubgraphRealizationHomeomorphicTo (SimpleGraph.completeGraph (Fin 5)) ∧
        ¬ graph.containsSubgraphRealizationHomeomorphicTo
          (completeBipartiteGraph (Fin 3) (Fin 3)) := by
  -- First assemble the packaged owner theorem from the three genuine graph-theoretic inputs.
  have hOwner :
      embeddableInPlane (SimpleGraph.realizationBoundary graph) ↔
        noRealizedKuratowskiObstruction graph :=
    planarRealizationBoundary_iff_noRealizedKuratowskiObstruction_of_prerequisites
      graph hK5 hK33 hBackward
  -- Then rewrite the packaged predicate to the explicit obstruction pair from the statement.
  exact
    canonicalKuratowskiCriterionCore_of_noRealizedKuratowskiObstruction
      graph hOwner

/-- Helper for Problem 4.6.3: the remaining owner theorem is the finite canonical Kuratowski
criterion stated directly on `SimpleGraph.realizationBoundary`. -/
theorem canonicalKuratowskiCriterionCore
    {V : Type u} (graph : SimpleGraph V)
    [FiniteGraph (SimpleGraph.realizationBoundary graph)] :
    embeddableInPlane (SimpleGraph.realizationBoundary graph) ↔
      ¬ graph.containsSubgraphRealizationHomeomorphicTo (SimpleGraph.completeGraph (Fin 5)) ∧
        ¬ graph.containsSubgraphRealizationHomeomorphicTo
          (completeBipartiteGraph (Fin 3) (Fin 3)) := by
  -- Route correction: the executable assembly route is now isolated in
  -- `canonicalKuratowskiCriterionCore_of_prerequisites`.
  -- TODO: replace the three cyclic support projections by independent proofs of
  -- `KuratowskiCoreSupport.completeGraphFiveBoundary_notEmbeddableInPlane`,
  -- `KuratowskiCoreSupport.completeBipartiteGraphThreeThreeBoundary_notEmbeddableInPlane`, and
  -- `KuratowskiCoreSupport
  --   .embeddableInPlane_realizationBoundary_of_noRealizedKuratowskiObstruction`.
  -- Then apply `canonicalKuratowskiCriterionCore_of_prerequisites`.
  sorry

-- Helper namespace for Problem 4.6.3: these support-owned graph-theoretic frontiers are kept
-- separate from the wrapper file so the canonical owner theorem no longer depends on wrapper-local
-- aliases.
namespace KuratowskiCoreSupport

/-- Helper for Problem 4.6.3: any realized `K₅` obstruction contradicts the packaged
obstruction-free predicate immediately through its first component. -/
theorem not_noRealizedKuratowskiObstruction_of_containsCompleteGraphFive
    {V : Type u} {graph : SimpleGraph V}
    (hContains :
      graph.containsSubgraphRealizationHomeomorphicTo (SimpleGraph.completeGraph (Fin 5))) :
    ¬ noRealizedKuratowskiObstruction graph := by
  -- Unpack the packaged predicate and close the contradiction with its `K₅` exclusion field.
  intro hNo
  exact hNo.1 hContains

/-- Helper for Problem 4.6.3: any realized `K_{3,3}` obstruction likewise contradicts the
packaged obstruction-free predicate through its second component. -/
theorem not_noRealizedKuratowskiObstruction_of_containsCompleteBipartiteGraphThreeThree
    {V : Type u} {graph : SimpleGraph V}
    (hContains :
      graph.containsSubgraphRealizationHomeomorphicTo
        (completeBipartiteGraph (Fin 3) (Fin 3))) :
    ¬ noRealizedKuratowskiObstruction graph := by
  -- Unpack the packaged predicate and close the contradiction with its `K_{3,3}` exclusion field.
  intro hNo
  exact hNo.2 hContains

/-- Helper for Problem 4.6.3: the canonical realization of `K₅` is not itself obstruction-free,
because the top subgraph realizes the forbidden `K₅` witness. -/
theorem completeGraphFive_not_noRealizedKuratowskiObstruction :
    ¬ noRealizedKuratowskiObstruction (SimpleGraph.completeGraph (Fin 5)) := by
  -- Specialize the generic contradiction helper to the self-obstruction witness of `K₅`.
  exact
    not_noRealizedKuratowskiObstruction_of_containsCompleteGraphFive
      completeGraphFive_containsSelfObstruction

/-- Helper for Problem 4.6.3: the canonical realization of `K_{3,3}` is also not obstruction-free,
because the top subgraph realizes the forbidden `K_{3,3}` witness. -/
theorem completeBipartiteGraphThreeThree_not_noRealizedKuratowskiObstruction :
    ¬ noRealizedKuratowskiObstruction (completeBipartiteGraph (Fin 3) (Fin 3)) := by
  -- Again specialize the generic contradiction helper to the canonical self-obstruction witness.
  exact
    not_noRealizedKuratowskiObstruction_of_containsCompleteBipartiteGraphThreeThree
      completeBipartiteGraphThreeThree_containsSelfObstruction

/-- Helper for Problem 4.6.3: once the owner-independent forward implication is available, the
canonical `K₅` realization is non-embeddable by contradicting its self-obstruction. -/
theorem completeGraphFiveBoundary_notEmbeddableInPlane_of_forward
    (hForward :
      embeddableInPlane
          (SimpleGraph.realizationBoundary (SimpleGraph.completeGraph (Fin 5))) →
        noRealizedKuratowskiObstruction (SimpleGraph.completeGraph (Fin 5))) :
    ¬ embeddableInPlane
      (SimpleGraph.realizationBoundary (SimpleGraph.completeGraph (Fin 5))) := by
  intro hEmb
  -- Feed the plane embedding into the forward implication and contradict the explicit `K₅`
  -- self-obstruction packaged above.
  exact completeGraphFive_not_noRealizedKuratowskiObstruction (hForward hEmb)

/-- Helper for Problem 4.6.3: the same owner-independent forward implication also turns the
canonical `K_{3,3}` self-obstruction into non-embeddability. -/
theorem completeBipartiteGraphThreeThreeBoundary_notEmbeddableInPlane_of_forward
    (hForward :
      embeddableInPlane
          (SimpleGraph.realizationBoundary (completeBipartiteGraph (Fin 3) (Fin 3))) →
        noRealizedKuratowskiObstruction (completeBipartiteGraph (Fin 3) (Fin 3))) :
    ¬ embeddableInPlane
      (SimpleGraph.realizationBoundary (completeBipartiteGraph (Fin 3) (Fin 3))) := by
  intro hEmb
  -- The explicit `K_{3,3}` self-obstruction closes the contradiction once the forward direction
  -- is isolated as a reusable hypothesis.
  exact completeBipartiteGraphThreeThree_not_noRealizedKuratowskiObstruction (hForward hEmb)

/-- Helper for Problem 4.6.3: both fixed obstruction proofs use the same missing owner-independent
forward implication from plane embeddability to packaged obstruction-freeness. -/
theorem noRealizedKuratowskiObstruction_of_embeddableInPlane
    {V : Type u} (graph : SimpleGraph V)
    [FiniteGraph (SimpleGraph.realizationBoundary graph)] :
    embeddableInPlane (SimpleGraph.realizationBoundary graph) →
      noRealizedKuratowskiObstruction graph := by
  -- Route correction: the forward implication is no longer treated as an independent owner input.
  intro hEmb
  -- Read the packaged forward implication directly from the explicit core criterion.
  simpa [noRealizedKuratowskiObstruction] using
    (canonicalKuratowskiCriterionCore (graph := graph)).1 hEmb

/-- Helper for Problem 4.6.3: the canonical realization of `K₅` should be treated as a support-owned
base obstruction, not reproved through the owner criterion that depends on it. -/
theorem completeGraphFiveBoundary_notEmbeddableInPlane :
    ¬ embeddableInPlane
      (SimpleGraph.realizationBoundary (SimpleGraph.completeGraph (Fin 5))) := by
  -- Route correction: the duplicated `K₅` contradiction is now delegated to the shared forward
  -- implication frontier rather than repeated locally.
  let _ : Finite (Fin 5) := Finite.of_fintype (Fin 5)
  let _ : FiniteGraph (SimpleGraph.realizationBoundary (SimpleGraph.completeGraph (Fin 5))) :=
    finiteGraph_realizationBoundary_ofFinite (SimpleGraph.completeGraph (Fin 5))
  exact
    completeGraphFiveBoundary_notEmbeddableInPlane_of_forward
      (noRealizedKuratowskiObstruction_of_embeddableInPlane
        (graph := SimpleGraph.completeGraph (Fin 5)))

/-- Helper for Problem 4.6.3: the canonical realization of `K_{3,3}` is the second fixed
support-owned base obstruction needed by the owner theorem. -/
theorem completeBipartiteGraphThreeThreeBoundary_notEmbeddableInPlane :
    ¬ embeddableInPlane
      (SimpleGraph.realizationBoundary (completeBipartiteGraph (Fin 3) (Fin 3))) := by
  -- Route correction: the duplicated `K_{3,3}` contradiction now factors through the same shared
  -- forward theorem, leaving a single support-owned frontier.
  let _ : Finite (Fin 3 ⊕ Fin 3) := Finite.of_fintype (Fin 3 ⊕ Fin 3)
  let _ :
      FiniteGraph (SimpleGraph.realizationBoundary (completeBipartiteGraph (Fin 3) (Fin 3))) :=
    finiteGraph_realizationBoundary_ofFinite (completeBipartiteGraph (Fin 3) (Fin 3))
  exact
    completeBipartiteGraphThreeThreeBoundary_notEmbeddableInPlane_of_forward
      (noRealizedKuratowskiObstruction_of_embeddableInPlane
        (graph := completeBipartiteGraph (Fin 3) (Fin 3)))

/-- Helper for Problem 4.6.3: once the two fixed support-owned base obstructions are isolated, the
owner theorem should consume them as a single prerequisite package. -/
theorem kuratowskiBaseObstructions_notEmbeddableInPlane :
    (¬ embeddableInPlane
        (SimpleGraph.realizationBoundary (SimpleGraph.completeGraph (Fin 5)))) ∧
      (¬ embeddableInPlane
        (SimpleGraph.realizationBoundary (completeBipartiteGraph (Fin 3) (Fin 3)))) := by
  -- Package the two fixed obstruction facts once so the owner assembly stays flat.
  exact ⟨completeGraphFiveBoundary_notEmbeddableInPlane,
    completeBipartiteGraphThreeThreeBoundary_notEmbeddableInPlane⟩

/-- Helper for Problem 4.6.3: after the fixed obstructions are split off, the only remaining deep
frontier is the canonical converse from packaged obstruction-freeness to plane embeddability. -/
theorem embeddableInPlane_realizationBoundary_of_noRealizedKuratowskiObstruction
    {V : Type u} (graph : SimpleGraph V)
    [FiniteGraph (SimpleGraph.realizationBoundary graph)]
    (hNo : noRealizedKuratowskiObstruction graph) :
    embeddableInPlane (SimpleGraph.realizationBoundary graph) := by
  -- Route correction: the converse is also a projection from the explicit core criterion.
  simpa [noRealizedKuratowskiObstruction] using
    (canonicalKuratowskiCriterionCore (graph := graph)).2 hNo

end KuratowskiCoreSupport

/-- Helper for Problem 4.6.3: the remaining owner theorem should characterize planarity of the
canonical realization boundary by the packaged absence of realized Kuratowski obstructions. -/
theorem planarRealizationBoundary_iff_noRealizedKuratowskiObstruction
    {V : Type u} (graph : SimpleGraph V)
    [FiniteGraph (SimpleGraph.realizationBoundary graph)] :
    embeddableInPlane (SimpleGraph.realizationBoundary graph) ↔
      noRealizedKuratowskiObstruction graph := by
  -- Route correction: the packaged owner theorem is now only the rewrite view of the explicit
  -- `K₅`/`K_{3,3}` core criterion.
  simpa [noRealizedKuratowskiObstruction] using
    (canonicalKuratowskiCriterionCore (graph := graph))
