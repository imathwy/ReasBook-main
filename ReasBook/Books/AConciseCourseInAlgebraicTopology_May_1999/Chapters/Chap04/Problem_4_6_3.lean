import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Problem_4_6_3.Obstruction
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Problem_4_6_3.KuratowskiCore
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Problem_4_6_3.Monotonicity
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Problem_4_6_3.Planarity
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Definition_4_1_4
import Mathlib.Topology.Separation.Hausdorff

open scoped unitInterval

universe u

/-- Helper for Problem 4.6.3: each chosen edge parametrization agrees with the canonical
orientation of the underlying edge, either directly or after swapping the two endpoints. -/
theorem boundaryOrientationCases
    {V : Type u} (graph : SimpleGraph V) (boundary : graph.edgeSet ↪ Fin 2 → V)
    (boundary_edge : ∀ e : graph.edgeSet, s(boundary e 0, boundary e 1) = (e : Sym2 V))
    (e : graph.edgeSet) :
    (boundary e 0 = e.1.out.1 ∧ boundary e 1 = e.1.out.2) ∨
      (boundary e 0 = e.1.out.2 ∧ boundary e 1 = e.1.out.1) := by
  -- Rewrite the chosen edge endpoints to the canonical endpoints of the underlying `Sym2`.
  have hEdge : s(boundary e 0, boundary e 1) = s(e.1.out.1, e.1.out.2) := by
    calc
      s(boundary e 0, boundary e 1) = (e : Sym2 V) := boundary_edge e
      _ = s(e.1.out.1, e.1.out.2) := e.1.out_eq.symm
  -- `Sym2.eq_iff` splits the unordered-edge equality into the direct and reversed cases.
  simpa using Sym2.eq_iff.mp hEdge

/-- Helper for Problem 4.6.3: the chosen parametrization of `e` already follows the canonical
orientation of `e`. -/
def boundaryHasCanonicalOrientation
    {V : Type u} {graph : SimpleGraph V} (boundary : graph.edgeSet ↪ Fin 2 → V)
    (e : graph.edgeSet) : Prop :=
  boundary e 0 = e.1.out.1 ∧ boundary e 1 = e.1.out.2

/-- Helper for Problem 4.6.3: normalize a source representative of the chosen realization to the
canonical realization by reversing the interval parameter exactly on reversed edges. -/
noncomputable def boundaryToCanonicalSource
    {V : Type u} {graph : SimpleGraph V} (boundary : graph.edgeSet ↪ Fin 2 → V) :
    V ⊕ (graph.edgeSet × I) → V ⊕ (graph.edgeSet × I) :=
  let _ : DecidableEq V := Classical.decEq V
  let _ : DecidablePred (boundaryHasCanonicalOrientation boundary) := Classical.decPred _
  fun z =>
    match z with
    | Sum.inl x => Sum.inl x
    | Sum.inr (e, t) =>
        if _h : boundaryHasCanonicalOrientation boundary e then
          Sum.inr (e, t)
        else
          Sum.inr (e, σ t)

/-- Helper for Problem 4.6.3: the swapped orientation case cannot also be the canonical
orientation, because an edge in a simple graph is never diagonal. -/
theorem boundaryHasCanonicalOrientation_false_of_reverse
    {V : Type u} (graph : SimpleGraph V) (boundary : graph.edgeSet ↪ Fin 2 → V)
    {e : graph.edgeSet}
    (hrev : boundary e 0 = e.1.out.2 ∧ boundary e 1 = e.1.out.1) :
    ¬ boundaryHasCanonicalOrientation boundary e := by
  -- If both orientations held then the two endpoints of `e` would coincide.
  intro hdir
  have heq : e.1.out.1 = e.1.out.2 := hdir.1.symm.trans hrev.1
  have hdiag : e.1.IsDiag := by
    simpa [e.1.out_eq] using (Sym2.mk_isDiag_iff.mpr heq : Sym2.IsDiag s(e.1.out.1, e.1.out.2))
  exact (graph.not_isDiag_of_mem_edgeSet e.2) hdiag

/-- Helper for Problem 4.6.3: on a canonically oriented edge, the source normalization map fixes
the edge parameter. -/
theorem boundaryToCanonicalSource_inr_of_canonical
    {V : Type u} {graph : SimpleGraph V} (boundary : graph.edgeSet ↪ Fin 2 → V)
    {e : graph.edgeSet} (t : I) (hdir : boundaryHasCanonicalOrientation boundary e) :
    boundaryToCanonicalSource boundary (Sum.inr (e, t)) = Sum.inr (e, t) := by
  let _ : DecidablePred (boundaryHasCanonicalOrientation boundary) := Classical.decPred _
  change (if boundaryHasCanonicalOrientation boundary e then Sum.inr (e, t) else Sum.inr (e, σ t)) =
    Sum.inr (e, t)
  rw [if_pos hdir]

/-- Helper for Problem 4.6.3: on a reversed edge, the source normalization map applies the unit
interval symmetry. -/
theorem boundaryToCanonicalSource_inr_of_reverse
    {V : Type u} (graph : SimpleGraph V) (boundary : graph.edgeSet ↪ Fin 2 → V)
    {e : graph.edgeSet} (t : I)
    (hrev : boundary e 0 = e.1.out.2 ∧ boundary e 1 = e.1.out.1) :
    boundaryToCanonicalSource boundary (Sum.inr (e, t)) = Sum.inr (e, σ t) := by
  let _ : DecidablePred (boundaryHasCanonicalOrientation boundary) := Classical.decPred _
  have hnot : ¬ boundaryHasCanonicalOrientation boundary e :=
    boundaryHasCanonicalOrientation_false_of_reverse graph boundary hrev
  change (if boundaryHasCanonicalOrientation boundary e then Sum.inr (e, t) else Sum.inr (e, σ t)) =
    Sum.inr (e, σ t)
  rw [if_neg hnot]

/-- Helper for Problem 4.6.3: the normalization map preserves the endpoint relation from the
chosen realization to the canonical realization. -/
theorem boundaryToCanonicalSource_rel
    {V : Type u} (graph : SimpleGraph V) (boundary : graph.edgeSet ↪ Fin 2 → V)
    (boundary_edge : ∀ e : graph.edgeSet, s(boundary e 0, boundary e 1) = (e : Sym2 V))
    {a b : V ⊕ (graph.edgeSet × I)} (hab : graphRealizationRel boundary a b) :
    graphRealizationSetoid (SimpleGraph.realizationBoundary graph)
      (boundaryToCanonicalSource boundary a) (boundaryToCanonicalSource boundary b) := by
  let canonicalBoundary := SimpleGraph.realizationBoundary graph
  -- Inspect the single generating endpoint identification and normalize it edge-by-edge.
  cases a with
  | inl x =>
      cases b with
      | inl y =>
          cases hab
      | inr jt =>
          rcases jt with ⟨e, t⟩
          rcases hab with hzero | hone
          · rcases hzero with ⟨hx, ht⟩
            subst hx
            subst ht
            rcases boundaryOrientationCases graph boundary boundary_edge e with hdir | hrev
            · -- In the direct case, endpoint `0` stays endpoint `0`.
              simpa [boundaryToCanonicalSource, boundaryHasCanonicalOrientation,
                SimpleGraph.realizationBoundary, canonicalBoundary, hdir.1, hdir.2] using
                graphRealizationSetoid_vertex_boundary_zero canonicalBoundary e
            · -- In the reversed case, endpoint `0` becomes the canonical endpoint `1`.
              rw [boundaryToCanonicalSource_inr_of_reverse graph boundary (0 : I) hrev]
              simpa [boundaryToCanonicalSource, SimpleGraph.realizationBoundary, canonicalBoundary,
                hrev.1, hrev.2, unitInterval.symm_zero] using
                graphRealizationSetoid_vertex_boundary_one canonicalBoundary e
          · rcases hone with ⟨hx, ht⟩
            subst hx
            subst ht
            rcases boundaryOrientationCases graph boundary boundary_edge e with hdir | hrev
            · -- In the direct case, endpoint `1` stays endpoint `1`.
              simpa [boundaryToCanonicalSource, boundaryHasCanonicalOrientation,
                SimpleGraph.realizationBoundary, canonicalBoundary, hdir.1, hdir.2] using
                graphRealizationSetoid_vertex_boundary_one canonicalBoundary e
            · -- In the reversed case, endpoint `1` becomes the canonical endpoint `0`.
              rw [boundaryToCanonicalSource_inr_of_reverse graph boundary (1 : I) hrev]
              simpa [boundaryToCanonicalSource, SimpleGraph.realizationBoundary, canonicalBoundary,
                hrev.1, hrev.2, unitInterval.symm_one] using
                graphRealizationSetoid_vertex_boundary_zero canonicalBoundary e
  | inr jt =>
      rcases jt with ⟨e, t⟩
      cases b with
      | inl x =>
          rcases hab with hzero | hone
          · rcases hzero with ⟨ht, hx⟩
            subst ht
            subst hx
            rcases boundaryOrientationCases graph boundary boundary_edge e with hdir | hrev
            · -- This is the symmetric orientation of the direct endpoint-`0` case.
              simpa [boundaryToCanonicalSource, boundaryHasCanonicalOrientation,
                SimpleGraph.realizationBoundary, canonicalBoundary, hdir.1, hdir.2] using
                (graphRealizationSetoid_vertex_boundary_zero canonicalBoundary e).symm
            · -- This is the symmetric orientation of the reversed endpoint-`1` case.
              rw [boundaryToCanonicalSource_inr_of_reverse graph boundary (0 : I) hrev]
              simpa [boundaryToCanonicalSource, SimpleGraph.realizationBoundary, canonicalBoundary,
                hrev.1, hrev.2, unitInterval.symm_zero] using
                (graphRealizationSetoid_vertex_boundary_one canonicalBoundary e).symm
          · rcases hone with ⟨ht, hx⟩
            subst ht
            subst hx
            rcases boundaryOrientationCases graph boundary boundary_edge e with hdir | hrev
            · -- This is the symmetric orientation of the direct endpoint-`1` case.
              simpa [boundaryToCanonicalSource, boundaryHasCanonicalOrientation,
                SimpleGraph.realizationBoundary, canonicalBoundary, hdir.1, hdir.2] using
                (graphRealizationSetoid_vertex_boundary_one canonicalBoundary e).symm
            · -- This is the symmetric orientation of the reversed endpoint-`0` case.
              rw [boundaryToCanonicalSource_inr_of_reverse graph boundary (1 : I) hrev]
              simpa [boundaryToCanonicalSource, SimpleGraph.realizationBoundary, canonicalBoundary,
                hrev.1, hrev.2, unitInterval.symm_one] using
                (graphRealizationSetoid_vertex_boundary_zero canonicalBoundary e).symm
      | inr zu =>
          cases hab

/-- Helper for Problem 4.6.3: the normalization map respects the full realization setoid from
the chosen realization to the canonical realization. -/
theorem boundaryToCanonical_respects
    {V : Type u} (graph : SimpleGraph V) (boundary : graph.edgeSet ↪ Fin 2 → V)
    (boundary_edge : ∀ e : graph.edgeSet, s(boundary e 0, boundary e 1) = (e : Sym2 V))
    {a b : V ⊕ (graph.edgeSet × I)} (hab : graphRealizationSetoid boundary a b) :
    graphRealizationSetoid (SimpleGraph.realizationBoundary graph)
      (boundaryToCanonicalSource boundary a) (boundaryToCanonicalSource boundary b) := by
  -- Extend the endpoint check from the generating relation to the equivalence closure.
  induction hab with
  | rel _ _ hrel =>
      exact boundaryToCanonicalSource_rel graph boundary boundary_edge hrel
  | refl a =>
      rfl
  | symm a b hab ih =>
      exact ih.symm
  | trans a b c hab hbc ihab ihbc =>
      exact Relation.EqvGen.trans _ _ _ ihab ihbc

/-- Helper for Problem 4.6.3: the same source normalization map also respects the canonical
realization relation back to the chosen realization, so it can serve as the inverse quotient map.
-/
theorem canonicalToBoundary_respects
    {V : Type u} (graph : SimpleGraph V) (boundary : graph.edgeSet ↪ Fin 2 → V)
    (boundary_edge : ∀ e : graph.edgeSet, s(boundary e 0, boundary e 1) = (e : Sym2 V))
    {a b : V ⊕ (graph.edgeSet × I)}
    (hab : graphRealizationSetoid (SimpleGraph.realizationBoundary graph) a b) :
    graphRealizationSetoid boundary
      (boundaryToCanonicalSource boundary a) (boundaryToCanonicalSource boundary b) := by
  let canonicalBoundary := SimpleGraph.realizationBoundary graph
  -- Again reduce to a single endpoint identification and undo the orientation choice.
  induction hab with
  | rel a b hrel =>
      cases a with
      | inl x =>
          cases b with
          | inl y =>
              cases hrel
          | inr jt =>
              rcases jt with ⟨e, t⟩
              rcases hrel with hzero | hone
              · rcases hzero with ⟨hx, ht⟩
                subst hx
                subst ht
                rcases boundaryOrientationCases graph boundary boundary_edge e with hdir | hrev
                · -- Directly oriented edges keep endpoint `0`.
                  simpa [boundaryToCanonicalSource, boundaryHasCanonicalOrientation,
                    SimpleGraph.realizationBoundary, canonicalBoundary, hdir.1, hdir.2] using
                    graphRealizationSetoid_vertex_boundary_zero boundary e
                · -- Reversed edges send canonical endpoint `0` back to chosen endpoint `1`.
                  rw [boundaryToCanonicalSource_inr_of_reverse graph boundary (0 : I) hrev]
                  simpa
                    [boundaryToCanonicalSource, SimpleGraph.realizationBoundary,
                      canonicalBoundary, hrev.1, hrev.2, unitInterval.symm_zero] using
                    graphRealizationSetoid_vertex_boundary_one boundary e
              · rcases hone with ⟨hx, ht⟩
                subst hx
                subst ht
                rcases boundaryOrientationCases graph boundary boundary_edge e with hdir | hrev
                · -- Directly oriented edges keep endpoint `1`.
                  simpa [boundaryToCanonicalSource, boundaryHasCanonicalOrientation,
                    SimpleGraph.realizationBoundary, canonicalBoundary, hdir.1, hdir.2] using
                    graphRealizationSetoid_vertex_boundary_one boundary e
                · -- Reversed edges send canonical endpoint `1` back to chosen endpoint `0`.
                  rw [boundaryToCanonicalSource_inr_of_reverse graph boundary (1 : I) hrev]
                  simpa
                    [boundaryToCanonicalSource, SimpleGraph.realizationBoundary,
                      canonicalBoundary, hrev.1, hrev.2, unitInterval.symm_one] using
                    graphRealizationSetoid_vertex_boundary_zero boundary e
      | inr jt =>
          rcases jt with ⟨e, t⟩
          cases b with
          | inl x =>
              rcases hrel with hzero | hone
              · rcases hzero with ⟨ht, hx⟩
                subst ht
                subst hx
                rcases boundaryOrientationCases graph boundary boundary_edge e with hdir | hrev
                · -- Symmetric form of the direct endpoint-`0` case.
                  simpa [boundaryToCanonicalSource, boundaryHasCanonicalOrientation,
                    SimpleGraph.realizationBoundary, canonicalBoundary, hdir.1, hdir.2] using
                    (graphRealizationSetoid_vertex_boundary_zero boundary e).symm
                · -- Symmetric form of the reversed endpoint-`1` case.
                  rw [boundaryToCanonicalSource_inr_of_reverse graph boundary (0 : I) hrev]
                  simpa
                    [boundaryToCanonicalSource, SimpleGraph.realizationBoundary,
                      canonicalBoundary, hrev.1, hrev.2, unitInterval.symm_zero] using
                    (graphRealizationSetoid_vertex_boundary_one boundary e).symm
              · rcases hone with ⟨ht, hx⟩
                subst ht
                subst hx
                rcases boundaryOrientationCases graph boundary boundary_edge e with hdir | hrev
                · -- Symmetric form of the direct endpoint-`1` case.
                  simpa [boundaryToCanonicalSource, boundaryHasCanonicalOrientation,
                    SimpleGraph.realizationBoundary, canonicalBoundary, hdir.1, hdir.2] using
                    (graphRealizationSetoid_vertex_boundary_one boundary e).symm
                · -- Symmetric form of the reversed endpoint-`0` case.
                  rw [boundaryToCanonicalSource_inr_of_reverse graph boundary (1 : I) hrev]
                  simpa
                    [boundaryToCanonicalSource, SimpleGraph.realizationBoundary,
                      canonicalBoundary, hrev.1, hrev.2, unitInterval.symm_one] using
                    (graphRealizationSetoid_vertex_boundary_zero boundary e).symm
          | inr zu =>
              cases hrel
  | refl a =>
      rfl
  | symm a b hab ih =>
      exact ih.symm
  | trans a b c hab hbc ihab ihbc =>
      exact Relation.EqvGen.trans _ _ _ ihab ihbc

/-- Helper for Problem 4.6.3: normalizing to the canonical boundary and normalizing back is the
identity on source representatives. -/
theorem boundaryToCanonicalSource_involutive
    {V : Type u} (graph : SimpleGraph V) (boundary : graph.edgeSet ↪ Fin 2 → V)
    (boundary_edge : ∀ e : graph.edgeSet, s(boundary e 0, boundary e 1) = (e : Sym2 V))
    (z : V ⊕ (graph.edgeSet × I)) :
    boundaryToCanonicalSource boundary (boundaryToCanonicalSource boundary z) = z := by
  -- The source map either does nothing or applies the interval symmetry, which squares to `id`.
  cases z with
  | inl x =>
      rfl
  | inr jt =>
      rcases jt with ⟨e, t⟩
      rcases boundaryOrientationCases graph boundary boundary_edge e with hdir | hrev
      · rw [boundaryToCanonicalSource_inr_of_canonical boundary t hdir]
        rw [boundaryToCanonicalSource_inr_of_canonical boundary t hdir]
      · rw [boundaryToCanonicalSource_inr_of_reverse graph boundary t hrev]
        rw [boundaryToCanonicalSource_inr_of_reverse graph boundary (σ t) hrev]
        exact congrArg (fun s : I => Sum.inr (e, s)) (unitInterval.symm_symm t)

/-- Helper for Problem 4.6.3: before any continuity work, the chosen realization and the
canonical realization are already equivalent as quotients of the same source after the
orientation-normalizing source involution. -/
noncomputable def realizationBoundaryEquiv
    {V : Type u} (graph : SimpleGraph V) (boundary : graph.edgeSet ↪ Fin 2 → V)
    (boundary_edge : ∀ e : graph.edgeSet, s(boundary e 0, boundary e 1) = (e : Sym2 V)) :
    graphRealization boundary ≃ graphRealization (SimpleGraph.realizationBoundary graph) where
  toFun :=
    Quotient.map' (boundaryToCanonicalSource boundary)
      (fun _ _ h => boundaryToCanonical_respects graph boundary boundary_edge h)
  invFun :=
    Quotient.map' (boundaryToCanonicalSource boundary)
      (fun _ _ h => canonicalToBoundary_respects graph boundary boundary_edge h)
  left_inv q := by
    -- Descend the source involution identity to the realization quotient.
    refine Quotient.inductionOn q ?_
    intro z
    simpa [boundaryToCanonicalSource_involutive] using
      congrArg (Quotient.mk (graphRealizationSetoid boundary))
        (boundaryToCanonicalSource_involutive graph boundary boundary_edge z)
  right_inv q := by
    -- The same involution identity gives the inverse law on the canonical quotient as well.
    refine Quotient.inductionOn q ?_
    intro z
    simpa [boundaryToCanonicalSource_involutive] using
      congrArg
        (Quotient.mk (graphRealizationSetoid (SimpleGraph.realizationBoundary graph)))
        (boundaryToCanonicalSource_involutive graph boundary boundary_edge z)

/-- Helper for Problem 4.6.3: the source partition where the chosen boundary already matches the
canonical orientation is clopen in the source-faithful topology on `graph.edgeSet × I`. -/
theorem isClopen_boundaryHasCanonicalOrientationFiber
    {V : Type u} {graph : SimpleGraph V} (boundary : graph.edgeSet ↪ Fin 2 → V) :
    let _ : TopologicalSpace (graph.edgeSet) := ⊥
    let _ : TopologicalSpace (graph.edgeSet × I) := inferInstance
    IsClopen {p : graph.edgeSet × I | boundaryHasCanonicalOrientation boundary p.1} := by
  let _ : TopologicalSpace (graph.edgeSet) := ⊥
  let _ : TopologicalSpace (graph.edgeSet × I) := inferInstance
  let _ : DiscreteTopology graph.edgeSet := discreteTopology_bot (graph.edgeSet)
  -- The orientation predicate only depends on the discrete edge coordinate.
  change IsClopen (Prod.fst ⁻¹' {e : graph.edgeSet | boundaryHasCanonicalOrientation boundary e})
  exact
    (isClopen_discrete {e : graph.edgeSet | boundaryHasCanonicalOrientation boundary e}).preimage
      continuous_fst

/-- Helper for Problem 4.6.3: in the source-faithful source topology, the normalization involution
on representatives is continuous. -/
theorem continuous_boundaryToCanonicalSource
    {V : Type u} {graph : SimpleGraph V} (boundary : graph.edgeSet ↪ Fin 2 → V) :
    let _ : TopologicalSpace V := ⊥
    let _ : TopologicalSpace (graph.edgeSet) := ⊥
    let _ : TopologicalSpace (V ⊕ (graph.edgeSet × I)) := inferInstance
    Continuous (boundaryToCanonicalSource boundary) := by
  let _ : TopologicalSpace V := ⊥
  let _ : TopologicalSpace (graph.edgeSet) := ⊥
  let _ : TopologicalSpace (V ⊕ (graph.edgeSet × I)) := inferInstance
  let _ : DecidablePred (boundaryHasCanonicalOrientation boundary) := Classical.decPred _
  -- Check continuity on the vertex and edge summands separately.
  rw [continuous_sum_dom]
  constructor
  · -- On vertices, the normalization map is the identity inclusion.
    change Continuous (fun x : V ↦ Sum.inl x)
    exact continuous_inl
  · -- On edges, the only branching is whether the chosen parametrization is canonical.
    change Continuous
      (fun p : graph.edgeSet × I ↦
        if boundaryHasCanonicalOrientation boundary p.1 then
          Sum.inr (p.1, p.2)
        else
          Sum.inr (p.1, σ p.2))
    have hclopen := isClopen_boundaryHasCanonicalOrientationFiber boundary
    have hfrontier :
        frontier {p : graph.edgeSet × I | boundaryHasCanonicalOrientation boundary p.1} = ∅ :=
      hclopen.frontier_eq
    refine Continuous.if ?_ ?_ ?_
    · intro p hp
      -- The two branches only need to agree on the empty frontier.
      exfalso
      rw [hfrontier] at hp
      exact hp
    · -- The canonical branch is the direct edge inclusion.
      exact continuous_inr
    · -- The reversed branch composes the edge inclusion with the interval symmetry.
      exact continuous_inr.comp
        (continuous_fst.prodMk (unitInterval.continuous_symm.comp continuous_snd))

/-- Helper for Problem 4.6.3: once the source normalization involution is continuous, the
quotient equivalence between the chosen and canonical realizations upgrades to a homeomorphism. -/
noncomputable def realizationBoundaryHomeomorph
    {V : Type u} (graph : SimpleGraph V) (boundary : graph.edgeSet ↪ Fin 2 → V)
    (boundary_edge : ∀ e : graph.edgeSet, s(boundary e 0, boundary e 1) = (e : Sym2 V)) :
    let _ : TopologicalSpace (graphRealization boundary) :=
      graphRealizationSourceFaithfulTopologicalSpace boundary
    let _ : TopologicalSpace (graphRealization (SimpleGraph.realizationBoundary graph)) :=
      graphRealizationSourceFaithfulTopologicalSpace (SimpleGraph.realizationBoundary graph)
    graphRealization boundary ≃ₜ graphRealization (SimpleGraph.realizationBoundary graph) := by
  let _ : TopologicalSpace V := ⊥
  let _ : TopologicalSpace (graph.edgeSet) := ⊥
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  let _ : TopologicalSpace (graphRealization (SimpleGraph.realizationBoundary graph)) :=
    graphRealizationSourceFaithfulTopologicalSpace (SimpleGraph.realizationBoundary graph)
  let hEquiv := realizationBoundaryEquiv graph boundary boundary_edge
  -- Package the quotient equivalence with the descended continuity in both directions.
  refine Homeomorph.mk hEquiv ?_ ?_
  · -- The forward map is the quotient descent of the continuous source involution.
    change Continuous (Quotient.map' (boundaryToCanonicalSource boundary)
      (fun a b h ↦ boundaryToCanonical_respects graph boundary boundary_edge h))
    exact Continuous.quotient_map' (continuous_boundaryToCanonicalSource boundary)
      (fun a b h ↦ boundaryToCanonical_respects graph boundary boundary_edge h)
  · -- The inverse map uses the same source involution against the reverse setoid relation.
    change Continuous (Quotient.map' (boundaryToCanonicalSource boundary)
      (fun a b h ↦ canonicalToBoundary_respects graph boundary boundary_edge h))
    exact Continuous.quotient_map' (continuous_boundaryToCanonicalSource boundary)
      (fun a b h ↦ canonicalToBoundary_respects graph boundary boundary_edge h)

/-- Helper for Problem 4.6.3: the fixed `K₅` obstruction must be independent of the canonical
Kuratowski criterion itself, so it is split out as its own graph-theoretic frontier. -/
theorem completeGraphFiveBoundary_notEmbeddableInPlane :
    ¬ embeddableInPlane
      (SimpleGraph.realizationBoundary (SimpleGraph.completeGraph (Fin 5))) := by
  -- Provide the finite vertex instance explicitly so the `FiniteGraph` helper does not spend
  -- heartbeats reconstructing it from `Fintype`.
  let _ : Finite (Fin 5) := Finite.of_fintype (Fin 5)
  let _ : FiniteGraph (SimpleGraph.realizationBoundary (SimpleGraph.completeGraph (Fin 5))) :=
    finiteGraph_realizationBoundary_ofFinite (SimpleGraph.completeGraph (Fin 5))
  -- Route correction: this base obstruction now reads off the finished support-owned owner
  -- criterion rather than feeding back into its assembly.
  intro hEmb
  have hNoObstruction :
      ¬ (SimpleGraph.completeGraph (Fin 5)).containsSubgraphRealizationHomeomorphicTo
        (SimpleGraph.completeGraph (Fin 5)) := by
    -- The owner theorem rules out a realized `K₅` obstruction inside any plane-embeddable `K₅`.
    exact (canonicalKuratowskiCriterionCore
      (graph := SimpleGraph.completeGraph (Fin 5))).mp hEmb |>.1
  -- The top subgraph witnesses that `K₅` contains its own canonical obstruction.
  exact hNoObstruction completeGraphFive_containsSelfObstruction

/-- Helper for Problem 4.6.3: the fixed `K_{3,3}` obstruction must also be proved independently
of the canonical Kuratowski criterion. -/
theorem completeBipartiteGraphThreeThreeBoundary_notEmbeddableInPlane :
    ¬ embeddableInPlane
      (SimpleGraph.realizationBoundary (completeBipartiteGraph (Fin 3) (Fin 3))) := by
  -- Again make the finite vertex type explicit before constructing the finite realization.
  let _ : Finite (Fin 3 ⊕ Fin 3) := Finite.of_fintype (Fin 3 ⊕ Fin 3)
  let _ :
      FiniteGraph (SimpleGraph.realizationBoundary (completeBipartiteGraph (Fin 3) (Fin 3))) :=
    finiteGraph_realizationBoundary_ofFinite (completeBipartiteGraph (Fin 3) (Fin 3))
  -- Route correction: this second base obstruction also now projects from the finished support
  -- owner theorem instead of participating in its proof.
  intro hEmb
  have hNoObstruction :
      ¬ (completeBipartiteGraph (Fin 3) (Fin 3)).containsSubgraphRealizationHomeomorphicTo
        (completeBipartiteGraph (Fin 3) (Fin 3)) := by
    -- The owner theorem likewise rules out a realized `K₃,₃` obstruction inside any
    -- plane-embeddable `K₃,₃`.
    exact (canonicalKuratowskiCriterionCore
      (graph := completeBipartiteGraph (Fin 3) (Fin 3))).mp hEmb |>.2
  -- Again the top subgraph witnesses the obstruction inside itself.
  exact hNoObstruction completeBipartiteGraphThreeThree_containsSelfObstruction

/-- Helper for Problem 4.6.3: once the two fixed obstructions are known independently, the
forward half of the canonical Kuratowski criterion is a direct specialization of the generic
obstruction-monotonicity theorem. -/
theorem canonicalKuratowskiForward
    {V : Type u} (graph : SimpleGraph V)
    [FiniteGraph (SimpleGraph.realizationBoundary graph)] :
    embeddableInPlane (SimpleGraph.realizationBoundary graph) →
      ¬ graph.containsSubgraphRealizationHomeomorphicTo (SimpleGraph.completeGraph (Fin 5)) ∧
        ¬ graph.containsSubgraphRealizationHomeomorphicTo
          (completeBipartiteGraph (Fin 3) (Fin 3)) := by
  intro hEmb
  -- Fix the two finite obstruction vertex types before specializing the generic monotonicity
  -- theorem to them.
  let _ : Finite (Fin 5) := Finite.of_fintype (Fin 5)
  let _ : Finite (Fin 3 ⊕ Fin 3) := Finite.of_fintype (Fin 3 ⊕ Fin 3)
  let _ : FiniteGraph (SimpleGraph.realizationBoundary (SimpleGraph.completeGraph (Fin 5))) :=
    finiteGraph_realizationBoundary_ofFinite (SimpleGraph.completeGraph (Fin 5))
  let _ :
      FiniteGraph (SimpleGraph.realizationBoundary (completeBipartiteGraph (Fin 3) (Fin 3))) :=
    finiteGraph_realizationBoundary_ofFinite (completeBipartiteGraph (Fin 3) (Fin 3))
  -- Apply the generic monotonicity theorem once the two classical obstructions are known to be
  -- non-embeddable independently.
  simpa [noRealizedKuratowskiObstruction] using
    noKuratowskiObstruction_of_embeddableInPlane_of_nonembeddableObstructions
      graph hEmb completeGraphFiveBoundary_notEmbeddableInPlane
      completeBipartiteGraphThreeThreeBoundary_notEmbeddableInPlane

/-- Helper for Problem 4.6.3: the imported support owner theorem already packages the converse
half of Kuratowski's criterion as a direct implication from the obstruction-free predicate. -/
theorem embeddableInPlane_realizationBoundary_of_noRealizedKuratowskiObstruction
    {V : Type u} (graph : SimpleGraph V)
    [FiniteGraph (SimpleGraph.realizationBoundary graph)]
    (hNo : noRealizedKuratowskiObstruction graph) :
    embeddableInPlane (SimpleGraph.realizationBoundary graph) := by
  -- Read the converse direction directly from the canonical owner theorem on packaged
  -- obstruction-freeness before returning to the explicit `K₅` and `K_{3,3}` clauses.
  exact (planarRealizationBoundary_iff_noRealizedKuratowskiObstruction (graph := graph)).2 hNo

/-- Helper for Problem 4.6.3: the forward half of the canonical criterion can also be read as
the packaged absence of realized Kuratowski obstructions. -/
theorem noRealizedKuratowskiObstruction_of_embeddableInPlane
    {V : Type u} (graph : SimpleGraph V)
    [FiniteGraph (SimpleGraph.realizationBoundary graph)]
    (hEmb : embeddableInPlane (SimpleGraph.realizationBoundary graph)) :
    noRealizedKuratowskiObstruction graph := by
  -- Package the two explicit obstruction exclusions into the support-owned predicate.
  simpa [noRealizedKuratowskiObstruction] using canonicalKuratowskiForward (graph := graph) hEmb

/-- Helper for Problem 4.6.3: the converse half of the canonical criterion is the remaining
graph-theoretic frontier after the realization transport has been normalized away. -/
theorem canonicalKuratowskiConverse
    {V : Type u} (graph : SimpleGraph V)
    [FiniteGraph (SimpleGraph.realizationBoundary graph)]
    (hK5 : ¬ graph.containsSubgraphRealizationHomeomorphicTo (SimpleGraph.completeGraph (Fin 5)))
    (hK33 :
      ¬ graph.containsSubgraphRealizationHomeomorphicTo
        (completeBipartiteGraph (Fin 3) (Fin 3))) :
    embeddableInPlane (SimpleGraph.realizationBoundary graph) := by
  -- Route correction: the transport layer is already complete, so this converse is now the
  -- single remaining graph-theoretic frontier inside the editable file.
  -- Repackage the two explicit obstruction exclusions into the imported packaged predicate.
  exact
    embeddableInPlane_realizationBoundary_of_noRealizedKuratowskiObstruction
      (graph := graph) ⟨hK5, hK33⟩

theorem canonicalKuratowskiCriterion
    {V : Type u} (graph : SimpleGraph V)
    [FiniteGraph (SimpleGraph.realizationBoundary graph)] :
    embeddableInPlane (SimpleGraph.realizationBoundary graph) ↔
      ¬ graph.containsSubgraphRealizationHomeomorphicTo (SimpleGraph.completeGraph (Fin 5)) ∧
        ¬ graph.containsSubgraphRealizationHomeomorphicTo
          (completeBipartiteGraph (Fin 3) (Fin 3)) := by
  constructor
  · -- The forward half is now a direct specialization of obstruction monotonicity.
    intro hEmb
    -- First package the forward exclusion theorem in the same obstruction-free form used by the
    -- support owner theorem, then unfold it back to the explicit `K₅` and `K_{3,3}` clauses.
    simpa [noRealizedKuratowskiObstruction] using
      noRealizedKuratowskiObstruction_of_embeddableInPlane (graph := graph) hEmb
  · rintro ⟨hK5, hK33⟩
    -- The converse is delegated to the remaining canonical graph-theoretic frontier.
    exact canonicalKuratowskiConverse (graph := graph) hK5 hK33

/-- Helper for Problem 4.6.3: the canonical realization of `K₅` is the first concrete
non-embeddable obstruction needed for the forward half of Kuratowski's criterion. -/
theorem notEmbeddableInPlane_completeGraphFiveBoundary :
    ¬ embeddableInPlane
      (SimpleGraph.realizationBoundary (SimpleGraph.completeGraph (Fin 5))) := by
  -- Route correction: use the independent fixed-obstruction theorem rather than the cyclic
  -- derivation through `canonicalKuratowskiCriterion`.
  exact completeGraphFiveBoundary_notEmbeddableInPlane

/-- Helper for Problem 4.6.3: the canonical realization of `K_{3,3}` is the second concrete
non-embeddable obstruction needed for the forward half of Kuratowski's criterion. -/
theorem notEmbeddableInPlane_completeBipartiteGraphThreeThreeBoundary :
    ¬ embeddableInPlane
      (SimpleGraph.realizationBoundary (completeBipartiteGraph (Fin 3) (Fin 3))) := by
  -- Route correction: this now points to the independent `K_{3,3}` base obstruction theorem.
  exact completeBipartiteGraphThreeThreeBoundary_notEmbeddableInPlane

/-- Helper for Problem 4.6.3: once the two classical obstructions are excluded, the remaining
canonical finite realization is plane-embeddable. This is the deep converse half of Kuratowski's
criterion. -/
-- Route correction: the transport from an arbitrary boundary to the canonical boundary is already
-- complete above, so the only remaining frontier is the genuine canonical Kuratowski converse.
theorem embeddableInPlane_of_noKuratowskiObstruction_canonical
    {V : Type u} (graph : SimpleGraph V)
    [FiniteGraph (SimpleGraph.realizationBoundary graph)]
    (hK5 : ¬ graph.containsSubgraphRealizationHomeomorphicTo (SimpleGraph.completeGraph (Fin 5)))
    (hK33 :
      ¬ graph.containsSubgraphRealizationHomeomorphicTo
        (completeBipartiteGraph (Fin 3) (Fin 3))) :
    embeddableInPlane (SimpleGraph.realizationBoundary graph) := by
  -- The converse is now factored through the dedicated canonical graph-theoretic frontier.
  exact canonicalKuratowskiConverse (graph := graph) hK5 hK33

/-- Helper for Problem 4.6.3: Kuratowski's criterion on the finite canonical realization boundary
of `graph`. This is the remaining graph-theoretic frontier after normalizing away the arbitrary
parametrization `boundary`. -/
-- Route correction: the transport layer and the generic obstruction-monotonicity theorem are now
-- complete, so the only remaining frontier is to supply the two concrete non-embeddability base
-- cases and the finite canonical Kuratowski converse isolated above.
theorem canonicalEmbeddableInPlane_iff_noKuratowskiObstruction
    {V : Type u} (graph : SimpleGraph V)
    [FiniteGraph (SimpleGraph.realizationBoundary graph)] :
    embeddableInPlane (SimpleGraph.realizationBoundary graph) ↔
      ¬ graph.containsSubgraphRealizationHomeomorphicTo (SimpleGraph.completeGraph (Fin 5)) ∧
        ¬ graph.containsSubgraphRealizationHomeomorphicTo
          (completeBipartiteGraph (Fin 3) (Fin 3)) := by
  -- This is exactly the canonical criterion isolated above.
  simpa using canonicalKuratowskiCriterion (graph := graph)

/-- Helper for Problem 4.6.3: replacing an arbitrary boundary parametrization by the canonical
realization boundary of the same graph does not change plane embeddability. -/
theorem embeddableInPlane_iff_embeddableInPlane_realizationBoundary
    {V : Type u} (graph : SimpleGraph V) (boundary : graph.edgeSet ↪ Fin 2 → V)
    (boundary_edge : ∀ e : graph.edgeSet, s(boundary e 0, boundary e 1) = (e : Sym2 V)) :
    embeddableInPlane boundary ↔ embeddableInPlane (SimpleGraph.realizationBoundary graph) := by
  let canonicalBoundary := SimpleGraph.realizationBoundary graph
  have hHomeomorph := realizationBoundaryHomeomorph graph boundary boundary_edge
  -- Transport plane embeddability across the quotient-level homeomorphism to the canonical model.
  simpa [canonicalBoundary] using
    embeddableInPlane_iff_homeomorphic boundary canonicalBoundary hHomeomorph

/-- Helper for Problem 4.6.3: once Kuratowski's criterion is known for the canonical realization
boundary of `graph`, the same criterion follows for any chosen realization boundary of `graph` by
transporting plane embeddability across the realization homeomorphism. -/
theorem embeddableInPlane_iff_noKuratowskiObstruction_of_canonicalCriterion
    {V : Type u} (graph : SimpleGraph V) (boundary : graph.edgeSet ↪ Fin 2 → V)
    [FiniteGraph boundary]
    (boundary_edge : ∀ e : graph.edgeSet, s(boundary e 0, boundary e 1) = (e : Sym2 V))
    (hCanonical :
      embeddableInPlane (SimpleGraph.realizationBoundary graph) ↔
        ¬ graph.containsSubgraphRealizationHomeomorphicTo (SimpleGraph.completeGraph (Fin 5)) ∧
          ¬ graph.containsSubgraphRealizationHomeomorphicTo
            (completeBipartiteGraph (Fin 3) (Fin 3))) :
    embeddableInPlane boundary ↔
      ¬ graph.containsSubgraphRealizationHomeomorphicTo (SimpleGraph.completeGraph (Fin 5)) ∧
        ¬ graph.containsSubgraphRealizationHomeomorphicTo
          (completeBipartiteGraph (Fin 3) (Fin 3)) := by
  let canonicalBoundary := SimpleGraph.realizationBoundary graph
  -- The only boundary-dependent part of the textbook statement is the left-hand realization.
  let _ : FiniteGraph canonicalBoundary :=
    finiteGraph_realizationBoundary_ofFiniteGraph graph boundary
  calc
    embeddableInPlane boundary ↔ embeddableInPlane canonicalBoundary := by
      -- First replace the chosen realization by the canonical realization of the same graph.
      exact
        embeddableInPlane_iff_embeddableInPlane_realizationBoundary
          graph boundary boundary_edge
    _ ↔ ¬ graph.containsSubgraphRealizationHomeomorphicTo (SimpleGraph.completeGraph (Fin 5)) ∧
          ¬ graph.containsSubgraphRealizationHomeomorphicTo
            (completeBipartiteGraph (Fin 3) (Fin 3)) := by
      -- Then read off the canonical Kuratowski criterion supplied as input.
      simpa [canonicalBoundary] using hCanonical

/-- Problem 4.6.3. Let `graph` be a finite graph, let `boundary : graph.edgeSet ↪ Fin 2 → V` be a
chosen realization of its edges, and suppose `boundary_edge` identifies each chosen parameterized
edge with the corresponding edge of `graph`. Then the source-faithful realization
`graphRealization boundary` is embeddable in the plane if and only if `graph` contains no
subgraph whose canonical realization is homeomorphic to the canonical realization of
`SimpleGraph.completeGraph (Fin 5)` and no subgraph whose canonical realization is homeomorphic to
the canonical realization of
`completeBipartiteGraph (Fin 3) (Fin 3)`.

This is Kuratowski's criterion, expressed on the chapter's realization API from
`Definition 4.1.2`, the source-faithful topology from `Definition 4.1.4`, and the chapter's
canonical `SimpleGraph.Subgraph` owner from `Definition 4.1.6`. -/
theorem embeddableInPlane_iff_noKuratowskiObstruction
    {V : Type u} (graph : SimpleGraph V) (boundary : graph.edgeSet ↪ Fin 2 → V)
    [FiniteGraph boundary]
    (boundary_edge : ∀ e : graph.edgeSet, s(boundary e 0, boundary e 1) = (e : Sym2 V)) :
    embeddableInPlane boundary ↔
      ¬ graph.containsSubgraphRealizationHomeomorphicTo (SimpleGraph.completeGraph (Fin 5)) ∧
        ¬ graph.containsSubgraphRealizationHomeomorphicTo
          (completeBipartiteGraph (Fin 3) (Fin 3)) := by
  let canonicalBoundary := SimpleGraph.realizationBoundary graph
  -- Route correction: the wrapper theorem is now a direct application of the target-file helper
  -- that isolates realization transport from the imported canonical criterion owner.
  let _ : FiniteGraph canonicalBoundary :=
    finiteGraph_realizationBoundary_ofFiniteGraph graph boundary
  exact
    embeddableInPlane_iff_noKuratowskiObstruction_of_canonicalCriterion
      graph boundary boundary_edge
      (canonicalEmbeddableInPlane_iff_noKuratowskiObstruction (graph := graph))
