import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Problem_4_6_3.Obstruction
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Problem_4_6_3.Planarity
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Definition_4_1_4
import Mathlib.Topology.Separation.Hausdorff

open scoped unitInterval

universe u

/-- Helper for Problem 4.6.3: plane embeddability only depends on the homeomorphism type of the
source-faithful realization. -/
theorem embeddableInPlane_iff_homeomorphic
    {V₁ : Type u} {V₂ : Type*} {J₁ : Type*} {J₂ : Type*}
    (boundary₁ : J₁ ↪ Fin 2 → V₁) (boundary₂ : J₂ ↪ Fin 2 → V₂)
    (h :
      let _ : TopologicalSpace (graphRealization boundary₁) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary₁
      let _ : TopologicalSpace (graphRealization boundary₂) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary₂
      graphRealization boundary₁ ≃ₜ graphRealization boundary₂) :
    embeddableInPlane boundary₁ ↔ embeddableInPlane boundary₂ := by
  let _ : TopologicalSpace (graphRealization boundary₁) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary₁
  let _ : TopologicalSpace (graphRealization boundary₂) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary₂
  constructor
  · rintro ⟨f, hf⟩
    -- Postcompose the embedding with the inverse homeomorphism on the source.
    refine ⟨fun x ↦ f (h.symm x), ?_⟩
    exact hf.comp h.symm.isEmbedding
  · rintro ⟨f, hf⟩
    -- Precompose the embedding with the forward homeomorphism on the source.
    refine ⟨fun x ↦ f (h x), ?_⟩
    exact hf.comp h.isEmbedding

/-- Helper for Problem 4.6.3: any source representative lying in the fiber of the vertex `x`
is equivalent to the vertex representative itself. -/
theorem graphRealizationSetoid_to_vertex_of_inVertexFiber
    {X₀ : Type*} {J : Type*} (boundary : J ↪ Fin 2 → X₀) (x : X₀)
    {z : X₀ ⊕ (J × I)} (hz : inVertexFiber boundary x z) :
    graphRealizationSetoid boundary z (Sum.inl x) := by
  -- Collapse each endpoint representative in the fiber back onto the common vertex `x`.
  cases z with
  | inl y =>
      have hy : y = x := by
        simpa [inVertexFiber] using hz
      subst hy
      rfl
  | inr jt =>
      rcases jt with ⟨j, t⟩
      have hz' : (t = 0 ∧ boundary j 0 = x) ∨ (t = 1 ∧ boundary j 1 = x) := by
        simpa [inVertexFiber] using hz
      rcases hz' with ⟨ht, hx⟩ | ⟨ht, hx⟩
      · subst ht
        simpa [hx] using (graphRealizationSetoid_vertex_boundary_zero boundary j).symm
      · subst ht
        simpa [hx] using (graphRealizationSetoid_vertex_boundary_one boundary j).symm

/-- Helper for Problem 4.6.3: two source representatives in the same vertex fiber are equivalent
in the realization quotient. -/
theorem graphRealizationSetoid_of_inVertexFiber
    {X₀ : Type*} {J : Type*} (boundary : J ↪ Fin 2 → X₀) (x : X₀)
    {a b : X₀ ⊕ (J × I)} (ha : inVertexFiber boundary x a) (hb : inVertexFiber boundary x b) :
    graphRealizationSetoid boundary a b := by
  -- Move both points to the common vertex representative and compose the two quotient equalities.
  exact Relation.EqvGen.trans _ _ _
    (graphRealizationSetoid_to_vertex_of_inVertexFiber boundary x ha)
    (graphRealizationSetoid_to_vertex_of_inVertexFiber boundary x hb).symm

/-- Helper for Problem 4.6.3: include canonical source representatives of a subgraph realization
into the ambient graph's canonical source. -/
def subgraphRealizationBoundarySourceMap
    {V : Type u} {graph : SimpleGraph V} (T : graph.Subgraph) :
    T.verts ⊕ (T.edgeSet × I) → V ⊕ (graph.edgeSet × I)
  | Sum.inl x => Sum.inl x.1
  | Sum.inr (e, t) => Sum.inr (⟨e.1, T.edgeSet_subset e.2⟩, t)

/-- Helper for Problem 4.6.3: the source inclusion of a canonical subgraph realization preserves
the generating endpoint identifications. -/
theorem subgraphRealizationBoundarySourceMap_rel
    {V : Type u} {graph : SimpleGraph V} (T : graph.Subgraph)
    {a b : T.verts ⊕ (T.edgeSet × I)}
    (hab : graphRealizationRel (SimpleGraph.Subgraph.realizationBoundary T) a b) :
    graphRealizationSetoid (SimpleGraph.realizationBoundary graph)
      (subgraphRealizationBoundarySourceMap T a)
      (subgraphRealizationBoundarySourceMap T b) := by
  -- Each subgraph endpoint identification is literally the corresponding ambient endpoint
  -- identification for the same underlying edge.
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
            simpa [subgraphRealizationBoundarySourceMap,
              SimpleGraph.Subgraph.realizationBoundary, SimpleGraph.realizationBoundary] using
              graphRealizationSetoid_vertex_boundary_zero (SimpleGraph.realizationBoundary graph)
                ⟨e.1, T.edgeSet_subset e.2⟩
          · rcases hone with ⟨hx, ht⟩
            subst hx
            subst ht
            simpa [subgraphRealizationBoundarySourceMap,
              SimpleGraph.Subgraph.realizationBoundary, SimpleGraph.realizationBoundary] using
              graphRealizationSetoid_vertex_boundary_one (SimpleGraph.realizationBoundary graph)
                ⟨e.1, T.edgeSet_subset e.2⟩
  | inr jt =>
      rcases jt with ⟨e, t⟩
      cases b with
      | inl x =>
          rcases hab with hzero | hone
          · rcases hzero with ⟨ht, hx⟩
            subst ht
            subst hx
            simpa [subgraphRealizationBoundarySourceMap,
              SimpleGraph.Subgraph.realizationBoundary, SimpleGraph.realizationBoundary] using
              (graphRealizationSetoid_vertex_boundary_zero (SimpleGraph.realizationBoundary graph)
                ⟨e.1, T.edgeSet_subset e.2⟩).symm
          · rcases hone with ⟨ht, hx⟩
            subst ht
            subst hx
            simpa [subgraphRealizationBoundarySourceMap,
              SimpleGraph.Subgraph.realizationBoundary, SimpleGraph.realizationBoundary] using
              (graphRealizationSetoid_vertex_boundary_one (SimpleGraph.realizationBoundary graph)
                ⟨e.1, T.edgeSet_subset e.2⟩).symm
      | inr zu =>
          cases hab

/-- Helper for Problem 4.6.3: the source inclusion of a canonical subgraph realization respects
the full realization setoid. -/
theorem subgraphRealizationBoundarySourceMap_respects
    {V : Type u} {graph : SimpleGraph V} (T : graph.Subgraph)
    {a b : T.verts ⊕ (T.edgeSet × I)}
    (hab : graphRealizationSetoid (SimpleGraph.Subgraph.realizationBoundary T) a b) :
    graphRealizationSetoid (SimpleGraph.realizationBoundary graph)
      (subgraphRealizationBoundarySourceMap T a)
      (subgraphRealizationBoundarySourceMap T b) := by
  -- Extend the generating endpoint check to the full equivalence closure.
  induction hab with
  | rel _ _ hrel =>
      exact subgraphRealizationBoundarySourceMap_rel T hrel
  | refl a =>
      rfl
  | symm a b hab ih =>
      exact ih.symm
  | trans a b c hab hbc ihab ihbc =>
      exact Relation.EqvGen.trans _ _ _ ihab ihbc

/-- Helper for Problem 4.6.3: the source inclusion for a canonical subgraph realization is
injective before passing to quotients. -/
theorem subgraphRealizationBoundarySourceMap_injective
    {V : Type u} {graph : SimpleGraph V} (T : graph.Subgraph) :
    Function.Injective (subgraphRealizationBoundarySourceMap T) := by
  -- The inclusion remembers the underlying vertex or edge together with the same interval
  -- coordinate, so equality in the ambient source already forces equality in the subgraph source.
  intro a b h
  cases a with
  | inl x =>
      cases b with
      | inl y =>
          have hxy : x.1 = y.1 := Sum.inl.inj h
          exact congrArg Sum.inl (Subtype.ext hxy)
      | inr jt =>
          cases h
  | inr jt =>
      rcases jt with ⟨e, t⟩
      cases b with
      | inl y =>
          cases h
      | inr zu =>
          rcases zu with ⟨e', t'⟩
          have hpair :
              ((⟨e.1, T.edgeSet_subset e.2⟩ : graph.edgeSet), t) =
                ((⟨e'.1, T.edgeSet_subset e'.2⟩ : graph.edgeSet), t') :=
            Sum.inr.inj h
          have hedge :
              (⟨e.1, T.edgeSet_subset e.2⟩ : graph.edgeSet) =
                (⟨e'.1, T.edgeSet_subset e'.2⟩ : graph.edgeSet) :=
            congrArg Prod.fst hpair
          have ht : t = t' := congrArg Prod.snd hpair
          apply congrArg Sum.inr
          apply Prod.ext
          · apply Subtype.ext
            exact congrArg (fun ee : graph.edgeSet ↦ ee.1) hedge
          · exact ht

/-- Helper for Problem 4.6.3: the ambient vertex-fiber predicate pulls back exactly to the
corresponding subgraph vertex fiber under the canonical source inclusion. -/
theorem subgraphRealizationBoundarySourceMap_inVertexFiber_iff
    {V : Type u} {graph : SimpleGraph V} (T : graph.Subgraph) (x : T.verts)
    (z : T.verts ⊕ (T.edgeSet × I)) :
    inVertexFiber (SimpleGraph.realizationBoundary graph) x.1
      (subgraphRealizationBoundarySourceMap T z) ↔
        inVertexFiber (SimpleGraph.Subgraph.realizationBoundary T) x z := by
  -- The source inclusion forgets no vertex information: it only drops the subtype wrappers.
  cases z with
  | inl y =>
      change y.1 = x.1 ↔ y = x
      constructor
      · intro h
        exact Subtype.ext h
      · intro h
        exact congrArg Subtype.val h
  | inr jt =>
      rcases jt with ⟨e, t⟩
      change
        ((t = 0 ∧ e.1.out.1 = x.1) ∨ (t = 1 ∧ e.1.out.2 = x.1)) ↔
          ((t = 0 ∧
              (⟨e.1.out.1, T.mem_verts_of_mem_edge e.2 (Sym2.out_fst_mem e.1)⟩ : T.verts) = x) ∨
            (t = 1 ∧
              (⟨e.1.out.2, T.mem_verts_of_mem_edge e.2 (Sym2.out_snd_mem e.1)⟩ : T.verts) = x))
      constructor
      · intro hz
        rcases hz with ⟨ht, hx⟩ | ⟨ht, hx⟩
        · exact Or.inl ⟨ht, Subtype.ext hx⟩
        · exact Or.inr ⟨ht, Subtype.ext hx⟩
      · intro hz
        rcases hz with ⟨ht, hx⟩ | ⟨ht, hx⟩
        · exact Or.inl ⟨ht, congrArg Subtype.val hx⟩
        · exact Or.inr ⟨ht, congrArg Subtype.val hx⟩

/-- Helper for Problem 4.6.3: the quotient-level map from a canonical subgraph realization into
the ambient canonical realization is obtained by descending the source inclusion. -/
noncomputable def subgraphRealizationBoundaryMap
    {V : Type u} {graph : SimpleGraph V} (T : graph.Subgraph) :
    graphRealization (SimpleGraph.Subgraph.realizationBoundary T) →
      graphRealization (SimpleGraph.realizationBoundary graph) :=
  Quotient.map' (subgraphRealizationBoundarySourceMap T)
    (fun _ _ h ↦ subgraphRealizationBoundarySourceMap_respects T h)

/-- Helper for Problem 4.6.3: the quotient-level inclusion of a canonical subgraph realization is
continuous for the source-faithful realization topologies. -/
theorem continuous_subgraphRealizationBoundaryMap
    {V : Type u} {graph : SimpleGraph V} (T : graph.Subgraph) :
    let _ : TopologicalSpace (graphRealization (SimpleGraph.Subgraph.realizationBoundary T)) :=
      graphRealizationSourceFaithfulTopologicalSpace (SimpleGraph.Subgraph.realizationBoundary T)
    let _ : TopologicalSpace (graphRealization (SimpleGraph.realizationBoundary graph)) :=
      graphRealizationSourceFaithfulTopologicalSpace (SimpleGraph.realizationBoundary graph)
    Continuous (subgraphRealizationBoundaryMap T) := by
  let subgraphBoundary := SimpleGraph.Subgraph.realizationBoundary T
  let ambientBoundary := SimpleGraph.realizationBoundary graph
  let _ : TopologicalSpace T.verts := ⊥
  let _ : TopologicalSpace T.edgeSet := ⊥
  let _ : TopologicalSpace V := ⊥
  let _ : TopologicalSpace graph.edgeSet := ⊥
  let _ : DiscreteTopology T.verts := discreteTopology_bot T.verts
  let _ : DiscreteTopology T.edgeSet := discreteTopology_bot T.edgeSet
  let _ : DiscreteTopology V := discreteTopology_bot V
  let _ : DiscreteTopology graph.edgeSet := discreteTopology_bot graph.edgeSet
  let _ : TopologicalSpace (graphRealization subgraphBoundary) :=
    graphRealizationSourceFaithfulTopologicalSpace subgraphBoundary
  let _ : TopologicalSpace (graphRealization ambientBoundary) :=
    graphRealizationSourceFaithfulTopologicalSpace ambientBoundary
  -- Descend the continuous source inclusion through the quotient map once.
  change Continuous
    (Quotient.map' (subgraphRealizationBoundarySourceMap T)
      (fun a b h ↦ subgraphRealizationBoundarySourceMap_respects T h))
  have hEdge :
      Continuous
        (fun e : T.edgeSet ↦ (⟨e.1, T.edgeSet_subset e.2⟩ : graph.edgeSet)) :=
    continuous_of_discreteTopology
  have hSource :
      Continuous (subgraphRealizationBoundarySourceMap T) := by
    rw [continuous_sum_dom]
    constructor
    · -- On vertices, the map is just the subtype inclusion.
      exact continuous_of_discreteTopology
    · -- On edges, pair the edge inclusion with the unchanged interval coordinate.
      have hPair :
          Continuous
            (fun p : T.edgeSet × I ↦ ((⟨p.1.1, T.edgeSet_subset p.1.2⟩ : graph.edgeSet), p.2)) :=
        (hEdge.comp continuous_fst).prodMk continuous_snd
      simpa [subgraphRealizationBoundarySourceMap] using continuous_inr.comp hPair
  exact Continuous.quotient_map' hSource
    (fun a b h ↦ subgraphRealizationBoundarySourceMap_respects T h)

/-- Helper for Problem 4.6.3: the quotient-level inclusion of a canonical subgraph realization is
injective because endpoint identifications are reflected on the image of the source inclusion. -/
theorem injective_subgraphRealizationBoundaryMap
    {V : Type u} {graph : SimpleGraph V} (T : graph.Subgraph) :
    Function.Injective (subgraphRealizationBoundaryMap T) := by
  let subgraphBoundary := SimpleGraph.Subgraph.realizationBoundary T
  let ambientBoundary := SimpleGraph.realizationBoundary graph
  -- Analyze an ambient quotient equality by whether the chosen subgraph source representative is
  -- a vertex, an endpoint, or a genuine interior point.
  intro q₁ q₂ hq
  refine Quotient.inductionOn₂ q₁ q₂ ?_ hq
  intro a b hab
  apply Quotient.sound
  have hAmbient :
      graphRealizationSetoid ambientBoundary
        (subgraphRealizationBoundarySourceMap T a)
        (subgraphRealizationBoundarySourceMap T b) := Quotient.eq'.1 hab
  cases a with
  | inl x =>
      have hFiberA :
          inVertexFiber ambientBoundary x.1
            (subgraphRealizationBoundarySourceMap T (Sum.inl x)) := by
        simp [inVertexFiber, subgraphRealizationBoundarySourceMap]
      have hFiberB :
          inVertexFiber ambientBoundary x.1
            (subgraphRealizationBoundarySourceMap T b) := by
        exact (graphRealizationSetoid_inVertexFiber_iff ambientBoundary x.1 hAmbient).1 hFiberA
      have hSubA : inVertexFiber subgraphBoundary x (Sum.inl x) := by
        simp [inVertexFiber]
      have hSubB : inVertexFiber subgraphBoundary x b := by
        exact (subgraphRealizationBoundarySourceMap_inVertexFiber_iff T x b).mp hFiberB
      exact graphRealizationSetoid_of_inVertexFiber subgraphBoundary x hSubA hSubB
  | inr jt =>
      rcases jt with ⟨e, t⟩
      by_cases ht0 : t = 0
      · let x : T.verts := ⟨e.1.out.1, T.mem_verts_of_mem_edge e.2 (Sym2.out_fst_mem e.1)⟩
        have hFiberA :
            inVertexFiber ambientBoundary x.1
              (subgraphRealizationBoundarySourceMap T (Sum.inr (e, t))) := by
          subst ht0
          change
            ((0 = 0 ∧ ambientBoundary ⟨e.1, T.edgeSet_subset e.2⟩ 0 = x.1) ∨
              (0 = 1 ∧ ambientBoundary ⟨e.1, T.edgeSet_subset e.2⟩ 1 = x.1))
          left
          constructor
          · rfl
          · rfl
        have hFiberB :
            inVertexFiber ambientBoundary x.1
              (subgraphRealizationBoundarySourceMap T b) := by
          exact (graphRealizationSetoid_inVertexFiber_iff ambientBoundary x.1 hAmbient).1 hFiberA
        have hSubA : inVertexFiber subgraphBoundary x (Sum.inr (e, t)) := by
          subst ht0
          change
            ((0 = 0 ∧ subgraphBoundary e 0 = x) ∨
              (0 = 1 ∧ subgraphBoundary e 1 = x))
          left
          constructor
          · rfl
          · rfl
        have hSubB : inVertexFiber subgraphBoundary x b := by
          exact (subgraphRealizationBoundarySourceMap_inVertexFiber_iff T x b).mp hFiberB
        exact graphRealizationSetoid_of_inVertexFiber subgraphBoundary x hSubA hSubB
      · by_cases ht1 : t = 1
        · let x : T.verts := ⟨e.1.out.2, T.mem_verts_of_mem_edge e.2 (Sym2.out_snd_mem e.1)⟩
          have hFiberA :
              inVertexFiber ambientBoundary x.1
                (subgraphRealizationBoundarySourceMap T (Sum.inr (e, t))) := by
            subst ht1
            change
              ((1 = 0 ∧ ambientBoundary ⟨e.1, T.edgeSet_subset e.2⟩ 0 = x.1) ∨
                (1 = 1 ∧ ambientBoundary ⟨e.1, T.edgeSet_subset e.2⟩ 1 = x.1))
            right
            constructor
            · rfl
            · rfl
          have hFiberB :
              inVertexFiber ambientBoundary x.1
                (subgraphRealizationBoundarySourceMap T b) := by
            exact (graphRealizationSetoid_inVertexFiber_iff ambientBoundary x.1 hAmbient).1 hFiberA
          have hSubA : inVertexFiber subgraphBoundary x (Sum.inr (e, t)) := by
            subst ht1
            change
              ((1 = 0 ∧ subgraphBoundary e 0 = x) ∨
                (1 = 1 ∧ subgraphBoundary e 1 = x))
            right
            constructor
            · rfl
            · rfl
          have hSubB : inVertexFiber subgraphBoundary x b := by
            exact (subgraphRealizationBoundarySourceMap_inVertexFiber_iff T x b).mp hFiberB
          exact graphRealizationSetoid_of_inVertexFiber subgraphBoundary x hSubA hSubB
        · have hEq :
              subgraphRealizationBoundarySourceMap T b =
                subgraphRealizationBoundarySourceMap T (Sum.inr (e, t)) := by
            simpa [subgraphRealizationBoundarySourceMap] using
              graphRealizationSetoid_interior_eq ambientBoundary
                ⟨e.1, T.edgeSet_subset e.2⟩ t ht0 ht1 hAmbient
          have hbEq : b = Sum.inr (e, t) :=
            subgraphRealizationBoundarySourceMap_injective T hEq
          subst hbEq
          rfl

/-- Helper for Problem 4.6.3: a finite realized graph is plane-embeddable as soon as it admits a
continuous injective map into some already plane-embeddable realization. -/
theorem embeddableInPlane_of_compactContinuousInjective
    {X₁ : Type u} {X₂ : Type*} {J₁ : Type*} {J₂ : Type*}
    (boundary₁ : J₁ ↪ Fin 2 → X₁) (boundary₂ : J₂ ↪ Fin 2 → X₂)
    [FiniteGraph boundary₁]
    (f : graphRealization boundary₁ → graphRealization boundary₂)
    (hfcont :
      let _ : TopologicalSpace (graphRealization boundary₁) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary₁
      let _ : TopologicalSpace (graphRealization boundary₂) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary₂
      Continuous f)
    (hfinj : Function.Injective f)
    (hEmb : embeddableInPlane boundary₂) :
    embeddableInPlane boundary₁ := by
  let _ : TopologicalSpace (graphRealization boundary₁) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary₁
  let _ : TopologicalSpace (graphRealization boundary₂) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary₂
  let _ : CompactSpace (graphRealization boundary₁) := inferInstance
  rcases hEmb with ⟨g, hg⟩
  let _ : T2Space (graphRealization boundary₂) := by
    let _ : T2Space ℝ := OrderClosedTopology.to_t2Space
    let _ : T2Space (ℝ × ℝ) := Prod.t2Space
    exact hg.t2Space
  -- First show the compact source embeds into the intermediate realization itself.
  have hclosed : Topology.IsClosedEmbedding f := by
    refine Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
      hfcont hfinj ?_
    exact hfcont.isClosedMap
  refine ⟨g ∘ f, ?_⟩
  -- Then compose that embedding with the ambient plane embedding.
  exact hg.comp hclosed.isEmbedding

/-- Helper for Problem 4.6.3: any canonical obstruction realized inside a plane-embeddable
canonical graph realization is itself plane-embeddable. -/
theorem embeddableInPlane_of_containsSubgraphRealizationHomeomorphicTo
    {V : Type u} {W : Type*} (graph : SimpleGraph V) (obstruction : SimpleGraph W)
    [FiniteGraph (SimpleGraph.realizationBoundary obstruction)]
    (hEmb : embeddableInPlane (SimpleGraph.realizationBoundary graph))
    (hContains : graph.containsSubgraphRealizationHomeomorphicTo obstruction) :
    embeddableInPlane (SimpleGraph.realizationBoundary obstruction) := by
  let obstructionBoundary := SimpleGraph.realizationBoundary obstruction
  let ambientBoundary := SimpleGraph.realizationBoundary graph
  rcases hContains with ⟨T, hTopo⟩
  rcases hTopo with ⟨hTopo⟩
  let subgraphBoundary := SimpleGraph.Subgraph.realizationBoundary T
  let _ : TopologicalSpace (graphRealization obstructionBoundary) :=
    graphRealizationSourceFaithfulTopologicalSpace obstructionBoundary
  let _ : TopologicalSpace (graphRealization subgraphBoundary) :=
    graphRealizationSourceFaithfulTopologicalSpace subgraphBoundary
  let _ : TopologicalSpace (graphRealization ambientBoundary) :=
    graphRealizationSourceFaithfulTopologicalSpace ambientBoundary
  let f : graphRealization obstructionBoundary → graphRealization ambientBoundary :=
    fun x ↦ subgraphRealizationBoundaryMap T (hTopo.symm x)
  -- Route correction: use the finished quotient-level inclusion and the homeomorphism witness,
  -- rather than reopening the source-level quotient normalization.
  have hfcont : Continuous f := by
    -- First move from the obstruction realization to the realizing subgraph, then include it.
    change Continuous (subgraphRealizationBoundaryMap T ∘ hTopo.symm)
    exact (continuous_subgraphRealizationBoundaryMap T).comp hTopo.symm.continuous
  have hfinj : Function.Injective f := by
    -- Both pieces of the composite remember points faithfully.
    change Function.Injective (subgraphRealizationBoundaryMap T ∘ hTopo.symm)
    exact (injective_subgraphRealizationBoundaryMap T).comp hTopo.symm.injective
  -- The compact obstruction realization therefore embeds in the same plane.
  exact
    embeddableInPlane_of_compactContinuousInjective obstructionBoundary ambientBoundary
      f hfcont hfinj hEmb

/-- Helper for Problem 4.6.3: a plane-embeddable canonical realization cannot contain any
homeomorphic obstruction whose own canonical realization is not plane-embeddable. -/
-- TODO: compose the canonical subgraph-realization inclusion proved above with the homeomorphism
-- witness from `containsSubgraphRealizationHomeomorphicTo`, then use compactness of the finite
-- obstruction realization to upgrade the resulting continuous injection into a plane embedding.
theorem not_containsSubgraphRealizationHomeomorphicTo_of_embeddableInPlane
    {V : Type u} {W : Type*} (graph : SimpleGraph V) (obstruction : SimpleGraph W)
    [FiniteGraph (SimpleGraph.realizationBoundary obstruction)]
    (hEmb : embeddableInPlane (SimpleGraph.realizationBoundary graph))
    (hob : ¬ embeddableInPlane (SimpleGraph.realizationBoundary obstruction)) :
    ¬ graph.containsSubgraphRealizationHomeomorphicTo obstruction := by
  intro hContains
  -- Any such contained obstruction would inherit plane embeddability from the ambient graph.
  exact hob <|
    embeddableInPlane_of_containsSubgraphRealizationHomeomorphicTo
      graph obstruction hEmb hContains

/-- Helper for Problem 4.6.3: the forward half of Kuratowski's criterion is a pair of
specializations of the generic obstruction-monotonicity lemma once the two base obstructions are
known to be non-embeddable. -/
theorem noKuratowskiObstruction_of_embeddableInPlane_of_nonembeddableObstructions
    {V : Type u} (graph : SimpleGraph V)
    [FiniteGraph (SimpleGraph.realizationBoundary (SimpleGraph.completeGraph (Fin 5)))]
    [FiniteGraph (SimpleGraph.realizationBoundary (completeBipartiteGraph (Fin 3) (Fin 3)))]
    (hEmb : embeddableInPlane (SimpleGraph.realizationBoundary graph))
    (hK5 :
      ¬ embeddableInPlane
        (SimpleGraph.realizationBoundary (SimpleGraph.completeGraph (Fin 5))))
    (hK33 :
      ¬ embeddableInPlane
        (SimpleGraph.realizationBoundary (completeBipartiteGraph (Fin 3) (Fin 3)))) :
    ¬ graph.containsSubgraphRealizationHomeomorphicTo (SimpleGraph.completeGraph (Fin 5)) ∧
      ¬ graph.containsSubgraphRealizationHomeomorphicTo
        (completeBipartiteGraph (Fin 3) (Fin 3)) := by
  -- Apply the generic monotonicity lemma to the two classical Kuratowski obstructions.
  constructor
  · exact
      not_containsSubgraphRealizationHomeomorphicTo_of_embeddableInPlane
        graph (SimpleGraph.completeGraph (Fin 5)) hEmb hK5
  · exact
      not_containsSubgraphRealizationHomeomorphicTo_of_embeddableInPlane
        graph (completeBipartiteGraph (Fin 3) (Fin 3)) hEmb hK33

/-- Helper for Problem 4.6.3: every ambient vertex of `graph` lies in the top subgraph. -/
theorem topSubgraph_mem_verts
    {V : Type u} {graph : SimpleGraph V} (x : V) :
    x ∈ (⊤ : graph.Subgraph).verts := by
  simp

/-- Helper for Problem 4.6.3: every ambient edge of `graph` lies in the top subgraph. -/
theorem topSubgraph_mem_edgeSet
    {V : Type u} {graph : SimpleGraph V} (e : graph.edgeSet) :
    (e : Sym2 V) ∈ (⊤ : graph.Subgraph).edgeSet := by
  exact e.2

/-- Helper for Problem 4.6.3: the ambient canonical source identifies with the canonical source of
the top subgraph by rewrapping vertices and edges in the corresponding subtype. -/
noncomputable def ambientToTopSubgraphSource
    {V : Type u} (graph : SimpleGraph V) :
    V ⊕ (graph.edgeSet × I) →
      (⊤ : graph.Subgraph).verts ⊕ (((⊤ : graph.Subgraph).edgeSet) × I)
  | Sum.inl x => Sum.inl ⟨x, topSubgraph_mem_verts (graph := graph) x⟩
  | Sum.inr (e, t) => Sum.inr (⟨e.1, topSubgraph_mem_edgeSet (graph := graph) e⟩, t)

/-- Helper for Problem 4.6.3: rewrapping an ambient endpoint identification in the top subgraph
still gives a valid endpoint identification there. -/
theorem ambientToTopSubgraphSource_rel
    {V : Type u} (graph : SimpleGraph V)
    {a b : V ⊕ (graph.edgeSet × I)}
    (hab : graphRealizationRel (SimpleGraph.realizationBoundary graph) a b) :
    graphRealizationSetoid (SimpleGraph.Subgraph.realizationBoundary (⊤ : graph.Subgraph))
      (ambientToTopSubgraphSource graph a)
      (ambientToTopSubgraphSource graph b) := by
  -- The top subgraph has the same canonical endpoint formulas after adding subtype wrappers.
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
            simpa [ambientToTopSubgraphSource, SimpleGraph.Subgraph.realizationBoundary] using
              graphRealizationSetoid_vertex_boundary_zero
                (SimpleGraph.Subgraph.realizationBoundary (⊤ : graph.Subgraph))
                ⟨e.1, topSubgraph_mem_edgeSet (graph := graph) e⟩
          · rcases hone with ⟨hx, ht⟩
            subst hx
            subst ht
            simpa [ambientToTopSubgraphSource, SimpleGraph.Subgraph.realizationBoundary] using
              graphRealizationSetoid_vertex_boundary_one
                (SimpleGraph.Subgraph.realizationBoundary (⊤ : graph.Subgraph))
                ⟨e.1, topSubgraph_mem_edgeSet (graph := graph) e⟩
  | inr jt =>
      rcases jt with ⟨e, t⟩
      cases b with
      | inl x =>
          rcases hab with hzero | hone
          · rcases hzero with ⟨ht, hx⟩
            subst ht
            subst hx
            simpa [ambientToTopSubgraphSource, SimpleGraph.Subgraph.realizationBoundary] using
              (graphRealizationSetoid_vertex_boundary_zero
                (SimpleGraph.Subgraph.realizationBoundary (⊤ : graph.Subgraph))
                ⟨e.1, topSubgraph_mem_edgeSet (graph := graph) e⟩).symm
          · rcases hone with ⟨ht, hx⟩
            subst ht
            subst hx
            simpa [ambientToTopSubgraphSource, SimpleGraph.Subgraph.realizationBoundary] using
              (graphRealizationSetoid_vertex_boundary_one
                (SimpleGraph.Subgraph.realizationBoundary (⊤ : graph.Subgraph))
                ⟨e.1, topSubgraph_mem_edgeSet (graph := graph) e⟩).symm
      | inr zu =>
          cases hab

/-- Helper for Problem 4.6.3: the ambient-to-top source rewrapping respects the full realization
setoid. -/
theorem ambientToTopSubgraphSource_respects
    {V : Type u} (graph : SimpleGraph V)
    {a b : V ⊕ (graph.edgeSet × I)}
    (hab : graphRealizationSetoid (SimpleGraph.realizationBoundary graph) a b) :
    graphRealizationSetoid (SimpleGraph.Subgraph.realizationBoundary (⊤ : graph.Subgraph))
      (ambientToTopSubgraphSource graph a)
      (ambientToTopSubgraphSource graph b) := by
  -- Extend the relation-level rewrapping to the equivalence closure.
  induction hab with
  | rel _ _ hrel =>
      exact ambientToTopSubgraphSource_rel graph hrel
  | refl a =>
      rfl
  | symm a b hab ih =>
      exact ih.symm
  | trans a b c hab hbc ihab ihbc =>
      exact Relation.EqvGen.trans _ _ _ ihab ihbc

/-- Helper for Problem 4.6.3: rewrapping a top-subgraph source representative into the ambient
source and back is the identity. -/
theorem ambientToTopSubgraphSource_left_inv
    {V : Type u} (graph : SimpleGraph V)
    (z :
      (⊤ : graph.Subgraph).verts ⊕ (((⊤ : graph.Subgraph).edgeSet) × I)) :
    ambientToTopSubgraphSource graph
        (subgraphRealizationBoundarySourceMap (⊤ : graph.Subgraph) z) = z := by
  -- Both summands only forget and then restore the trivial top-subgraph proof.
  cases z with
  | inl x =>
      apply congrArg Sum.inl
      apply Subtype.ext
      rfl
  | inr jt =>
      rcases jt with ⟨e, t⟩
      apply congrArg Sum.inr
      apply Prod.ext
      · apply Subtype.ext
        rfl
      · rfl

/-- Helper for Problem 4.6.3: rewrapping an ambient source representative in the top subgraph and
then forgetting the subtype wrappers recovers the original ambient representative. -/
theorem ambientToTopSubgraphSource_right_inv
    {V : Type u} (graph : SimpleGraph V) (z : V ⊕ (graph.edgeSet × I)) :
    subgraphRealizationBoundarySourceMap (⊤ : graph.Subgraph)
        (ambientToTopSubgraphSource graph z) = z := by
  -- The top-subgraph inclusion is literally the identity on the underlying ambient data.
  cases z with
  | inl x =>
      rfl
  | inr jt =>
      rcases jt with ⟨e, t⟩
      apply congrArg Sum.inr
      apply Prod.ext
      · apply Subtype.ext
        rfl
      · rfl

/-- Helper for Problem 4.6.3: the ambient-to-top source rewrapping is continuous for the
source-faithful source topologies. -/
theorem continuous_ambientToTopSubgraphSource
    {V : Type u} (graph : SimpleGraph V) :
    let _ : TopologicalSpace V := ⊥
    let _ : TopologicalSpace (graph.edgeSet) := ⊥
    let _ : TopologicalSpace ((⊤ : graph.Subgraph).verts) := ⊥
    let _ : TopologicalSpace (((⊤ : graph.Subgraph).edgeSet)) := ⊥
    let _ : TopologicalSpace (V ⊕ (graph.edgeSet × I)) := inferInstance
    let _ : TopologicalSpace
        ((⊤ : graph.Subgraph).verts ⊕ (((⊤ : graph.Subgraph).edgeSet) × I)) := inferInstance
    Continuous (ambientToTopSubgraphSource graph) := by
  let _ : TopologicalSpace V := ⊥
  let _ : TopologicalSpace (graph.edgeSet) := ⊥
  let _ : TopologicalSpace ((⊤ : graph.Subgraph).verts) := ⊥
  let _ : TopologicalSpace (((⊤ : graph.Subgraph).edgeSet)) := ⊥
  let _ : DiscreteTopology V := discreteTopology_bot V
  let _ : DiscreteTopology (graph.edgeSet) := discreteTopology_bot (graph.edgeSet)
  let _ : DiscreteTopology ((⊤ : graph.Subgraph).verts) :=
    discreteTopology_bot ((⊤ : graph.Subgraph).verts)
  let _ : DiscreteTopology (((⊤ : graph.Subgraph).edgeSet)) :=
    discreteTopology_bot (((⊤ : graph.Subgraph).edgeSet))
  let _ : TopologicalSpace (V ⊕ (graph.edgeSet × I)) := inferInstance
  let _ : TopologicalSpace
      ((⊤ : graph.Subgraph).verts ⊕ (((⊤ : graph.Subgraph).edgeSet) × I)) := inferInstance
  -- Each branch is a discrete inclusion together with the unchanged interval coordinate.
  rw [continuous_sum_dom]
  constructor
  · exact continuous_of_discreteTopology
  · have hEdge :
        Continuous
          (fun e : graph.edgeSet ↦
            (⟨e.1, topSubgraph_mem_edgeSet (graph := graph) e⟩ :
              ((⊤ : graph.Subgraph).edgeSet))) :=
        continuous_of_discreteTopology
    have hPair :
        Continuous
          (fun p : graph.edgeSet × I ↦
            ((⟨p.1.1, topSubgraph_mem_edgeSet (graph := graph) p.1⟩ :
                ((⊤ : graph.Subgraph).edgeSet)), p.2)) :=
      (hEdge.comp continuous_fst).prodMk continuous_snd
    simpa [ambientToTopSubgraphSource] using continuous_inr.comp hPair

/-- Helper for Problem 4.6.3: the ambient canonical realization descends to the canonical
realization of the top subgraph by rewrapping source representatives. -/
noncomputable def ambientToTopSubgraphRealizationMap
    {V : Type u} (graph : SimpleGraph V) :
    graphRealization (SimpleGraph.realizationBoundary graph) →
      graphRealization (SimpleGraph.Subgraph.realizationBoundary (⊤ : graph.Subgraph)) :=
  Quotient.map' (ambientToTopSubgraphSource graph)
    (fun _ _ h ↦ ambientToTopSubgraphSource_respects graph h)

/-- Helper for Problem 4.6.3: the descended ambient-to-top quotient map is continuous. -/
theorem continuous_ambientToTopSubgraphRealizationMap
    {V : Type u} (graph : SimpleGraph V) :
    let _ : TopologicalSpace (graphRealization (SimpleGraph.realizationBoundary graph)) :=
      graphRealizationSourceFaithfulTopologicalSpace (SimpleGraph.realizationBoundary graph)
    let _ : TopologicalSpace
        (graphRealization (SimpleGraph.Subgraph.realizationBoundary (⊤ : graph.Subgraph))) :=
      graphRealizationSourceFaithfulTopologicalSpace
        (SimpleGraph.Subgraph.realizationBoundary (⊤ : graph.Subgraph))
    Continuous (ambientToTopSubgraphRealizationMap graph) := by
  let ambientBoundary := SimpleGraph.realizationBoundary graph
  let topBoundary := SimpleGraph.Subgraph.realizationBoundary (⊤ : graph.Subgraph)
  let _ : TopologicalSpace V := ⊥
  let _ : TopologicalSpace (graph.edgeSet) := ⊥
  let _ : TopologicalSpace ((⊤ : graph.Subgraph).verts) := ⊥
  let _ : TopologicalSpace (((⊤ : graph.Subgraph).edgeSet)) := ⊥
  let _ : TopologicalSpace (V ⊕ (graph.edgeSet × I)) := inferInstance
  let _ : TopologicalSpace
      ((⊤ : graph.Subgraph).verts ⊕ (((⊤ : graph.Subgraph).edgeSet) × I)) := inferInstance
  let _ : TopologicalSpace (graphRealization ambientBoundary) :=
    graphRealizationSourceFaithfulTopologicalSpace ambientBoundary
  let _ : TopologicalSpace (graphRealization topBoundary) :=
    graphRealizationSourceFaithfulTopologicalSpace topBoundary
  -- Descend the continuous source rewrapping once through the quotient.
  change Continuous
    (Quotient.map' (ambientToTopSubgraphSource graph)
      (fun a b h ↦ ambientToTopSubgraphSource_respects graph h))
  exact Continuous.quotient_map' (continuous_ambientToTopSubgraphSource graph)
    (fun a b h ↦ ambientToTopSubgraphSource_respects graph h)

/-- Helper for Problem 4.6.3: the canonical realization of the top subgraph is homeomorphic to the
canonical realization of the ambient graph. -/
noncomputable def topSubgraphRealizationHomeomorph
    {V : Type u} (graph : SimpleGraph V) :
    let _ :
        TopologicalSpace
          (graphRealization (SimpleGraph.Subgraph.realizationBoundary (⊤ : graph.Subgraph))) :=
      graphRealizationSourceFaithfulTopologicalSpace
        (SimpleGraph.Subgraph.realizationBoundary (⊤ : graph.Subgraph))
    let _ : TopologicalSpace (graphRealization (SimpleGraph.realizationBoundary graph)) :=
      graphRealizationSourceFaithfulTopologicalSpace (SimpleGraph.realizationBoundary graph)
    graphRealization (SimpleGraph.Subgraph.realizationBoundary (⊤ : graph.Subgraph)) ≃ₜ
      graphRealization (SimpleGraph.realizationBoundary graph) := by
  let topBoundary := SimpleGraph.Subgraph.realizationBoundary (⊤ : graph.Subgraph)
  let ambientBoundary := SimpleGraph.realizationBoundary graph
  let _ : TopologicalSpace (graphRealization topBoundary) :=
    graphRealizationSourceFaithfulTopologicalSpace topBoundary
  let _ : TopologicalSpace (graphRealization ambientBoundary) :=
    graphRealizationSourceFaithfulTopologicalSpace ambientBoundary
  let hEquiv : graphRealization topBoundary ≃ graphRealization ambientBoundary :=
    { toFun := subgraphRealizationBoundaryMap (⊤ : graph.Subgraph)
      invFun := ambientToTopSubgraphRealizationMap graph
      left_inv := by
        intro q
        -- Descend the source-level inverse formula to the top-subgraph quotient.
        refine Quotient.inductionOn q ?_
        intro z
        simpa [subgraphRealizationBoundaryMap, ambientToTopSubgraphRealizationMap] using
          congrArg (Quotient.mk (graphRealizationSetoid topBoundary))
            (ambientToTopSubgraphSource_left_inv graph z)
      right_inv := by
        intro q
        -- The same source-level identity gives the inverse law on the ambient quotient.
        refine Quotient.inductionOn q ?_
        intro z
        simpa [subgraphRealizationBoundaryMap, ambientToTopSubgraphRealizationMap] using
          congrArg (Quotient.mk (graphRealizationSetoid ambientBoundary))
            (ambientToTopSubgraphSource_right_inv graph z) }
  -- Package the quotient equivalence together with continuity of both descended maps.
  refine Homeomorph.mk hEquiv ?_ ?_
  · exact continuous_subgraphRealizationBoundaryMap (⊤ : graph.Subgraph)
  · exact continuous_ambientToTopSubgraphRealizationMap graph

/-- Helper for Problem 4.6.3: every graph contains a canonical subgraph realization homeomorphic
to its own canonical realization, witnessed by the top subgraph. -/
theorem containsSubgraphRealizationHomeomorphicTo_self
    {V : Type u} (graph : SimpleGraph V) :
    graph.containsSubgraphRealizationHomeomorphicTo graph := by
  let topBoundary := SimpleGraph.Subgraph.realizationBoundary (⊤ : graph.Subgraph)
  let obstructionBoundary := SimpleGraph.realizationBoundary graph
  let _ : TopologicalSpace (graphRealization topBoundary) :=
    graphRealizationSourceFaithfulTopologicalSpace topBoundary
  let _ : TopologicalSpace (graphRealization obstructionBoundary) :=
    graphRealizationSourceFaithfulTopologicalSpace obstructionBoundary
  -- Choose `T := ⊤` and use the canonical top-subgraph homeomorphism.
  refine ⟨⊤, ?_⟩
  exact ⟨topSubgraphRealizationHomeomorph graph⟩

/-- Helper for Problem 4.6.3: the canonical realization of a graph on a finite vertex type is a
finite graph. -/
theorem finiteGraph_realizationBoundary_ofFinite
    {V : Type u} (graph : SimpleGraph V) [Finite V] :
    FiniteGraph (SimpleGraph.realizationBoundary graph) := by
  -- `realizationBoundary` uses the ambient vertex type and its edge set, so finite vertices give
  -- finite edges through the ambient `Sym2 V`.
  let _ : Finite (Sym2 V) := by infer_instance
  exact instFiniteGraphOfFinite _

/-- Helper for Problem 4.6.3: any finite chosen realization of `graph` induces finiteness of the
canonical realization boundary of the same graph. -/
theorem finiteGraph_realizationBoundary_ofFiniteGraph
    {V : Type u} (graph : SimpleGraph V) (boundary : graph.edgeSet ↪ Fin 2 → V)
    [FiniteGraph boundary] :
    FiniteGraph (SimpleGraph.realizationBoundary graph) := by
  -- Reuse the finite vertex and edge types already carried by the chosen realization `boundary`.
  let _ : Finite V := FiniteGraph.finiteVertices (boundary := boundary)
  let _ : Finite graph.edgeSet := FiniteGraph.finiteEdges (boundary := boundary)
  exact instFiniteGraphOfFinite (SimpleGraph.realizationBoundary graph)

/-- Helper for Problem 4.6.3: the canonical realization of `K₅` contains itself as the obvious
Kuratowski obstruction. -/
theorem completeGraphFive_containsSelfObstruction :
    (SimpleGraph.completeGraph (Fin 5)).containsSubgraphRealizationHomeomorphicTo
      (SimpleGraph.completeGraph (Fin 5)) := by
  -- Use the top subgraph of `K₅` as the realized obstruction witness.
  exact containsSubgraphRealizationHomeomorphicTo_self (SimpleGraph.completeGraph (Fin 5))

/-- Helper for Problem 4.6.3: the canonical realization of `K_{3,3}` also contains itself as the
second classical Kuratowski obstruction. -/
theorem completeBipartiteGraphThreeThree_containsSelfObstruction :
    (completeBipartiteGraph (Fin 3) (Fin 3)).containsSubgraphRealizationHomeomorphicTo
      (completeBipartiteGraph (Fin 3) (Fin 3)) := by
  -- Again the top subgraph gives the required realized obstruction witness.
  exact containsSubgraphRealizationHomeomorphicTo_self
    (completeBipartiteGraph (Fin 3) (Fin 3))
