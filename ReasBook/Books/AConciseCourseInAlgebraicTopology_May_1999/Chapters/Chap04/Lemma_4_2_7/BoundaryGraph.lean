import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Homotopy.Path
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Definition_4_1_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Lemma_4_2_7.SourceFaithfulTree

open scoped unitInterval
open SimpleGraph

universe u v

variable {X₀ : Type u} {J : Type v}

noncomputable section

/-- Helper for Lemma 4.2.7: the simple graph on `X₀` whose edges are the nondegenerate unordered
endpoint pairs carried by `boundary`. -/
def boundaryGraph (boundary : J ↪ Fin 2 → X₀) : SimpleGraph X₀ where
  Adj x y := x ≠ y ∧ ∃ j : J, Sym2.mk (boundary j 0) (boundary j 1) = Sym2.mk x y
  symm := by
    intro x y hxy
    rcases hxy with ⟨hneq, ⟨j, hj⟩⟩
    exact ⟨hneq.symm, ⟨j, hj.trans Sym2.eq_swap⟩⟩
  loopless := ⟨fun x hxx ↦ hxx.1 rfl⟩

/-- Helper for Lemma 4.2.7: unpacking adjacency in `boundaryGraph boundary` gives a nondegenerate
edge of `boundary` whose endpoints are exactly the two adjacent vertices. -/
theorem boundaryGraph_adj_iff (boundary : J ↪ Fin 2 → X₀) (x y : X₀) :
    (boundaryGraph boundary).Adj x y ↔
      x ≠ y ∧ ∃ j : J, Sym2.mk (boundary j 0) (boundary j 1) = Sym2.mk x y :=
  Iff.rfl

/-- Helper for Lemma 4.2.7: an adjacency in `boundaryGraph boundary` determines the corresponding
realized edge path between the two endpoint vertices. -/
def boundaryGraphAdjPath (boundary : J ↪ Fin 2 → X₀) {u v : X₀}
    (h : (boundaryGraph boundary).Adj u v) :
    let _ : TopologicalSpace (graphRealization boundary) :=
      graphRealizationSourceFaithfulTopologicalSpace boundary
    _root_.Path (graphVertex boundary u) (graphVertex boundary v) := by
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  classical
  change u ≠ v ∧ ∃ j : J, Sym2.mk (boundary j 0) (boundary j 1) = Sym2.mk u v at h
  let j : J := Classical.choose h.2
  let hj : Sym2.mk (boundary j 0) (boundary j 1) = Sym2.mk u v := Classical.choose_spec h.2
  by_cases h0 : boundary j 0 = u
  · have h1 : boundary j 1 = v := by
      have hor :
          (boundary j 0 = u ∧ boundary j 1 = v) ∨
            (boundary j 0 = v ∧ boundary j 1 = u) :=
        Sym2.eq_iff.mp hj
      rcases hor with hdir | hrev
      · exact hdir.2
      · exact (h.1 (h0.symm.trans hrev.1)).elim
    refine
      { toFun := graphEdgePoint boundary j
        continuous_toFun := ?_
        source' := ?_
        target' := ?_ }
    · let _ : TopologicalSpace X₀ := ⊥
      let _ : TopologicalSpace J := ⊥
      have hsource :
          Continuous (fun t : I ↦ (Sum.inr (j, t) : X₀ ⊕ (J × I))) := by
        simpa using
          (continuous_inr.comp
            (continuous_const.prodMk continuous_id) :
              Continuous (fun t : I ↦ (Sum.inr (j, t) : X₀ ⊕ (J × I))))
      simpa [graphEdgePoint, graphRealizationPoint] using continuous_quotient_mk'.comp hsource
    · simpa [h0] using (graphVertex_boundary_zero_eq_graphEdgePoint_zero boundary j).symm
    · simpa [h1] using (graphVertex_boundary_one_eq_graphEdgePoint_one boundary j).symm
  · have h0' : boundary j 0 = v := by
      have hor :
          (boundary j 0 = u ∧ boundary j 1 = v) ∨
            (boundary j 0 = v ∧ boundary j 1 = u) :=
        Sym2.eq_iff.mp hj
      rcases hor with hdir | hrev
      · exact (h0 hdir.1).elim
      · exact hrev.1
    have h1' : boundary j 1 = u := by
      have hor :
          (boundary j 0 = u ∧ boundary j 1 = v) ∨
            (boundary j 0 = v ∧ boundary j 1 = u) :=
        Sym2.eq_iff.mp hj
      rcases hor with hdir | hrev
      · exact (h0 hdir.1).elim
      · exact hrev.2
    refine
      { toFun := fun t ↦ graphEdgePoint boundary j (σ t)
        continuous_toFun := ?_
        source' := ?_
        target' := ?_ }
    · let _ : TopologicalSpace X₀ := ⊥
      let _ : TopologicalSpace J := ⊥
      have hsource :
          Continuous (fun t : I ↦ (Sum.inr (j, σ t) : X₀ ⊕ (J × I))) := by
        simpa using
          (continuous_inr.comp
            (continuous_const.prodMk unitInterval.continuous_symm) :
              Continuous (fun t : I ↦ (Sum.inr (j, σ t) : X₀ ⊕ (J × I))))
      simpa [graphEdgePoint, graphRealizationPoint] using continuous_quotient_mk'.comp hsource
    · simpa [h1'] using (graphVertex_boundary_one_eq_graphEdgePoint_one boundary j).symm
    · simpa [h0'] using (graphVertex_boundary_zero_eq_graphEdgePoint_zero boundary j).symm

/-- Helper for Lemma 4.2.7: a walk in `boundaryGraph boundary` induces a path in the realization
by traversing the corresponding realized edges in order. -/
def boundaryGraphWalkPath (boundary : J ↪ Fin 2 → X₀) {u v : X₀} :
    (boundaryGraph boundary).Walk u v →
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      _root_.Path (graphVertex boundary u) (graphVertex boundary v)
  := by
    let _ : TopologicalSpace (graphRealization boundary) :=
      graphRealizationSourceFaithfulTopologicalSpace boundary
    intro w
    induction w with
    | nil => exact _root_.Path.refl _
    | @cons tail u' v' h p ih =>
        exact _root_.Path.trans (boundaryGraphAdjPath boundary h) ih

/-- Helper for Lemma 4.2.7: an adjacency in `boundaryGraph boundary` can be represented by an
oriented edge whose realized endpoints are the corresponding graph vertices. -/
theorem boundaryGraph_adj_exists_orientedEdge
    (boundary : J ↪ Fin 2 → X₀) {u v : X₀} (h : (boundaryGraph boundary).Adj u v) :
    ∃ k : OrientedEdge boundary,
      k.initialVertex = graphVertex boundary u ∧
        k.terminalVertex = graphVertex boundary v := by
  rcases h with ⟨hneq, ⟨j, hj⟩⟩
  rcases Sym2.eq_iff.mp hj with hdir | hrev
  · refine ⟨⟨j, .forward⟩, ?_, ?_⟩
    · simp [hdir.1]
    · simp [hdir.2]
  · refine ⟨⟨j, .backward⟩, ?_, ?_⟩
    · simp [hrev.2]
    · simp [hrev.1]

/-- Helper for Lemma 4.2.7: the `n`th edge of a walk is the unoriented edge joining the `n`th and
`(n+1)`st visited vertices. -/
theorem walk_edges_getElem_eq_sym2 {G : SimpleGraph X₀} {u v : X₀} (w : G.Walk u v)
    (n : ℕ) (hn : n < w.edges.length) :
    w.edges[n] = Sym2.mk (w.getVert n) (w.getVert (n + 1)) := by
  have hdart :=
    congrArg SimpleGraph.Dart.edge (w.darts_getElem_eq_getVert n (by simpa using hn))
  simpa [SimpleGraph.Walk.edges] using hdart

/-- Helper for Lemma 4.2.7: in a source-faithful tree realization, an edge cannot have
coincident endpoints, since that single oriented edge would already give a closed reduced edge
path. -/
theorem boundary_ne_endpoints (boundary : J ↪ Fin 2 → X₀) [SourceFaithfulIsTree boundary]
    (j : J) :
    boundary j 0 ≠ boundary j 1 := by
  intro hdeg
  let p : EdgePath boundary :=
    { length := 0
      toEdge := fun _ ↦ ⟨j, .forward⟩
      composable := fun m ↦ Fin.elim0 m }
  have hpClosed : p.IsClosed := by
    simp [EdgePath.IsClosed, EdgePath.initialVertex, EdgePath.terminalVertex, p, hdeg]
  have hpReduced : p.Reduced := by
    intro m
    exact Fin.elim0 m
  exact ‹SourceFaithfulIsTree boundary›.not_reduced_of_isClosed p hpClosed hpReduced

/-- Helper for Lemma 4.2.7: a source-faithful tree realization has an actual vertex witness
in `X₀`. -/
theorem nonempty_vertex_of_isTree (boundary : J ↪ Fin 2 → X₀) [SourceFaithfulIsTree boundary] :
    Nonempty X₀ := by
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  let _ : Nonempty (graphRealization boundary) := inferInstance
  rcases ‹Nonempty (graphRealization boundary)› with ⟨x⟩
  refine Quotient.inductionOn x ?_
  intro z
  cases z with
  | inl x => exact ⟨x⟩
  | inr jt => exact ⟨boundary jt.1 0⟩

/-- Helper for Lemma 4.2.7: the two endpoints of each boundary edge lie in the same connected
component of `boundaryGraph boundary`. -/
theorem boundaryGraph_endpointComponentEq (boundary : J ↪ Fin 2 → X₀)
    [SourceFaithfulIsTree boundary] (j : J) :
    (boundaryGraph boundary).connectedComponentMk (boundary j 0) =
      (boundaryGraph boundary).connectedComponentMk (boundary j 1) := by
  exact ConnectedComponent.connectedComponentMk_eq_of_adj
    ⟨boundary_ne_endpoints boundary j, ⟨j, rfl⟩⟩

/-- Helper for Lemma 4.2.7: before descending to the quotient realization, a source
representative already determines a connected component of `boundaryGraph boundary`. -/
def boundaryGraphComponentSource (boundary : J ↪ Fin 2 → X₀) [SourceFaithfulIsTree boundary] :
    X₀ ⊕ (J × I) → (boundaryGraph boundary).ConnectedComponent
  | .inl x => (boundaryGraph boundary).connectedComponentMk x
  | .inr (j, _) => (boundaryGraph boundary).connectedComponentMk (boundary j 0)

/-- Helper for Lemma 4.2.7: the connected-component label on source representatives respects a
single generating endpoint identification in the realization quotient. -/
theorem boundaryGraphComponentSource_rel (boundary : J ↪ Fin 2 → X₀)
    [SourceFaithfulIsTree boundary] {a b : X₀ ⊕ (J × I)}
    (hab : graphRealizationRel boundary a b) :
    boundaryGraphComponentSource boundary a = boundaryGraphComponentSource boundary b := by
  cases a with
  | inl x =>
      cases b with
      | inl y => cases hab
      | inr jt =>
          rcases jt with ⟨j, t⟩
          rcases hab with (⟨hx, ht⟩ | ⟨hx, ht⟩)
          · subst hx
            subst t
            rfl
          · subst hx
            subst t
            exact ConnectedComponent.connectedComponentMk_eq_of_adj
              ⟨(boundary_ne_endpoints boundary j).symm, ⟨j, Sym2.eq_swap⟩⟩
  | inr jt =>
      rcases jt with ⟨j, t⟩
      cases b with
      | inl x =>
          rcases hab with (⟨ht, hx⟩ | ⟨ht, hx⟩)
          · subst hx
            subst t
            rfl
          · subst hx
            subst t
            exact ConnectedComponent.connectedComponentMk_eq_of_adj
              ⟨boundary_ne_endpoints boundary j, ⟨j, rfl⟩⟩
      | inr jt' => cases hab

/-- Helper for Lemma 4.2.7: the connected-component label on source representatives respects the
full realization setoid generated by the endpoint identifications. -/
theorem boundaryGraphComponentSource_setoid (boundary : J ↪ Fin 2 → X₀)
    [SourceFaithfulIsTree boundary] {a b : X₀ ⊕ (J × I)}
    (hab : graphRealizationSetoid boundary a b) :
    boundaryGraphComponentSource boundary a = boundaryGraphComponentSource boundary b := by
  induction hab with
  | rel _ _ hrel =>
      exact boundaryGraphComponentSource_rel boundary hrel
  | refl a =>
      rfl
  | symm a b hab ih =>
      exact ih.symm
  | trans a b c hab hbc ih₁ ih₂ =>
      exact ih₁.trans ih₂

/-- Helper for Lemma 4.2.7: the connected-component label descends from source representatives to
the quotient realization `graphRealization boundary`. -/
def boundaryGraphComponentMap (boundary : J ↪ Fin 2 → X₀) [SourceFaithfulIsTree boundary] :
    graphRealization boundary → (boundaryGraph boundary).ConnectedComponent :=
  Quotient.lift (boundaryGraphComponentSource boundary)
    (fun _ _ hab ↦ boundaryGraphComponentSource_setoid boundary hab)

/-- Helper for Lemma 4.2.7: a realized vertex maps to its own connected component in
`boundaryGraph boundary`. -/
@[simp]
theorem boundaryGraphComponentMap_graphVertex (boundary : J ↪ Fin 2 → X₀)
    [SourceFaithfulIsTree boundary] (x : X₀) :
    boundaryGraphComponentMap boundary (graphVertex boundary x) =
      (boundaryGraph boundary).connectedComponentMk x :=
  rfl

/-- Helper for Lemma 4.2.7: a realized edge point maps to the connected component of the edge's
initial endpoint, which also equals that of the terminal endpoint in a tree. -/
@[simp]
theorem boundaryGraphComponentMap_graphEdgePoint (boundary : J ↪ Fin 2 → X₀)
    [SourceFaithfulIsTree boundary] (j : J) (t : I) :
    boundaryGraphComponentMap boundary (graphEdgePoint boundary j t) =
      (boundaryGraph boundary).connectedComponentMk (boundary j 0) :=
  rfl

/-- Helper for Lemma 4.2.7: the auxiliary simple graph `boundaryGraph boundary` is connected.
If the quotient realization carries a continuous map to the discrete connected-component type, then
preconnectedness of the realization forces that component label to be constant, hence every vertex
lies in one graph component. -/
theorem boundaryGraph_connected_of_componentMap_continuous
    (boundary : J ↪ Fin 2 → X₀) [SourceFaithfulIsTree boundary]
    (hmap :
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      let _ : TopologicalSpace ((boundaryGraph boundary).ConnectedComponent) := ⊥
      Continuous (boundaryGraphComponentMap boundary)) :
    (boundaryGraph boundary).Connected := by
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  classical
  obtain ⟨v⟩ := nonempty_vertex_of_isTree boundary
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨v, fun w ↦ ?_⟩
  let _ : TopologicalSpace ((boundaryGraph boundary).ConnectedComponent) := ⊥
  let _ : DiscreteTopology ((boundaryGraph boundary).ConnectedComponent) := ⟨rfl⟩
  have hmap' : Continuous (boundaryGraphComponentMap boundary) := by
    simpa using hmap
  have hconst :
      boundaryGraphComponentMap boundary (graphVertex boundary w) =
        boundaryGraphComponentMap boundary (graphVertex boundary v) := by
    exact (inferInstance : PreconnectedSpace (graphRealization boundary)).constant hmap'
  have hcomponent :
      (boundaryGraph boundary).connectedComponentMk v =
        (boundaryGraph boundary).connectedComponentMk w := by
    simpa using hconst.symm
  exact ConnectedComponent.eq.mp hcomponent

/-- Helper for Lemma 4.2.7: before quotienting, each connected-component fiber of the source
label map is open in the disjoint-union source. -/
theorem boundaryGraphComponentSource_fiber_isOpen
    (boundary : J ↪ Fin 2 → X₀) [SourceFaithfulIsTree boundary]
    (c : (boundaryGraph boundary).ConnectedComponent) :
    let _ : TopologicalSpace X₀ := ⊥
    let _ : TopologicalSpace J := ⊥
    IsOpen {z : X₀ ⊕ (J × I) | boundaryGraphComponentSource boundary z = c} := by
  let _ : TopologicalSpace X₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  let _ : DiscreteTopology X₀ := discreteTopology_bot X₀
  let _ : DiscreteTopology J := discreteTopology_bot J
  rw [isOpen_sum_iff]
  constructor
  · change IsOpen {x : X₀ | boundaryGraphComponentSource boundary (Sum.inl x) = c}
    change IsOpen {x : X₀ | (boundaryGraph boundary).connectedComponentMk x = c}
    exact
      @isOpen_discrete X₀ ⊥ (discreteTopology_bot X₀)
        {x : X₀ | (boundaryGraph boundary).connectedComponentMk x = c}
  · change IsOpen {p : J × I | boundaryGraphComponentSource boundary (Sum.inr p) = c}
    have hEq :
        {p : J × I | boundaryGraphComponentSource boundary (Sum.inr p) = c} =
          {j : J | (boundaryGraph boundary).connectedComponentMk (boundary j 0) = c} ×ˢ
            (Set.univ : Set I) := by
      ext p
      rcases p with ⟨j, t⟩
      simp [boundaryGraphComponentSource]
    rw [hEq]
    have hJOpen :
        IsOpen {j : J | (boundaryGraph boundary).connectedComponentMk (boundary j 0) = c} := by
      exact
        @isOpen_discrete J ⊥ (discreteTopology_bot J)
          {j : J | (boundaryGraph boundary).connectedComponentMk (boundary j 0) = c}
    exact hJOpen.prod isOpen_univ

/-- Helper for Lemma 4.2.7: pulling a realization-level component fiber back along the quotient
map recovers the corresponding source-level fiber. -/
theorem boundaryGraphComponentFiber_preimage
    (boundary : J ↪ Fin 2 → X₀) [SourceFaithfulIsTree boundary]
    (c : (boundaryGraph boundary).ConnectedComponent) :
    (@Quotient.mk' (X₀ ⊕ (J × I)) (graphRealizationSetoid boundary)) ⁻¹'
        {x : graphRealization boundary | boundaryGraphComponentMap boundary x = c} =
      {z : X₀ ⊕ (J × I) | boundaryGraphComponentSource boundary z = c} := by
  ext z
  rfl

/-- Helper for Lemma 4.2.7: every realization-level connected-component fiber of
`boundaryGraphComponentMap boundary` is open for the source-faithful realization topology. -/
theorem boundaryGraphComponentFiber_isOpen
    (boundary : J ↪ Fin 2 → X₀) [SourceFaithfulIsTree boundary]
    (c : (boundaryGraph boundary).ConnectedComponent) :
    let _ : TopologicalSpace (graphRealization boundary) :=
      graphRealizationSourceFaithfulTopologicalSpace boundary
    IsOpen {x : graphRealization boundary | boundaryGraphComponentMap boundary x = c} := by
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  let _ : TopologicalSpace X₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  -- The realization fiber is open because its quotient-map preimage is exactly the open source
  -- fiber proved above.
  have hpreimageOpen :
      IsOpen ((@Quotient.mk' (X₀ ⊕ (J × I)) (graphRealizationSetoid boundary)) ⁻¹'
        {x : graphRealization boundary | boundaryGraphComponentMap boundary x = c}) := by
    rw [boundaryGraphComponentFiber_preimage]
    exact boundaryGraphComponentSource_fiber_isOpen boundary c
  exact
    (isQuotientMap_quotient_mk'.isOpen_preimage
      (s := {x : graphRealization boundary | boundaryGraphComponentMap boundary x = c})).1
      hpreimageOpen

/-- Helper for Lemma 4.2.7: the auxiliary simple graph `boundaryGraph boundary` is connected.
The proof descends the "which connected component am I in?" map from the realization source to the
quotient realization and then uses connectedness of the tree realization to show that map is
constant. -/
theorem boundaryGraph_connected (boundary : J ↪ Fin 2 → X₀) [SourceFaithfulIsTree boundary] :
    (boundaryGraph boundary).Connected := by
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  have hmap :
      let _ : TopologicalSpace ((boundaryGraph boundary).ConnectedComponent) := ⊥
      Continuous (boundaryGraphComponentMap boundary) := by
    let _ : TopologicalSpace ((boundaryGraph boundary).ConnectedComponent) := ⊥
    refine continuous_def.2 ?_
    intro s _
    have hpreimage :
        boundaryGraphComponentMap boundary ⁻¹' s =
          ⋃ z : s, {x : graphRealization boundary | boundaryGraphComponentMap boundary x = z} := by
      ext x
      constructor
      · intro hx
        exact Set.mem_iUnion.2 ⟨⟨boundaryGraphComponentMap boundary x, hx⟩, by simp⟩
      · intro hx
        rcases Set.mem_iUnion.1 hx with ⟨z, hz⟩
        change boundaryGraphComponentMap boundary x ∈ s
        exact hz.symm ▸ z.property
    rw [hpreimage]
    exact isOpen_iUnion (fun z : s ↦ boundaryGraphComponentFiber_isOpen boundary z)
  exact boundaryGraph_connected_of_componentMap_continuous boundary hmap
