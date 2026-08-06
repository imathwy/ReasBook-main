import Mathlib.Topology.Compactness.Compact
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Definition_4_1_4.FiniteGraph

open Topology
open scoped unitInterval

universe u v

variable {X₀ : Type u} {J : Type v}

-- Semantic recall: `Finite.compactSpace`, `finite_of_compact_of_discrete`, and
-- `Quotient.compactSpace` are the compactness primitives behind this graph realization criterion.

/-- Helper for Definition 4.1.4: the quotient map presenting `graphRealization boundary`. -/
abbrev graphQuotientMap (boundary : J ↪ Fin 2 → X₀) :
    X₀ ⊕ (J × I) → graphRealization boundary :=
  @Quotient.mk' (X₀ ⊕ (J × I)) (graphRealizationSetoid boundary)

/-- Helper for Definition 4.1.4: the source points identified with the vertex `x`. -/
def inVertexFiber (boundary : J ↪ Fin 2 → X₀) (x : X₀) : X₀ ⊕ (J × I) → Prop
  | Sum.inl y => y = x
  | Sum.inr (j, t) => (t = 0 ∧ boundary j 0 = x) ∨ (t = 1 ∧ boundary j 1 = x)

/-- Helper for Definition 4.1.4: one generating endpoint identification preserves the predicate
of lying in the source fiber of the vertex `x`. -/
theorem graphRealizationRel_inVertexFiber_iff (boundary : J ↪ Fin 2 → X₀) (x : X₀)
    {a b : X₀ ⊕ (J × I)} (hab : graphRealizationRel boundary a b) :
    inVertexFiber boundary x a ↔ inVertexFiber boundary x b := by
  cases a with
  | inl y =>
      cases b with
      | inl z =>
          cases hab
      | inr jt =>
          rcases jt with ⟨j, t⟩
          rcases hab with h | h
          · rcases h with ⟨hy, ht⟩
            subst hy
            subst ht
            -- This is exactly the endpoint relation at `0`.
            simp [inVertexFiber]
          · rcases h with ⟨hy, ht⟩
            subst hy
            subst ht
            -- This is exactly the endpoint relation at `1`.
            simp [inVertexFiber]
  | inr jt =>
      rcases jt with ⟨j, t⟩
      cases b with
      | inl y =>
          rcases hab with h | h
          · rcases h with ⟨ht, hy⟩
            subst ht
            subst hy
            -- This is exactly the endpoint relation at `0`.
            simp [inVertexFiber]
          · rcases h with ⟨ht, hy⟩
            subst ht
            subst hy
            -- This is exactly the endpoint relation at `1`.
            simp [inVertexFiber]
      | inr zu =>
          cases hab

/-- Helper for Definition 4.1.4: the generated quotient relation preserves the source fiber of a
fixed vertex. -/
theorem graphRealizationSetoid_inVertexFiber_iff (boundary : J ↪ Fin 2 → X₀) (x : X₀)
    {a b : X₀ ⊕ (J × I)} (hab : graphRealizationSetoid boundary a b) :
    inVertexFiber boundary x a ↔ inVertexFiber boundary x b := by
  induction hab with
  | rel _ _ hrel =>
      exact graphRealizationRel_inVertexFiber_iff boundary x hrel
  | refl a =>
      simp
  | symm a b hab ih =>
      exact ih.symm
  | trans a b c hab hbc ih₁ ih₂ =>
      exact ih₁.trans ih₂

/-- Helper for Definition 4.1.4: every source representative of `graphVertex boundary x` is either
the vertex itself or one of the two edge endpoints incident to it. -/
theorem graphRealizationSetoid_vertex_cases (boundary : J ↪ Fin 2 → X₀) (x : X₀)
    {z : X₀ ⊕ (J × I)} (hz : graphRealizationSetoid boundary (Sum.inl x) z) :
    z = Sum.inl x ∨ (∃ j, z = Sum.inr (j, 0) ∧ boundary j 0 = x) ∨
      ∃ j, z = Sum.inr (j, 1) ∧ boundary j 1 = x := by
  -- Transport the vertex-fiber predicate across the generated setoid.
  have hz' : inVertexFiber boundary x z := by
    exact (graphRealizationSetoid_inVertexFiber_iff boundary x hz).1 (by simp [inVertexFiber])
  cases z with
  | inl y =>
      -- On the vertex side the predicate says exactly `y = x`.
      left
      simpa [inVertexFiber] using hz'
  | inr jt =>
      rcases jt with ⟨j, t⟩
      -- On the edge side the predicate forces one of the two endpoints.
      have hz'' :
          (t = 0 ∧ boundary j 0 = x) ∨ (t = 1 ∧ boundary j 1 = x) := by
        simpa [inVertexFiber] using hz'
      rcases hz'' with ⟨ht, hx⟩ | ⟨ht, hx⟩
      · subst ht
        exact Or.inr (Or.inl ⟨j, rfl, hx⟩)
      · subst ht
        exact Or.inr (Or.inr ⟨j, rfl, hx⟩)

/-- Helper for Definition 4.1.4: a single generating endpoint identification cannot move a chosen
interior point of an edge. -/
theorem graphRealizationRel_edgeInterior_eq_iff (boundary : J ↪ Fin 2 → X₀) (j : J) (t : I)
    (ht₀ : t ≠ 0) (ht₁ : t ≠ 1) {a b : X₀ ⊕ (J × I)}
    (hab : graphRealizationRel boundary a b) :
    a = Sum.inr (j, t) ↔ b = Sum.inr (j, t) := by
  constructor
  · intro ha
    subst ha
    cases b with
    | inl x =>
        rcases hab with (⟨hzero, _⟩ | ⟨hone, _⟩)
        · exact (ht₀ hzero).elim
        · exact (ht₁ hone).elim
    | inr jt =>
        cases hab
  · intro hb
    subst hb
    cases a with
    | inl x =>
        rcases hab with (⟨_, hzero⟩ | ⟨_, hone⟩)
        · exact (ht₀ hzero).elim
        · exact (ht₁ hone).elim
    | inr jt =>
        cases hab

/-- Helper for Definition 4.1.4: the full quotient relation preserves the proposition that a
source point is the chosen interior point `(j, t)`. -/
theorem graphRealizationSetoid_interior_eq_iff (boundary : J ↪ Fin 2 → X₀) (j : J) (t : I)
    (ht₀ : t ≠ 0) (ht₁ : t ≠ 1) {a b : X₀ ⊕ (J × I)}
    (hab : graphRealizationSetoid boundary a b) :
    a = Sum.inr (j, t) ↔ b = Sum.inr (j, t) := by
  induction hab with
  | rel _ _ hrel =>
      exact graphRealizationRel_edgeInterior_eq_iff boundary j t ht₀ ht₁ hrel
  | refl a =>
      simp
  | symm a b hab ih =>
      exact ih.symm
  | trans a b c hab hbc ih₁ ih₂ =>
      exact ih₁.trans ih₂

/-- Helper for Definition 4.1.4: an interior edge point is fixed by the generated quotient
relation. -/
theorem graphRealizationSetoid_interior_eq (boundary : J ↪ Fin 2 → X₀) (j : J) (t : I)
    (ht₀ : t ≠ 0) (ht₁ : t ≠ 1) {z : X₀ ⊕ (J × I)}
    (hz : graphRealizationSetoid boundary (Sum.inr (j, t)) z) :
    z = Sum.inr (j, t) := by
  -- Apply the invariant characterization to the distinguished representative.
  exact (graphRealizationSetoid_interior_eq_iff boundary j t ht₀ ht₁ hz).1 rfl

/-- Helper for Definition 4.1.4: the midpoint `1 / 2` belongs to `I`. -/
theorem oneHalf_mem_unitInterval : ((1 / 2 : ℝ) ∈ (I : Set ℝ)) := by
  -- The midpoint lies between the two endpoints of the unit interval.
  constructor <;> norm_num

/-- Helper for Definition 4.1.4: the fixed interior point used to recover the edge index set from
the realization. -/
noncomputable def graphMidpoint : I :=
  ⟨(1 / 2 : ℝ), oneHalf_mem_unitInterval⟩

/-- Helper for Definition 4.1.4: the chosen midpoint is not the endpoint `0`. -/
theorem graphMidpoint_ne_zero : graphMidpoint ≠ 0 := by
  intro h
  have h' : ((graphMidpoint : I) : ℝ) = 0 := by
    simpa using congrArg (fun t : I ↦ (t : ℝ)) h
  norm_num [graphMidpoint] at h'

/-- Helper for Definition 4.1.4: the chosen midpoint is not the endpoint `1`. -/
theorem graphMidpoint_ne_one : graphMidpoint ≠ 1 := by
  intro h
  have h' : ((graphMidpoint : I) : ℝ) = 1 := by
    simpa using congrArg (fun t : I ↦ (t : ℝ)) h
  norm_num [graphMidpoint] at h'

/-- Helper for Definition 4.1.4: the quotient preimage of the image of a vertex subset is the
corresponding subset of vertices together with all incident identified endpoints. -/
theorem graphVertex_preimage_image (boundary : J ↪ Fin 2 → X₀) (s : Set X₀) :
    graphQuotientMap boundary ⁻¹' (graphVertex boundary '' s) =
      Sum.inl '' s ∪
        Sum.inr '' {p : J × I |
          (p.2 = 0 ∧ boundary p.1 0 ∈ s) ∨ (p.2 = 1 ∧ boundary p.1 1 ∈ s)} := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨x, hx, hEq⟩
    -- Convert equality in the quotient into a source-level setoid relation.
    have hsetoid : graphRealizationSetoid boundary (Sum.inl x) z := by
      have hEq' : graphQuotientMap boundary (Sum.inl x) = graphQuotientMap boundary z := by
        simpa [graphVertex, graphRealizationPoint, graphQuotientMap] using hEq
      exact Quotient.eq'.1 hEq'
    rcases graphRealizationSetoid_vertex_cases boundary x hsetoid with h | h | h
    · left
      exact ⟨x, hx, h.symm⟩
    · rcases h with ⟨j, hzj, hjx⟩
      right
      refine ⟨(j, 0), Or.inl ⟨rfl, ?_⟩, hzj.symm⟩
      simpa [hjx] using hx
    · rcases h with ⟨j, hzj, hjx⟩
      right
      refine ⟨(j, 1), Or.inr ⟨rfl, ?_⟩, hzj.symm⟩
      simpa [hjx] using hx
  · intro hz
    rcases hz with hz | hz
    · rcases hz with ⟨x, hx, rfl⟩
      -- A source vertex maps to its own quotient image.
      exact ⟨x, hx, rfl⟩
    · rcases hz with ⟨⟨j, t⟩, hmem, rfl⟩
      rcases hmem with (⟨ht, hs⟩ | ⟨ht, hs⟩)
      · subst ht
        -- Endpoint `0` is identified with the initial vertex.
        refine ⟨boundary j 0, hs, ?_⟩
        simpa [graphEdgePoint, graphRealizationPoint, graphQuotientMap] using
          graphVertex_boundary_zero_eq_graphEdgePoint_zero boundary j
      · subst ht
        -- Endpoint `1` is identified with the terminal vertex.
        refine ⟨boundary j 1, hs, ?_⟩
        simpa [graphEdgePoint, graphRealizationPoint, graphQuotientMap] using
          graphVertex_boundary_one_eq_graphEdgePoint_one boundary j

/-- Helper for Definition 4.1.4: the quotient preimage of the chosen midpoint section is exactly
the corresponding midpoint copy of the edge index set. -/
theorem graphMidpoint_preimage_image (boundary : J ↪ Fin 2 → X₀) (m : I)
    (hm₀ : m ≠ 0) (hm₁ : m ≠ 1) (s : Set J) :
    graphQuotientMap boundary ⁻¹' ((fun j : J ↦ graphEdgePoint boundary j m) '' s) =
      Sum.inr '' {p : J × I | p.1 ∈ s ∧ p.2 = m} := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨j, hj, hEq⟩
    -- Equality in the quotient forces equality of the interior representatives.
    have hsetoid : graphRealizationSetoid boundary (Sum.inr (j, m)) z := by
      have hEq' : graphQuotientMap boundary (Sum.inr (j, m)) = graphQuotientMap boundary z := by
        simpa [graphEdgePoint, graphRealizationPoint, graphQuotientMap] using hEq
      exact Quotient.eq'.1 hEq'
    have hzEq : z = Sum.inr (j, m) :=
      graphRealizationSetoid_interior_eq boundary j m hm₀ hm₁ hsetoid
    exact ⟨(j, m), ⟨hj, rfl⟩, hzEq.symm⟩
  · intro hz
    rcases hz with ⟨⟨j, t⟩, hmem, rfl⟩
    rcases hmem with ⟨hj, ht⟩
    subst ht
    -- Each chosen midpoint source representative maps to the expected quotient point.
    exact ⟨j, hj, rfl⟩

/-- Helper for Definition 4.1.4: with discrete source topologies on vertices and edges, the
vertex map into the realization is a closed embedding. -/
theorem graphVertex_isClosedEmbedding (boundary : J ↪ Fin 2 → X₀) :
    let _ : TopologicalSpace X₀ := ⊥
    let _ : TopologicalSpace J := ⊥
    let _ : TopologicalSpace (graphRealization boundary) :=
      graphRealizationSourceFaithfulTopologicalSpace boundary
    Topology.IsClosedEmbedding (graphVertex boundary) := by
  let _ : TopologicalSpace X₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  let _ : DiscreteTopology X₀ := discreteTopology_bot X₀
  let _ : DiscreteTopology J := discreteTopology_bot J
  refine Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap ?_ ?_ ?_
  · -- The vertex map is the quotient map composed with the left inclusion.
    simpa [graphVertex, graphRealizationPoint, graphQuotientMap] using
      (continuous_quotient_mk' : Continuous (graphQuotientMap boundary)).comp continuous_inl
  · intro x y hxy
    -- Quotient equality between vertices can only come from the same source vertex.
    have hsetoid : graphRealizationSetoid boundary (Sum.inl x) (Sum.inl y) := by
      have hEq' :
          graphQuotientMap boundary (Sum.inl x) = graphQuotientMap boundary (Sum.inl y) := by
        simpa [graphVertex, graphRealizationPoint, graphQuotientMap] using hxy
      exact Quotient.eq'.1 hEq'
    have hyx : y = x := by
      simpa [inVertexFiber] using
        (graphRealizationSetoid_inVertexFiber_iff boundary x hsetoid).1 (by simp [inVertexFiber])
    exact hyx.symm
  · intro s hs
    have hquot : Topology.IsQuotientMap (graphQuotientMap boundary) := isQuotientMap_quotient_mk'
    have hs_preimage : IsClosed (graphQuotientMap boundary ⁻¹' (graphVertex boundary '' s)) := by
      rw [graphVertex_preimage_image]
      -- Compute the quotient preimage and show each source piece is closed.
      refine (IsClosedEmbedding.inl.isClosedMap _ hs).union ?_
      have hendpointZero :
          IsClosed {p : J × I | p.2 = 0 ∧ boundary p.1 0 ∈ s} := by
        have hsnd : IsClosed ((fun p : J × I ↦ p.2) ⁻¹' ({0} : Set I)) :=
          isClosed_singleton.preimage continuous_snd
        have hfst : IsClosed ((fun p : J × I ↦ p.1) ⁻¹' {j : J | boundary j 0 ∈ s}) :=
          (isClosed_discrete _).preimage
            (continuous_fst : Continuous (fun p : J × I ↦ p.1))
        convert hsnd.inter hfst using 1
      have hendpointOne :
          IsClosed {p : J × I | p.2 = 1 ∧ boundary p.1 1 ∈ s} := by
        have hsnd : IsClosed ((fun p : J × I ↦ p.2) ⁻¹' ({1} : Set I)) :=
          isClosed_singleton.preimage continuous_snd
        have hfst : IsClosed ((fun p : J × I ↦ p.1) ⁻¹' {j : J | boundary j 1 ∈ s}) :=
          (isClosed_discrete _).preimage
            (continuous_fst : Continuous (fun p : J × I ↦ p.1))
        convert hsnd.inter hfst using 1
      exact IsClosedEmbedding.inr.isClosedMap _ (hendpointZero.union hendpointOne)
    -- Pull the closedness statement back through the quotient map characterization.
    exact hquot.isClosed_preimage.1 hs_preimage

/-- Helper for Definition 4.1.4: with discrete source topologies on vertices and edges, the fixed
midpoint section of the edge index set is a closed embedding. -/
theorem graphMidpoint_isClosedEmbedding (boundary : J ↪ Fin 2 → X₀) (m : I)
    (hm₀ : m ≠ 0) (hm₁ : m ≠ 1) :
    let _ : TopologicalSpace X₀ := ⊥
    let _ : TopologicalSpace J := ⊥
    let _ : TopologicalSpace (graphRealization boundary) :=
      graphRealizationSourceFaithfulTopologicalSpace boundary
    Topology.IsClosedEmbedding (fun j : J ↦ graphEdgePoint boundary j m) := by
  let _ : TopologicalSpace X₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  let _ : DiscreteTopology X₀ := discreteTopology_bot X₀
  let _ : DiscreteTopology J := discreteTopology_bot J
  refine Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap ?_ ?_ ?_
  · -- The midpoint section factors through the right inclusion of the source sum.
    have hpair : Continuous (fun j : J ↦ (j, m)) :=
      continuous_id.prodMk continuous_const
    simpa [graphEdgePoint, graphRealizationPoint, graphQuotientMap] using
      (continuous_quotient_mk' : Continuous (graphQuotientMap boundary)).comp
        (continuous_inr.comp hpair)
  · intro j k hEq
    -- Interior rigidity forces equality of the underlying edge indices.
    have hsetoid : graphRealizationSetoid boundary (Sum.inr (j, m)) (Sum.inr (k, m)) := by
      have hEq' :
          graphQuotientMap boundary (Sum.inr (j, m)) =
            graphQuotientMap boundary (Sum.inr (k, m)) := by
        simpa [graphEdgePoint, graphRealizationPoint, graphQuotientMap] using hEq
      exact Quotient.eq'.1 hEq'
    have hk : Sum.inr (k, m) = Sum.inr (j, m) :=
      graphRealizationSetoid_interior_eq boundary j m hm₀ hm₁ hsetoid
    have hpair : (k, m) = (j, m) := Sum.inr.inj hk
    cases hpair
    rfl
  · intro s hs
    have hquot : Topology.IsQuotientMap (graphQuotientMap boundary) := isQuotientMap_quotient_mk'
    have hs_preimage :
        IsClosed (graphQuotientMap boundary ⁻¹'
          ((fun j : J ↦ graphEdgePoint boundary j m) '' s)) := by
      rw [graphMidpoint_preimage_image boundary m hm₀ hm₁ s]
      -- The source midpoint slice is closed because `s` is closed in the discrete edge index set
      -- and `{m}` is closed in the interval.
      have hfst : IsClosed ((fun p : J × I ↦ p.1) ⁻¹' s) := by
        exact hs.preimage (continuous_fst : Continuous (fun p : J × I ↦ p.1))
      have hsnd : IsClosed ((fun p : J × I ↦ p.2) ⁻¹' ({m} : Set I)) :=
        isClosed_singleton.preimage continuous_snd
      have hslice : IsClosed {p : J × I | p.1 ∈ s ∧ p.2 = m} := by
        convert hfst.inter hsnd using 1
      exact IsClosedEmbedding.inr.isClosedMap _ hslice
    -- Descend the closedness statement through the quotient map.
    exact hquot.isClosed_preimage.1 hs_preimage

/-- A finite graph realization is compact for the source-faithful quotient topology coming from
discrete vertices and edges together with the usual topology on `I`. -/
instance finiteGraph_compactSpace (boundary : J ↪ Fin 2 → X₀) [h : FiniteGraph boundary] :
    @CompactSpace (graphRealization boundary)
      (graphRealizationSourceFaithfulTopologicalSpace boundary) := by
  let _ : TopologicalSpace X₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  let _ : DiscreteTopology X₀ := discreteTopology_bot X₀
  let _ : DiscreteTopology J := discreteTopology_bot J
  -- Put compact structures on the discrete source pieces using the finite hypotheses.
  let _ : Finite X₀ := h.finiteVertices
  let _ : Finite J := h.finiteEdges
  let _ : CompactSpace X₀ := Finite.compactSpace
  let _ : CompactSpace J := Finite.compactSpace
  let _ : CompactSpace (J × I) := inferInstance
  let _ : CompactSpace (X₀ ⊕ (J × I)) := inferInstance
  -- Compactness descends to the quotient realization.
  exact Quotient.compactSpace

/-- Conversely, compactness of the source-faithful graph realization recovers finiteness of the
underlying graph. -/
instance compactSpace_finiteGraph (boundary : J ↪ Fin 2 → X₀)
    [@CompactSpace (graphRealization boundary)
      (graphRealizationSourceFaithfulTopologicalSpace boundary)] :
    FiniteGraph boundary := by
  let _ : TopologicalSpace X₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  -- Recover compactness of the discrete vertex and edge index sets from closed embeddings.
  have hVertex : Topology.IsClosedEmbedding (graphVertex boundary) :=
    graphVertex_isClosedEmbedding boundary
  let _ : CompactSpace X₀ := hVertex.compactSpace
  have hMidpoint :
      Topology.IsClosedEmbedding (fun j : J ↦ graphEdgePoint boundary j graphMidpoint) :=
    graphMidpoint_isClosedEmbedding boundary graphMidpoint
      graphMidpoint_ne_zero graphMidpoint_ne_one
  let _ : CompactSpace J := hMidpoint.compactSpace
  let _ : DiscreteTopology X₀ := discreteTopology_bot X₀
  let _ : DiscreteTopology J := discreteTopology_bot J
  -- Compact discrete spaces are finite.
  exact ⟨finite_of_compact_of_discrete, finite_of_compact_of_discrete⟩

/-- Definition 4.1.4. A graph is finite when it has only finitely many vertices and edges;
equivalently, its realization is compact. -/
theorem finiteGraph_iff_compactSpace (boundary : J ↪ Fin 2 → X₀) :
    FiniteGraph boundary ↔
      @CompactSpace (graphRealization boundary)
        (graphRealizationSourceFaithfulTopologicalSpace boundary) := by
  constructor
  · intro h
    -- The forward implication is the compactness instance just proved above.
    let _ : FiniteGraph boundary := h
    infer_instance
  · intro h
    -- The reverse implication is the finiteness instance recovered from compactness.
    let _ : @CompactSpace (graphRealization boundary)
      (graphRealizationSourceFaithfulTopologicalSpace boundary) := h
    infer_instance
