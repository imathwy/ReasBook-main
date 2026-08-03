module

public import Topology_Munkres_2000.Book.Example_50_7
public import Topology_Munkres_2000.Book.Remark_64_2.Incidence
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

public section

universe u v w

namespace SimpleGraph.LinearRealization

/-- Helper for Remark 64.2: every point on a selected realized edge belongs to the
corresponding selected edge union. -/
lemma selectedEdgePoint_mem_edgeUnion {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge) (i : {i // i ∈ s})
    (t : unitInterval) : L.edge i.1 t ∈ edgeUnion L s := by
  -- The chosen edge index and its range witness edge-union membership.
  exact (mem_edgeUnion_iff L s _).2 ⟨i.1, i.2, ⟨t, rfl⟩⟩

/-- Helper for Remark 64.2: the parameterization of a selected edge, with codomain
restricted to the selected edge union. -/
def edgeUnionParam {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge) (i : {i // i ∈ s}) :
    unitInterval → edgeUnion L s :=
  Set.codRestrict (L.edge i.1) (edgeUnion L s) (selectedEdgePoint_mem_edgeUnion L s i)

/-- Helper for Remark 64.2: restricting a selected edge's codomain preserves its
topological embedding. -/
lemma edgeUnionParam_isEmbedding {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge) (i : {i // i ∈ s}) :
    Topology.IsEmbedding (edgeUnionParam L s i) := by
  -- Apply the standard codomain-restriction theorem to the stored edge embedding.
  exact (L.edgeEmbedding i.1).codRestrict (edgeUnion L s)
    (selectedEdgePoint_mem_edgeUnion L s i)

/-- Helper for Remark 64.2: membership in a restricted selected edge is detected in
the ambient realization. -/
lemma mem_range_edgeUnionParam_iff {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge) (i : {i // i ∈ s})
    (x : edgeUnion L s) :
    x ∈ Set.range (edgeUnionParam L s i) ↔ (x : X) ∈ L.edgeSet i.1 := by
  -- Witnesses in the two ranges are identical after forgetting the subtype proof.
  rw [L.edgeSet_def]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, rfl⟩
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    exact Subtype.ext ht

/-- Helper for Remark 64.2: the restricted selected-edge parameterizations cover the
selected edge union. -/
lemma iUnion_range_edgeUnionParam {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge) :
    ⋃ i, Set.range (edgeUnionParam L s i) = Set.univ := by
  -- Expand edge-union membership and retain its selected edge witness.
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  obtain ⟨i, hi, hxi⟩ := (mem_edgeUnion_iff L s (x : X)).1 x.2
  exact ⟨⟨i, hi⟩, (mem_range_edgeUnionParam_iff L s ⟨i, hi⟩ x).2 hxi⟩

/-- Helper for Remark 64.2: distinct restricted selected edges meet only at endpoints
of both restricted edges. -/
lemma edgeUnionParam_inter_subset_endpoints {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge)
    {i j : {i // i ∈ s}} (hij : i ≠ j) :
    Set.range (edgeUnionParam L s i) ∩ Set.range (edgeUnionParam L s j) ⊆
      ({edgeUnionParam L s i 0, edgeUnionParam L s i 1} ∩
        {edgeUnionParam L s j 0, edgeUnionParam L s j 1} : Set (edgeUnion L s)) := by
  -- Forget subtype proofs, apply the original endpoint-intersection axiom, and lift back.
  intro x hx
  have hindex : i.1 ≠ j.1 := fun h ↦ hij (Subtype.ext h)
  have hambient := L.inter_subset_endpoints hindex
    ⟨(mem_range_edgeUnionParam_iff L s i x).1 hx.1,
      (mem_range_edgeUnionParam_iff L s j x).1 hx.2⟩
  rcases hambient with ⟨hi0 | hi1, hj0 | hj1⟩
  · exact ⟨Or.inl (Subtype.ext hi0), Or.inl (Subtype.ext hj0)⟩
  · exact ⟨Or.inl (Subtype.ext hi0), Or.inr (Subtype.ext hj1)⟩
  · exact ⟨Or.inr (Subtype.ext hi1), Or.inl (Subtype.ext hj0)⟩
  · exact ⟨Or.inr (Subtype.ext hi1), Or.inr (Subtype.ext hj1)⟩

/-- Helper for Remark 64.2: intersections of distinct restricted selected edges remain
subsingletons. -/
lemma edgeUnionParam_inter_subsingleton {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge)
    {i j : {i // i ∈ s}} (hij : i ≠ j) :
    (Set.range (edgeUnionParam L s i) ∩
      Set.range (edgeUnionParam L s j)).Subsingleton := by
  -- Ambient equality follows from the original subsingleton-intersection axiom.
  intro x hx y hy
  apply Subtype.ext
  have hindex : i.1 ≠ j.1 := fun h ↦ hij (Subtype.ext h)
  exact L.inter_subsingleton hindex
    ⟨(mem_range_edgeUnionParam_iff L s i x).1 hx.1,
      (mem_range_edgeUnionParam_iff L s j x).1 hx.2⟩
    ⟨(mem_range_edgeUnionParam_iff L s i y).1 hy.1,
      (mem_range_edgeUnionParam_iff L s j y).1 hy.2⟩

/-- Helper for Remark 64.2: a selected edge union inherits the Hausdorff topology of
the ambient finite linear graph. -/
lemma edgeUnion_t2Space {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge) : T2Space (edgeUnion L s) := by
  -- Local instance justification (stored presentation data): the ambient Hausdorff instance
  -- is carried as a field of `L`, and subtype Hausdorffness is then canonical.
  letI : T2Space X := L.t2Space
  infer_instance

/-- Helper for Remark 64.2: a selected union of edges is itself a finite linear graph,
with exactly the selected realized edges as its presentation. -/
def edgeUnionLinearGraph {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge) :
    FiniteLinearGraph.{u, v} (edgeUnion L s) :=
  {
    t2Space := edgeUnion_t2Space L s
    Edge := {i // i ∈ s}
    edgeFinite := selectedEdge_finite L s
    edge := edgeUnionParam L s
    edgeEmbedding := edgeUnionParam_isEmbedding L s
    iUnion_range := iUnion_range_edgeUnionParam L s
    interSubsetEndpoints := edgeUnionParam_inter_subset_endpoints L s
    interSubsingleton := edgeUnionParam_inter_subsingleton L s
  }

/-- Helper for Remark 64.2: affine edge maps into any finite-dimensional real normed
space glue continuously across a finite linear graph. -/
lemma FiniteLinearGraph.exists_continuous_edgewiseLineMapTo
    {X : Type u} [TopologicalSpace X] [T2Space X]
    {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (G : FiniteLinearGraph.{u, v} X) (z : X → E) :
    ∃ f : X → E, Continuous f ∧
      ∀ i t, f (G.edge i t) =
        AffineMap.lineMap (z (G.edge i 0)) (z (G.edge i 1)) (t : ℝ) := by
  classical
  -- Local instance justification (stored presentation data): finite gluing needs the edge
  -- index type's finiteness, which `G` stores as a field.
  letI : Finite G.Edge := G.edgeFinite
  let φ : ∀ i, G.edgeSet i → E := fun i x ↦
    AffineMap.lineMap (z (G.edge i 0)) (z (G.edge i 1))
      ((G.edgeEmbedding i).toHomeomorph.symm
        ⟨x, G.edgeSetPoint_mem_range i x⟩ : ℝ)
  have hφ_spec (i : G.Edge) (t : unitInterval) :
      φ i ⟨G.edge i t, G.edgePoint_mem_edgeSet i t⟩ =
        AffineMap.lineMap (z (G.edge i 0)) (z (G.edge i 1)) (t : ℝ) := by
    -- The inverse edge homeomorphism recovers the original unit-interval parameter.
    have htparam := (G.edgeEmbedding i).toHomeomorph_symm_apply t
    exact congrArg (AffineMap.lineMap (z (G.edge i 0)) (z (G.edge i 1)))
      (congrArg Subtype.val htparam)
  have hφ_vertex (i : G.Edge) (x : X) (hx : x ∈ G.edgeSet i)
      (hend : x = G.edge i 0 ∨ x = G.edge i 1) : φ i ⟨x, hx⟩ = z x := by
    -- At either endpoint the affine map equals its assigned vertex coordinate.
    obtain rfl | rfl := hend
    · simpa using hφ_spec i 0
    · simpa using hφ_spec i 1
  have hcompat : ∀ (i j : G.Edge) (x : X) (hxi : x ∈ G.edgeSet i)
      (hxj : x ∈ G.edgeSet j), φ i ⟨x, hxi⟩ = φ j ⟨x, hxj⟩ := by
    intro i j x hxi hxj
    by_cases hij : i = j
    · subst j
      rfl
    · have hend := G.inter_subset_endpoints hij ⟨hxi, hxj⟩
      exact (hφ_vertex i x hxi hend.1).trans (hφ_vertex j x hxj hend.2).symm
  let f : X → E := Set.liftCover G.edgeSet φ hcompat G.iUnion_edgeSet
  refine ⟨f, ?_, ?_⟩
  · -- Continuity follows from the finite closed cover by compact edge images.
    refine (locallyFinite_of_finite G.edgeSet).continuous G.iUnion_edgeSet ?_ ?_
    · intro i
      exact (isCompact_range (G.edgeEmbedding i).continuous).isClosed
    · intro i
      have hφ_cont : Continuous (φ i) := by
        exact
          (AffineMap.lineMap
            (z (G.edge i 0)) (z (G.edge i 1))).continuous_of_finiteDimensional.comp
          (continuous_subtype_val.comp (G.edgeEmbedding i).toHomeomorph.symm.continuous)
      rw [continuousOn_iff_continuous_restrict]
      have hrestrict : (G.edgeSet i).restrict f = φ i := by
        funext x
        exact Set.liftCover_coe (hS := G.iUnion_edgeSet) x
      rw [hrestrict]
      exact hφ_cont
  · intro i t
    -- The lift-cover computation rule gives the affine formula on each edge.
    have hmem : G.edge i t ∈ G.edgeSet i := G.edgePoint_mem_edgeSet i t
    have hlift : f (G.edge i t) = φ i ⟨G.edge i t, hmem⟩ :=
      Set.liftCover_of_mem hmem
    rw [hlift]
    exact hφ_spec i t

end SimpleGraph.LinearRealization
