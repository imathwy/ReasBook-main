module

public import Topology_Munkres_2000.Book.Remark_64_2.Classifier
public import Topology_Munkres_2000.Book.Remark_64_2.PathEmbedding
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

public section

universe u v

namespace SimpleGraph.LinearRealization

variable {V : Type u} {G : SimpleGraph V}

/-- A topological linear-graph realization embeds in the plane `ℝ × ℝ`. -/
def IsPlaneEmbeddable (R : G.LinearRealization.{u, v}) : Prop :=
  ∃ f : R.Carrier → ℝ × ℝ, Topology.IsEmbedding f

/-- A topological linear-graph realization contains an embedded realization of the
utilities graph or the complete graph on five vertices. -/
def ContainsKuratowskiObstruction (R : G.LinearRealization.{u, v}) : Prop :=
  (∃ S : (completeBipartiteGraph (Fin 3) (Fin 3)).LinearRealization.{0, v},
    ∃ e : S.Carrier → R.Carrier, Topology.IsEmbedding e) ∨
  ∃ S : (SimpleGraph.completeGraph (Fin 5)).LinearRealization.{0, v},
    ∃ e : S.Carrier → R.Carrier, Topology.IsEmbedding e

/-- A realization contains a Kuratowski obstruction exactly when it contains an embedded
utilities-graph realization or an embedded complete-five-graph realization. -/
theorem containsKuratowskiObstruction_iff (R : G.LinearRealization.{u, v}) :
    R.ContainsKuratowskiObstruction ↔
      (∃ S : (completeBipartiteGraph (Fin 3) (Fin 3)).LinearRealization.{0, v},
        ∃ e : S.Carrier → R.Carrier, Topology.IsEmbedding e) ∨
      ∃ S : (SimpleGraph.completeGraph (Fin 5)).LinearRealization.{0, v},
        ∃ e : S.Carrier → R.Carrier, Topology.IsEmbedding e :=
  Iff.rfl

/-- Remark 64.2 (1). If a graph realization contains an embedded realization of the
utilities graph or the complete graph on five vertices, then it does not embed in the plane. -/
theorem forbiddenGraphEmbedding_obstructsPlaneEmbedding (R : G.LinearRealization.{u, v})
    (h_forbidden : R.ContainsKuratowskiObstruction) : ¬ R.IsPlaneEmbeddable := by
  rcases h_forbidden with ⟨S, e, he⟩ | ⟨S, e, he⟩
  · rintro ⟨f, hf⟩
    exact utilitiesGraph_not_isEmbedding S ⟨f ∘ e, hf.comp he⟩
  · rintro ⟨f, hf⟩
    exact completeGraphFive_not_isEmbedding S ⟨f ∘ e, hf.comp he⟩

/-- Helper for Remark 64.2: an adjacency in the selected incidence graph determines an
incidence edge. -/
private def incidenceEdgeOfAdj {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge)
    {a b : SelectedEndpoint L s} (h : (selectedIncidenceGraph L s).Adj a b) :
    (selectedIncidenceGraph L s).edgeSet :=
  ⟨s(a, b), h⟩

/-- Helper for Remark 64.2: the realized edge selected by an incidence adjacency. -/
private noncomputable def selectedEdgeOfAdj {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge)
    {a b : SelectedEndpoint L s} (h : (selectedIncidenceGraph L s).Adj a b) :
    {i // i ∈ s} :=
  selectedIncidenceGraph_edgeEquiv L s (incidenceEdgeOfAdj L s h)

/-- Helper for Remark 64.2: the edge selected by an incidence adjacency has exactly the
adjacency's two ambient endpoints. -/
private lemma selectedEdgeOfAdj_endpointPair {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge)
    {a b : SelectedEndpoint L s} (h : (selectedIncidenceGraph L s).Adj a b) :
    s(L.edge (selectedEdgeOfAdj L s h).1 0, L.edge (selectedEdgeOfAdj L s h).1 1) =
      s((a : X), (b : X)) := by
  -- Map the subtype endpoint-pair identity to the ambient carrier `X`.
  have hp := selectedIncidenceGraph_edgeEquiv_endpointPair L s
    (incidenceEdgeOfAdj L s h)
  have hm := congrArg (Sym2.map (fun x : SelectedEndpoint L s ↦ (x : X))) hp
  rw [selectedEdgeEndpointPair_map_coe] at hm
  simpa only [selectedEdgeOfAdj, Sym2.map_mk, incidenceEdgeOfAdj] using hm

/-- Helper for Remark 64.2: an incidence adjacency orders its selected realized edge either
forward or backward. -/
private lemma selectedEdgeOfAdj_orientation {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge)
    {a b : SelectedEndpoint L s} (h : (selectedIncidenceGraph L s).Adj a b) :
    ((a : X) = L.edge (selectedEdgeOfAdj L s h).1 0 ∧
      (b : X) = L.edge (selectedEdgeOfAdj L s h).1 1) ∨
    ((a : X) = L.edge (selectedEdgeOfAdj L s h).1 1 ∧
      (b : X) = L.edge (selectedEdgeOfAdj L s h).1 0) := by
  -- Equality of unordered pairs gives precisely the two possible orientations.
  rcases Sym2.eq_iff.mp (selectedEdgeOfAdj_endpointPair L s h) with hforward | hreverse
  · exact Or.inl ⟨hforward.1.symm, hforward.2.symm⟩
  · exact Or.inr ⟨hreverse.2.symm, hreverse.1.symm⟩

/-- Helper for Remark 64.2: if the forward endpoint order fails, an incidence adjacency uses
the reverse order. -/
private lemma selectedEdgeOfAdj_reverse_orientation {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge)
    {a b : SelectedEndpoint L s} (h : (selectedIncidenceGraph L s).Adj a b)
    (hforward : ¬ ((a : X) = L.edge (selectedEdgeOfAdj L s h).1 0 ∧
      (b : X) = L.edge (selectedEdgeOfAdj L s h).1 1)) :
    (a : X) = L.edge (selectedEdgeOfAdj L s h).1 1 ∧
      (b : X) = L.edge (selectedEdgeOfAdj L s h).1 0 := by
  -- Eliminate the forward alternative in the orientation dichotomy.
  rcases selectedEdgeOfAdj_orientation L s h with hdirect | hreverse
  · exact (hforward hdirect).elim
  · exact hreverse

/-- Helper for Remark 64.2: a selected realized edge, with its stored parameterization, is a
path between its endpoints. -/
private def selectedRealizedEdgePath {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (i : L.Edge) :
    _root_.Path (L.edge i 0) (L.edge i 1) :=
  _root_.Path.mk ⟨L.edge i, (L.edgeEmbedding i).continuous⟩ rfl rfl

/-- Helper for Remark 64.2: the underlying map of a selected realized-edge path is the stored
edge parameterization. -/
private lemma selectedRealizedEdgePath_coe {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (i : L.Edge) :
    ⇑(selectedRealizedEdgePath L i) = L.edge i := by
  -- The path constructor stores the original edge parameterization unchanged.
  rfl

/-- Helper for Remark 64.2: reversing a selected realized-edge path precomposes its stored
parameterization with interval symmetry. -/
private lemma selectedRealizedEdgePath_symm_coe {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (i : L.Edge) :
    ⇑(selectedRealizedEdgePath L i).symm = L.edge i ∘ unitInterval.symm := by
  -- Both sides use the same interval-symmetry precomposition.
  rfl

/-- Helper for Remark 64.2: a selected realized-edge path is a topological embedding. -/
private lemma selectedRealizedEdgePath_isEmbedding {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (i : L.Edge) :
    Topology.IsEmbedding (selectedRealizedEdgePath L i) := by
  -- Rewrite to the stored edge parameterization and use its embedding field.
  rw [selectedRealizedEdgePath_coe]
  exact L.edgeEmbedding i

/-- Helper for Remark 64.2: reversing a selected realized-edge path preserves its embedding
property. -/
private lemma selectedRealizedEdgePath_symm_isEmbedding {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (i : L.Edge) :
    Topology.IsEmbedding (selectedRealizedEdgePath L i).symm := by
  -- Interval symmetry is a homeomorphism, so precomposition preserves embedding.
  rw [selectedRealizedEdgePath_symm_coe]
  exact (L.edgeEmbedding i).comp unitInterval.symmHomeomorph.isEmbedding

/-- Helper for Remark 64.2: an incidence adjacency admits an oriented topological path whose
range is its uniquely selected realized edge. -/
private lemma exists_selectedAdjacencyPath {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge)
    {a b : SelectedEndpoint L s} (h : (selectedIncidenceGraph L s).Adj a b) :
    ∃ γ : _root_.Path (a : X) (b : X),
      Topology.IsEmbedding γ ∧
        Set.range γ = L.edgeSet (selectedEdgeOfAdj L s h).1 := by
  -- Choose the stored edge path or its reversal according to the unordered endpoint equality.
  rcases selectedEdgeOfAdj_orientation L s h with hforward | hreverse
  · let γ := (selectedRealizedEdgePath L (selectedEdgeOfAdj L s h).1).cast
      hforward.1 hforward.2
    refine ⟨γ, ?_, ?_⟩
    · -- Casting endpoint proofs does not change the embedded function.
      rw [Path.cast_coe]
      exact selectedRealizedEdgePath_isEmbedding L _
    · calc
        Set.range γ = Set.range (selectedRealizedEdgePath L
            (selectedEdgeOfAdj L s h).1) :=
          congrArg Set.range (Path.cast_coe _ hforward.1 hforward.2)
        _ = Set.range (L.edge (selectedEdgeOfAdj L s h).1) :=
          congrArg Set.range (selectedRealizedEdgePath_coe L _)
        _ = L.edgeSet (selectedEdgeOfAdj L s h).1 := (L.edgeSet_def _).symm
  · let γ := (selectedRealizedEdgePath L (selectedEdgeOfAdj L s h).1).symm.cast
      hreverse.1 hreverse.2
    refine ⟨γ, ?_, ?_⟩
    · -- Reversal is embedded, and casting endpoint proofs again preserves the function.
      rw [Path.cast_coe]
      exact selectedRealizedEdgePath_symm_isEmbedding L _
    · calc
        Set.range γ = Set.range
            (selectedRealizedEdgePath L (selectedEdgeOfAdj L s h).1).symm :=
          congrArg Set.range (Path.cast_coe _ hreverse.1 hreverse.2)
        _ = Set.range (selectedRealizedEdgePath L (selectedEdgeOfAdj L s h).1) :=
          Path.symm_range _
        _ = Set.range (L.edge (selectedEdgeOfAdj L s h).1) :=
          congrArg Set.range (selectedRealizedEdgePath_coe L _)
        _ = L.edgeSet (selectedEdgeOfAdj L s h).1 := (L.edgeSet_def _).symm

/-- Helper for Remark 64.2: orient the realized path belonging to an incidence adjacency from
the adjacency's first endpoint to its second. -/
private noncomputable def selectedAdjacencyPath {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge)
    {a b : SelectedEndpoint L s} (h : (selectedIncidenceGraph L s).Adj a b) :
    _root_.Path (a : X) (b : X) :=
  Classical.choose (exists_selectedAdjacencyPath L s h)

/-- Helper for Remark 64.2: the oriented adjacency path has the range of its uniquely selected
realized edge. -/
private lemma selectedAdjacencyPath_range {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge)
    {a b : SelectedEndpoint L s} (h : (selectedIncidenceGraph L s).Adj a b) :
    Set.range (selectedAdjacencyPath L s h) =
      L.edgeSet (selectedEdgeOfAdj L s h).1 := by
  -- Read the range specification stored with the chosen oriented path.
  exact (Classical.choose_spec (exists_selectedAdjacencyPath L s h)).2

/-- Helper for Remark 64.2: the oriented path belonging to one incidence adjacency is a
topological embedding. -/
private lemma selectedAdjacencyPath_isEmbedding {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge)
    {a b : SelectedEndpoint L s} (h : (selectedIncidenceGraph L s).Adj a b) :
    Topology.IsEmbedding (selectedAdjacencyPath L s h) := by
  -- Read the embedding specification stored with the chosen oriented path.
  exact (Classical.choose_spec (exists_selectedAdjacencyPath L s h)).1

/-- Helper for Remark 64.2: the endpoints of the realized edge selected by an incidence
adjacency are precisely the two vertices of that adjacency. -/
private lemma selectedEdgeOfAdj_endpoint_iff {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge)
    {a b : SelectedEndpoint L s} (h : (selectedIncidenceGraph L s).Adj a b) (x : X) :
    (x = L.edge (selectedEdgeOfAdj L s h).1 0 ∨
      x = L.edge (selectedEdgeOfAdj L s h).1 1) ↔
      x = (a : X) ∨ x = (b : X) := by
  -- Resolve the unordered endpoint equality once, then compare the two possible orders.
  rcases selectedEdgeOfAdj_orientation L s h with hforward | hreverse
  · constructor
    · rintro (hx | hx)
      · exact Or.inl (hx.trans hforward.1.symm)
      · exact Or.inr (hx.trans hforward.2.symm)
    · rintro (hx | hx)
      · exact Or.inl (hx.trans hforward.1)
      · exact Or.inr (hx.trans hforward.2)
  · constructor
    · rintro (hx | hx)
      · exact Or.inr (hx.trans hreverse.2.symm)
      · exact Or.inl (hx.trans hreverse.1.symm)
    · rintro (hx | hx)
      · exact Or.inr (hx.trans hreverse.1)
      · exact Or.inl (hx.trans hreverse.2)

/-- Helper for Remark 64.2: distinct incidence edges select distinct realized edges. -/
private lemma selectedEdgeOfAdj_ne {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge)
    {a b c d : SelectedEndpoint L s}
    (h : (selectedIncidenceGraph L s).Adj a b)
    (k : (selectedIncidenceGraph L s).Adj c d)
    (hne : incidenceEdgeOfAdj L s h ≠ incidenceEdgeOfAdj L s k) :
    (selectedEdgeOfAdj L s h).1 ≠ (selectedEdgeOfAdj L s k).1 := by
  -- Injectivity of the edge equivalence transports equality back to incidence edges.
  intro hedges
  apply hne
  apply (selectedIncidenceGraph_edgeEquiv L s).injective
  apply Subtype.ext
  exact hedges

/-- Helper for Remark 64.2: an intersection point of two distinct realized incidence edges
comes from a vertex incident to both graph edges. -/
private lemma selectedAdjacencyPath_intersection_branch {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge)
    {a b c d : SelectedEndpoint L s}
    (h : (selectedIncidenceGraph L s).Adj a b)
    (k : (selectedIncidenceGraph L s).Adj c d)
    (hne : incidenceEdgeOfAdj L s h ≠ incidenceEdgeOfAdj L s k)
    {x : X} (hx : x ∈ Set.range (selectedAdjacencyPath L s h))
    (hk : x ∈ Set.range (selectedAdjacencyPath L s k)) :
    ∃ q, q ∈ s(a, b) ∧ q ∈ s(c, d) ∧ (q : X) = x := by
  -- Move the intersection to the two original realized edges and invoke their endpoint axiom.
  rw [selectedAdjacencyPath_range] at hx hk
  have hedgeNe := selectedEdgeOfAdj_ne L s h k hne
  have hendpoints := L.inter_subset_endpoints hedgeNe ⟨hx, hk⟩
  have hab : x = (a : X) ∨ x = (b : X) := by
    apply (selectedEdgeOfAdj_endpoint_iff L s h x).1
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hendpoints.1
  have hcd : x = (c : X) ∨ x = (d : X) := by
    apply (selectedEdgeOfAdj_endpoint_iff L s k x).1
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hendpoints.2
  -- Equality in the ambient carrier identifies the corresponding endpoint subtypes.
  rcases hab with hxa | hxb
  · refine ⟨a, Sym2.mem_mk_left a b, ?_, hxa.symm⟩
    rcases hcd with hxc | hxd
    · have hac : a = c := Subtype.ext (hxa.symm.trans hxc)
      rw [hac]
      exact Sym2.mem_mk_left c d
    · have had : a = d := Subtype.ext (hxa.symm.trans hxd)
      rw [had]
      exact Sym2.mem_mk_right c d
  · refine ⟨b, Sym2.mem_mk_right a b, ?_, hxb.symm⟩
    rcases hcd with hxc | hxd
    · have hbc : b = c := Subtype.ext (hxb.symm.trans hxc)
      rw [hbc]
      exact Sym2.mem_mk_left c d
    · have hbd : b = d := Subtype.ext (hxb.symm.trans hxd)
      rw [hbd]
      exact Sym2.mem_mk_right c d

/-- Helper for Remark 64.2: realized paths of disjoint incidence edges have disjoint
ranges. -/
private lemma selectedAdjacencyPath_disjoint_of_incidence_disjoint
    {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge)
    {a b c d : SelectedEndpoint L s}
    (h : (selectedIncidenceGraph L s).Adj a b)
    (k : (selectedIncidenceGraph L s).Adj c d)
    (hne : incidenceEdgeOfAdj L s h ≠ incidenceEdgeOfAdj L s k)
    (hdisjoint : ∀ q, q ∈ s(a, b) → q ∉ s(c, d)) :
    Disjoint (Set.range (selectedAdjacencyPath L s h))
      (Set.range (selectedAdjacencyPath L s k)) := by
  -- A common range point would provide a common incidence vertex.
  rw [Set.disjoint_left]
  intro x hx hk
  obtain ⟨q, hqab, hqcd, _⟩ :=
    selectedAdjacencyPath_intersection_branch L s h k hne hx hk
  exact hdisjoint q hqab hqcd

/-- Helper for Remark 64.2: two distinct realized incidence edges sharing one endpoint meet
exactly at that endpoint. -/
private lemma selectedAdjacencyPath_inter_eq_singleton
    {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge)
    {a b c : SelectedEndpoint L s}
    (h : (selectedIncidenceGraph L s).Adj a b)
    (k : (selectedIncidenceGraph L s).Adj b c)
    (hne : incidenceEdgeOfAdj L s h ≠ incidenceEdgeOfAdj L s k) :
    Set.range (selectedAdjacencyPath L s h) ∩
        Set.range (selectedAdjacencyPath L s k) = {(b : X)} := by
  -- The finite-linear-graph intersection is subsingleton and contains the common endpoint.
  have hedgeNe := selectedEdgeOfAdj_ne L s h k hne
  have hsubsingleton :
      (Set.range (selectedAdjacencyPath L s h) ∩
        Set.range (selectedAdjacencyPath L s k)).Subsingleton := by
    rw [selectedAdjacencyPath_range, selectedAdjacencyPath_range]
    exact L.inter_subsingleton hedgeNe
  have hb : (b : X) ∈ Set.range (selectedAdjacencyPath L s h) ∩
      Set.range (selectedAdjacencyPath L s k) := by
    constructor
    · exact ⟨1, Path.target _⟩
    · exact ⟨0, Path.source _⟩
  ext x
  constructor
  · intro hx
    rw [Set.mem_singleton_iff]
    exact hsubsingleton hx hb
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    exact hx ▸ hb

/-- Helper for Remark 64.2: a selected endpoint lies on an oriented adjacency path exactly
when it is one of that adjacency's endpoints. -/
private lemma selectedEndpoint_mem_selectedAdjacencyPath_range_iff
    {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge)
    {a b : SelectedEndpoint L s} (h : (selectedIncidenceGraph L s).Adj a b)
    (c : SelectedEndpoint L s) :
    (c : X) ∈ Set.range (selectedAdjacencyPath L s h) ↔ c = a ∨ c = b := by
  constructor
  · intro hc
    -- Compare the edge witnessing that `c` is selected with the edge realizing `h`.
    rw [selectedAdjacencyPath_range] at hc
    obtain ⟨i, hi, hci⟩ := (mem_selectedEndpointSet_iff L s c).1 c.2
    have hcSelected :
        (c : X) = L.edge (selectedEdgeOfAdj L s h).1 0 ∨
          (c : X) = L.edge (selectedEdgeOfAdj L s h).1 1 := by
      by_cases hieq : i = (selectedEdgeOfAdj L s h).1
      · subst i
        exact hci
      · have hciSet : (c : X) ∈ L.edgeSet i := by
          rw [L.edgeSet_def]
          rcases hci with hci | hci
          · exact ⟨0, hci.symm⟩
          · exact ⟨1, hci.symm⟩
        have hendpoints := L.inter_subset_endpoints hieq ⟨hciSet, hc⟩
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hendpoints.2
    -- The selected-edge orientation transports the ambient endpoint equality to the subtype.
    rcases (selectedEdgeOfAdj_endpoint_iff L s h (c : X)).1 hcSelected with hca | hcb
    · exact Or.inl (Subtype.ext hca)
    · exact Or.inr (Subtype.ext hcb)
  · rintro (rfl | rfl)
    · -- The source of the oriented edge path is its first incidence vertex.
      exact ⟨0, Path.source _⟩
    · -- Its target is the second incidence vertex.
      exact ⟨1, Path.target _⟩

/-- Helper for Remark 64.2: every selected realized edge lies in its selected edge union. -/
private lemma selectedEdgeSet_subset_edgeUnion {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge) (i : {i // i ∈ s}) :
    L.edgeSet i.1 ⊆ edgeUnion L s := by
  -- Select `i` in the two indexed unions defining `edgeUnion`.
  intro x hx
  exact (mem_edgeUnion_iff L s x).2 ⟨i.1, i.2, hx⟩

/-- Helper for Remark 64.2: every selected endpoint belongs to the selected edge union. -/
private lemma selectedEndpoint_mem_edgeUnion {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge) (a : SelectedEndpoint L s) :
    (a : X) ∈ edgeUnion L s := by
  -- Use the selected edge witnessing that `a` is one of its two endpoints.
  obtain ⟨i, hi, ha | ha⟩ := (mem_selectedEndpointSet_iff L s a).1 a.2
  · apply selectedEdgeSet_subset_edgeUnion L s ⟨i, hi⟩
    rw [L.edgeSet_def]
    exact ⟨0, ha.symm⟩
  · apply selectedEdgeSet_subset_edgeUnion L s ⟨i, hi⟩
    rw [L.edgeSet_def]
    exact ⟨1, ha.symm⟩

/-- Helper for Remark 64.2: concatenate the realized paths along a walk in the selected
endpoint-incidence graph. -/
private noncomputable def selectedWalkPath {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge) :
    {a b : SelectedEndpoint L s} → (selectedIncidenceGraph L s).Walk a b →
      _root_.Path (a : X) (b : X)
  | _, _, .nil => _root_.Path.refl _
  | _, _, .cons h .nil => selectedAdjacencyPath L s h
  | _, _, .cons h (.cons k p) =>
      (selectedAdjacencyPath L s h).trans (selectedWalkPath L s (.cons k p))

/-- Helper for Remark 64.2: the realized path of an incidence walk stays inside the selected
edge union. -/
private lemma selectedWalkPath_range_subset {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge)
    {a b : SelectedEndpoint L s} (p : (selectedIncidenceGraph L s).Walk a b) :
    Set.range (selectedWalkPath L s p) ⊆ edgeUnion L s := by
  induction p with
  | nil =>
      -- A nil walk realizes the constant path at its selected endpoint.
      rw [selectedWalkPath, Path.refl_range]
      exact Set.singleton_subset_iff.mpr (selectedEndpoint_mem_edgeUnion L s _)
  | cons h p ih =>
      cases p with
      | nil =>
          -- A one-edge walk is represented by that edge alone, with no constant tail.
          rw [selectedWalkPath, selectedAdjacencyPath_range]
          exact selectedEdgeSet_subset_edgeUnion L s (selectedEdgeOfAdj L s h)
      | cons k p =>
          -- Longer walks concatenate the first selected edge with the nonempty tail.
          rw [selectedWalkPath, Path.trans_range, Set.union_subset_iff,
            selectedAdjacencyPath_range]
          exact ⟨selectedEdgeSet_subset_edgeUnion L s (selectedEdgeOfAdj L s h), ih⟩

/-- Helper for Remark 64.2: a selected endpoint lies on a realized incidence walk exactly
when it belongs to the walk support. -/
private lemma selectedEndpoint_mem_selectedWalkPath_range_iff
    {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge)
    {a b : SelectedEndpoint L s} (p : (selectedIncidenceGraph L s).Walk a b)
    (q : SelectedEndpoint L s) :
    (q : X) ∈ Set.range (selectedWalkPath L s p) ↔ q ∈ p.support := by
  induction p with
  | nil =>
      -- Both the reflexive path range and the nil-walk support are the initial singleton.
      simp only [selectedWalkPath, Path.refl_range, Set.mem_singleton_iff,
        SimpleGraph.Walk.support_nil, List.mem_singleton]
      exact Subtype.coe_injective.eq_iff
  | cons h p ih =>
      cases p with
      | nil =>
          -- A one-edge walk has precisely its two incidence endpoints in both descriptions.
          rw [selectedWalkPath, selectedEndpoint_mem_selectedAdjacencyPath_range_iff]
          simp
      | cons k p =>
          -- For a longer walk, both range and support split into the first arc and the tail.
          rw [selectedWalkPath, Path.trans_range, Set.mem_union,
            selectedEndpoint_mem_selectedAdjacencyPath_range_iff, ih]
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
          constructor
          · rintro ((rfl | rfl) | htail)
            · exact Or.inl rfl
            · exact Or.inr (by simp)
            · exact Or.inr htail
          · rintro (rfl | htail)
            · exact Or.inl (Or.inl rfl)
            · exact Or.inr htail

/-- Helper for Remark 64.2: every point of a nonempty realized walk lies on a realized
incidence edge occurring in that walk. -/
private lemma selectedWalkPath_range_edge_witness
    {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge)
    {a b : SelectedEndpoint L s} (p : (selectedIncidenceGraph L s).Walk a b)
    (hnil : ¬ p.Nil) {x : X} (hx : x ∈ Set.range (selectedWalkPath L s p)) :
    ∃ e : (selectedIncidenceGraph L s).edgeSet,
      e.1 ∈ p.edges ∧ x ∈ L.edgeSet (selectedIncidenceGraph_edgeEquiv L s e).1 := by
  induction p with
  | nil =>
      -- The nonempty hypothesis excludes a nil walk before any edge witness is required.
      exact (hnil SimpleGraph.Walk.Nil.nil).elim
  | cons h p ih =>
      cases p with
      | nil =>
          -- The unique incidence edge witnesses every point of a one-edge realization.
          refine ⟨incidenceEdgeOfAdj L s h, ?_, ?_⟩
          · simp only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
              List.mem_singleton, incidenceEdgeOfAdj]
          · rw [selectedWalkPath, selectedAdjacencyPath_range] at hx
            exact hx
      | cons k p =>
          -- A concatenated range point lies either on its first edge or on the nonempty tail.
          rw [selectedWalkPath, Path.trans_range, Set.mem_union] at hx
          rcases hx with hfirst | htail
          · refine ⟨incidenceEdgeOfAdj L s h, ?_, ?_⟩
            · rw [SimpleGraph.Walk.edges_cons, List.mem_cons]
              exact Or.inl rfl
            · rw [selectedAdjacencyPath_range] at hfirst
              exact hfirst
          · obtain ⟨e, he, hxe⟩ := ih SimpleGraph.Walk.not_nil_cons htail
            refine ⟨e, ?_, hxe⟩
            rw [SimpleGraph.Walk.edges_cons, List.mem_cons]
            exact Or.inr he

/-- Helper for Remark 64.2: the ambient endpoints of an incidence edge are exactly the
ambient images of the two vertices belonging to that incidence edge. -/
private lemma selectedIncidenceEdge_endpoint_iff
    {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge)
    (e : (selectedIncidenceGraph L s).edgeSet) (x : X) :
    (x = L.edge (selectedIncidenceGraph_edgeEquiv L s e).1 0 ∨
      x = L.edge (selectedIncidenceGraph_edgeEquiv L s e).1 1) ↔
      ∃ q, q ∈ e.1 ∧ (q : X) = x := by
  -- Map the canonical endpoint-pair equation once from selected endpoints to `X`.
  have hp := selectedIncidenceGraph_edgeEquiv_endpointPair L s e
  have hm := congrArg (Sym2.map (fun q : SelectedEndpoint L s ↦ (q : X))) hp
  have hpAmbient :
      s(L.edge (selectedIncidenceGraph_edgeEquiv L s e).1 0,
        L.edge (selectedIncidenceGraph_edgeEquiv L s e).1 1) =
          Sym2.map (fun q : SelectedEndpoint L s ↦ (q : X)) e.1 := by
    simpa only [selectedEdgeEndpointPair_map_coe] using hm
  constructor
  · intro hx
    have hxPair : x ∈ s(L.edge (selectedIncidenceGraph_edgeEquiv L s e).1 0,
        L.edge (selectedIncidenceGraph_edgeEquiv L s e).1 1) :=
      Sym2.mem_iff.mpr hx
    rw [hpAmbient, Sym2.mem_map] at hxPair
    exact hxPair
  · rintro ⟨q, hqe, hqx⟩
    have hxPair : x ∈ Sym2.map (fun z : SelectedEndpoint L s ↦ (z : X)) e.1 :=
      Sym2.mem_map.mpr ⟨q, hqe, hqx⟩
    rw [← hpAmbient, Sym2.mem_iff] at hxPair
    exact hxPair

/-- Helper for Remark 64.2: if two nonempty incidence walks have at most one common support
vertex, every intersection point of their realized ranges is that common vertex. -/
private lemma selectedWalkPath_intersection_subset_commonSupport
    {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge)
    {a b c d : SelectedEndpoint L s}
    (p : (selectedIncidenceGraph L s).Walk a b)
    (q : (selectedIncidenceGraph L s).Walk c d)
    (hpNil : ¬ p.Nil) (hqNil : ¬ q.Nil)
    (hcommon : {z | z ∈ p.support ∧ z ∈ q.support}.Subsingleton)
    {x : X} (hxp : x ∈ Set.range (selectedWalkPath L s p))
    (hxq : x ∈ Set.range (selectedWalkPath L s q)) :
    ∃ z, z ∈ p.support ∧ z ∈ q.support ∧ (z : X) = x := by
  obtain ⟨ep, hep, hxep⟩ := selectedWalkPath_range_edge_witness L s p hpNil hxp
  obtain ⟨eq, heq, hxeq⟩ := selectedWalkPath_range_edge_witness L s q hqNil hxq
  -- The same incidence edge would put both of its distinct endpoints in the common support.
  have hedgeNe : ep ≠ eq := by
    intro hedge
    subst eq
    have hp0 := p.mem_support_of_mem_edges hep (Sym2.out_fst_mem ep.1)
    have hp1 := p.mem_support_of_mem_edges hep (Sym2.out_snd_mem ep.1)
    have hq0 := q.mem_support_of_mem_edges heq (Sym2.out_fst_mem ep.1)
    have hq1 := q.mem_support_of_mem_edges heq (Sym2.out_snd_mem ep.1)
    have hout := hcommon ⟨hp0, hq0⟩ ⟨hp1, hq1⟩
    apply (selectedIncidenceGraph L s).not_isDiag_of_mem_edgeSet ep.2
    rw [← ep.1.out_eq, Sym2.mk_isDiag_iff]
    exact hout
  have hselectedNe :
      (selectedIncidenceGraph_edgeEquiv L s ep).1 ≠
        (selectedIncidenceGraph_edgeEquiv L s eq).1 := by
    intro h
    apply hedgeNe
    apply (selectedIncidenceGraph_edgeEquiv L s).injective
    exact Subtype.ext h
  -- Distinct realized edges meet at endpoints; transport their endpoint witnesses back to the
  -- incidence graph and identify them through the ambient subtype coercion.
  have hendpoints := L.inter_subset_endpoints hselectedNe ⟨hxep, hxeq⟩
  have hepEndpoint :
      x = L.edge (selectedIncidenceGraph_edgeEquiv L s ep).1 0 ∨
        x = L.edge (selectedIncidenceGraph_edgeEquiv L s ep).1 1 := by
    simpa only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff] using
      hendpoints.1
  have heqEndpoint :
      x = L.edge (selectedIncidenceGraph_edgeEquiv L s eq).1 0 ∨
        x = L.edge (selectedIncidenceGraph_edgeEquiv L s eq).1 1 := by
    simpa only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff] using
      hendpoints.2
  obtain ⟨zp, hzp, hzpx⟩ := (selectedIncidenceEdge_endpoint_iff L s ep x).1 hepEndpoint
  obtain ⟨zq, hzq, hzqx⟩ := (selectedIncidenceEdge_endpoint_iff L s eq x).1 heqEndpoint
  have hz : zp = zq := Subtype.ext (hzpx.trans hzqx.symm)
  subst zq
  refine ⟨zp, p.mem_support_of_mem_edges hep hzp,
    q.mem_support_of_mem_edges heq hzq, hzpx⟩

/-- Helper for Remark 64.2: an adjacency arc is disjoint from a realized walk when neither
of its incidence endpoints occurs in the walk support. -/
private lemma selectedAdjacencyPath_disjoint_selectedWalkPath_of_support
    {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge)
    {a b c d : SelectedEndpoint L s}
    (h : (selectedIncidenceGraph L s).Adj a b)
    (p : (selectedIncidenceGraph L s).Walk c d)
    (habsent : ∀ q, q ∈ s(a, b) → q ∉ p.support) :
    Disjoint (Set.range (selectedAdjacencyPath L s h))
      (Set.range (selectedWalkPath L s p)) := by
  induction p with
  | nil =>
      -- A common point with a reflexive walk would be one of the forbidden endpoints.
      rw [Set.disjoint_left]
      intro x hx hp
      rw [selectedWalkPath, Path.refl_range, Set.mem_singleton_iff] at hp
      subst x
      rcases (selectedEndpoint_mem_selectedAdjacencyPath_range_iff L s h _).1 hx with
        hca | hcb
      · apply habsent a (Sym2.mem_mk_left a b)
        simpa only [SimpleGraph.Walk.support_nil, List.mem_singleton] using hca.symm
      · apply habsent b (Sym2.mem_mk_right a b)
        simpa only [SimpleGraph.Walk.support_nil, List.mem_singleton] using hcb.symm
  | @cons c e d k p ih =>
      -- Endpoint absence makes the distinguished incidence edge disjoint from the first edge.
      have hpairDisjoint : ∀ q, q ∈ s(a, b) → q ∉ s(c, e) := by
        intro q hqab hqce
        rcases Sym2.mem_iff.mp hqce with hqc | hqe
        · subst q
          exact habsent c hqab (by simp)
        · subst q
          exact habsent e hqab (by simp)
      have hne : incidenceEdgeOfAdj L s h ≠ incidenceEdgeOfAdj L s k := by
        intro heq
        have hpairEq : s(a, b) = s(c, e) := by
          simpa only [incidenceEdgeOfAdj] using congrArg Subtype.val heq
        apply hpairDisjoint a (Sym2.mem_mk_left a b)
        rw [← hpairEq]
        exact Sym2.mem_mk_left a b
      have hfirst := selectedAdjacencyPath_disjoint_of_incidence_disjoint
        L s h k hne hpairDisjoint
      have habsentTail : ∀ q, q ∈ s(a, b) → q ∉ p.support := by
        intro q hqab hqp
        exact habsent q hqab (SimpleGraph.Walk.support_subset_support_cons p k hqp)
      cases p with
      | nil =>
          -- A one-edge walk has exactly the first arc as its realization.
          simpa only [selectedWalkPath] using hfirst
      | cons m p =>
          -- For a longer walk, combine disjointness from the first arc and from the tail.
          rw [selectedWalkPath, Path.trans_range, Set.disjoint_union_right]
          exact ⟨hfirst, ih habsentTail⟩

/-- Helper for Remark 64.2: the first arc of a simple walk meets the realized nonempty tail
exactly at their common incidence vertex. -/
private lemma selectedAdjacencyPath_inter_selectedWalkPath_eq_singleton
    {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge)
    {a b c : SelectedEndpoint L s}
    (h : (selectedIncidenceGraph L s).Adj a b)
    (p : (selectedIncidenceGraph L s).Walk b c)
    (hp : (SimpleGraph.Walk.cons h p).IsPath) (hnil : ¬ p.Nil) :
    Set.range (selectedAdjacencyPath L s h) ∩
        Set.range (selectedWalkPath L s p) = {(b : X)} := by
  cases p with
  | nil =>
      -- The tail's nonemptiness excludes the reflexive-walk case.
      exact (hnil SimpleGraph.Walk.Nil.nil).elim
  | cons k p =>
      have hpTail : (SimpleGraph.Walk.cons k p).IsPath := hp.of_cons
      -- Edge noduplication ensures that the first edge differs from the tail's first edge.
      have hedgeNe : incidenceEdgeOfAdj L s h ≠ incidenceEdgeOfAdj L s k := by
        intro hedgeEq
        have hfirstNotMem : s(a, b) ∉ (SimpleGraph.Walk.cons k p).edges := by
          have hnodup := hp.edges_nodup
          rw [SimpleGraph.Walk.edges_cons, List.nodup_cons] at hnodup
          exact hnodup.1
        apply hfirstNotMem
        rw [SimpleGraph.Walk.edges_cons, List.mem_cons]
        exact Or.inl (congrArg Subtype.val hedgeEq)
      have hinter := selectedAdjacencyPath_inter_eq_singleton L s h k hedgeNe
      cases p with
      | nil =>
          -- For a one-edge tail this is the established adjacent-arc intersection formula.
          simpa only [selectedWalkPath] using hinter
      | cons m p =>
          -- Simplicity removes both endpoints of the first edge from the tail after `k`.
          have haAbsent : a ∉ (SimpleGraph.Walk.cons k
              (SimpleGraph.Walk.cons m p)).support :=
            (SimpleGraph.Walk.cons_isPath_iff h _).1 hp |>.2
          have hbAbsent : b ∉ (SimpleGraph.Walk.cons m p).support :=
            (SimpleGraph.Walk.cons_isPath_iff k _).1 hpTail |>.2
          have habsent : ∀ q, q ∈ s(a, b) →
              q ∉ (SimpleGraph.Walk.cons m p).support := by
            intro q hqab hqSupport
            rcases Sym2.mem_iff.mp hqab with hqa | hqb
            · subst q
              exact haAbsent (SimpleGraph.Walk.support_subset_support_cons _ k hqSupport)
            · subst q
              exact hbAbsent hqSupport
          have hdisjoint := selectedAdjacencyPath_disjoint_selectedWalkPath_of_support
            L s h (SimpleGraph.Walk.cons m p) habsent
          have hinterRest : Set.range (selectedAdjacencyPath L s h) ∩
              Set.range (selectedWalkPath L s (SimpleGraph.Walk.cons m p)) = ∅ :=
            Set.disjoint_iff_inter_eq_empty.mp hdisjoint
          -- Normalize the realized tail range into its first arc and remaining walk.
          rw [selectedWalkPath, Path.trans_range, Set.inter_union_distrib_left,
            hinter, hinterRest, Set.union_empty]

/-- Helper for Remark 64.2: every nonempty simple incidence walk realizes as an embedded
topological path. -/
private lemma selectedWalkPath_isEmbedding_of_isPath
    {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge)
    {a b : SelectedEndpoint L s}
    (p : (selectedIncidenceGraph L s).Walk a b)
    (hp : p.IsPath) (hnil : ¬ p.Nil) :
    Topology.IsEmbedding (selectedWalkPath L s p) := by
  -- Route correction: the nonstuttering realization makes the one-edge base case exactly the
  -- selected adjacency arc; only genuinely longer walks require the path-gluing theorem.
  -- Local instance justification (stored presentation data): Hausdorffness is a field of `L`
  -- and is needed only by the generic embedded-path concatenation theorem below.
  letI : T2Space X := L.t2Space
  induction p with
  | nil =>
      -- The nonempty hypothesis eliminates the constant-walk case.
      exact (hnil SimpleGraph.Walk.Nil.nil).elim
  | cons h p ih =>
      cases p with
      | nil =>
          -- A one-edge walk now realizes as its embedded selected adjacency path directly.
          simpa only [selectedWalkPath] using selectedAdjacencyPath_isEmbedding L s h
      | @cons c d e k p =>
          -- Simplicity passes to the nonempty tail, whose realization is embedded inductively.
          have hpTail : (SimpleGraph.Walk.cons k p).IsPath := hp.of_cons
          have htailEmbedding :
              Topology.IsEmbedding (selectedWalkPath L s (SimpleGraph.Walk.cons k p)) :=
            ih hpTail SimpleGraph.Walk.not_nil_cons
          -- The first arc and the entire embedded tail meet only at their common endpoint.
          have hinter := selectedAdjacencyPath_inter_selectedWalkPath_eq_singleton
            L s h (SimpleGraph.Walk.cons k p) hp SimpleGraph.Walk.not_nil_cons
          rw [selectedWalkPath]
          exact Path.trans_isEmbedding_of_range_inter_eq_singleton
            (selectedAdjacencyPath L s h) (selectedWalkPath L s (SimpleGraph.Walk.cons k p))
            (selectedAdjacencyPath_isEmbedding L s h) htailEmbedding hinter

/-- Helper for Remark 64.2: distinct routes in a Kuratowski path system can meet only at
the realized image of a branch vertex common to their abstract edges. -/
private lemma KuratowskiPathSystem.realizedRoute_intersection_branch
    {A : Type u} {X : Type v} [TopologicalSpace X]
    {K : SimpleGraph A} (L : FiniteLinearGraph.{v, v} X) (s : Set L.Edge)
    (P : KuratowskiPathSystem K (selectedIncidenceGraph L s))
    {e f : K.edgeSet} (hef : e ≠ f) {x : X}
    (hxe : x ∈ Set.range (selectedWalkPath L s (P.route e)))
    (hxf : x ∈ Set.range (selectedWalkPath L s (P.route f))) :
    ∃ a, a ∈ e.1 ∧ a ∈ f.1 ∧ (P.branch a : X) = x := by
  have hcommon :
      {z | z ∈ (P.route e).support ∧ z ∈ (P.route f).support}.Subsingleton := by
    intro z hz w hw
    obtain ⟨a, hae, haf, haz⟩ := P.route_intersection hef hz.1 hz.2
    obtain ⟨b, hbe, hbf, hbw⟩ := P.route_intersection hef hw.1 hw.2
    have hab : a = b := by
      by_contra hab
      apply hef
      apply Subtype.ext
      exact Sym2.eq_of_ne_mem hab hae hbe haf hbf
    -- Equality of the abstract branch vertices identifies their selected endpoint images.
    rw [← haz, ← hbw, hab]
  obtain ⟨z, hze, hzf, hzx⟩ := selectedWalkPath_intersection_subset_commonSupport
    L s (P.route e) (P.route f) (P.route_not_nil e) (P.route_not_nil f)
      hcommon hxe hxf
  obtain ⟨a, hae, haf, haz⟩ := P.route_intersection hef hze hzf
  refine ⟨a, hae, haf, ?_⟩
  exact congrArg Subtype.val haz |>.trans hzx

/-- Helper for Remark 64.2: the carrier swept out by all realized routes of a path system. -/
private def realizedRouteUnion
    {A : Type u} {X : Type v} [TopologicalSpace X]
    {K : SimpleGraph A} (L : FiniteLinearGraph.{v, v} X) (s : Set L.Edge)
    (P : KuratowskiPathSystem K (selectedIncidenceGraph L s)) : Set X :=
  ⋃ e : K.edgeSet, Set.range (selectedWalkPath L s (P.route e))

/-- Helper for Remark 64.2: every point on a realized route belongs to the route-union
carrier. -/
private lemma selectedWalkPath_mem_realizedRouteUnion
    {A : Type u} {X : Type v} [TopologicalSpace X]
    {K : SimpleGraph A} (L : FiniteLinearGraph.{v, v} X) (s : Set L.Edge)
    (P : KuratowskiPathSystem K (selectedIncidenceGraph L s))
    (e : K.edgeSet) (t : unitInterval) :
    selectedWalkPath L s (P.route e) t ∈ realizedRouteUnion L s P := by
  -- Select the abstract edge and the route parameter in the indexed union.
  rw [realizedRouteUnion, Set.mem_iUnion]
  exact ⟨e, Set.mem_range_self t⟩

/-- Helper for Remark 64.2: a path-system route regarded as an edge of its route-union
subtype. -/
private noncomputable def realizedRouteEdge
    {A : Type u} {X : Type v} [TopologicalSpace X]
    {K : SimpleGraph A} (L : FiniteLinearGraph.{v, v} X) (s : Set L.Edge)
    (P : KuratowskiPathSystem K (selectedIncidenceGraph L s)) :
    K.edgeSet → unitInterval → realizedRouteUnion L s P :=
  fun e t ↦ ⟨selectedWalkPath L s (P.route e) t,
    selectedWalkPath_mem_realizedRouteUnion L s P e t⟩

/-- Helper for Remark 64.2: coercing a route-union edge to the ambient carrier recovers its
realized route. -/
private lemma realizedRouteEdge_coe
    {A : Type u} {X : Type v} [TopologicalSpace X]
    {K : SimpleGraph A} (L : FiniteLinearGraph.{v, v} X) (s : Set L.Edge)
    (P : KuratowskiPathSystem K (selectedIncidenceGraph L s)) (e : K.edgeSet) :
    Subtype.val ∘ realizedRouteEdge L s P e = selectedWalkPath L s (P.route e) := by
  -- The subtype edge stores the same ambient path pointwise.
  rfl

/-- Helper for Remark 64.2: the initial point of a route-union edge is its first branch
vertex in the ambient carrier. -/
private lemma realizedRouteEdge_zero_coe
    {A : Type u} {X : Type v} [TopologicalSpace X]
    {K : SimpleGraph A} (L : FiniteLinearGraph.{v, v} X) (s : Set L.Edge)
    (P : KuratowskiPathSystem K (selectedIncidenceGraph L s)) (e : K.edgeSet) :
    ((realizedRouteEdge L s P e 0 : realizedRouteUnion L s P) : X) =
      P.branch e.1.out.1 := by
  -- The selected walk path has the prescribed combinatorial source.
  exact Path.source (selectedWalkPath L s (P.route e))

/-- Helper for Remark 64.2: the terminal point of a route-union edge is its second branch
vertex in the ambient carrier. -/
private lemma realizedRouteEdge_one_coe
    {A : Type u} {X : Type v} [TopologicalSpace X]
    {K : SimpleGraph A} (L : FiniteLinearGraph.{v, v} X) (s : Set L.Edge)
    (P : KuratowskiPathSystem K (selectedIncidenceGraph L s)) (e : K.edgeSet) :
    ((realizedRouteEdge L s P e 1 : realizedRouteUnion L s P) : X) =
      P.branch e.1.out.2 := by
  -- The selected walk path has the prescribed combinatorial target.
  exact Path.target (selectedWalkPath L s (P.route e))

/-- Helper for Remark 64.2: every route-union edge is topologically embedded. -/
private lemma realizedRouteEdge_isEmbedding
    {A : Type u} {X : Type v} [TopologicalSpace X]
    {K : SimpleGraph A} (L : FiniteLinearGraph.{v, v} X) (s : Set L.Edge)
    (P : KuratowskiPathSystem K (selectedIncidenceGraph L s)) (e : K.edgeSet) :
    Topology.IsEmbedding (realizedRouteEdge L s P e) := by
  -- Check embedding after the canonical subtype inclusion, where it is the verified walk path.
  apply Topology.IsEmbedding.subtypeVal.of_comp_iff.mp
  rw [realizedRouteEdge_coe]
  exact selectedWalkPath_isEmbedding_of_isPath L s (P.route e)
    (P.route_isPath e) (P.route_not_nil e)

/-- Helper for Remark 64.2: the route-union edges cover their subtype carrier. -/
private lemma realizedRouteEdge_iUnion_range
    {A : Type u} {X : Type v} [TopologicalSpace X]
    {K : SimpleGraph A} (L : FiniteLinearGraph.{v, v} X) (s : Set L.Edge)
    (P : KuratowskiPathSystem K (selectedIncidenceGraph L s)) :
    ⋃ e, Set.range (realizedRouteEdge L s P e) = Set.univ := by
  ext x
  constructor
  · exact fun _ ↦ Set.mem_univ x
  · intro _
    obtain ⟨e, he⟩ := Set.mem_iUnion.mp x.2
    obtain ⟨t, ht⟩ := he
    rw [Set.mem_iUnion]
    refine ⟨e, t, ?_⟩
    -- The ambient equality determines equality in the route-union subtype.
    exact Subtype.ext ht

/-- Helper for Remark 64.2: a common branch vertex identifies an intersection point with
one endpoint of the corresponding route-union edge. -/
private lemma realizedRouteEdge_eq_endpoint_of_mem
    {A : Type u} {X : Type v} [TopologicalSpace X]
    {K : SimpleGraph A} (L : FiniteLinearGraph.{v, v} X) (s : Set L.Edge)
    (P : KuratowskiPathSystem K (selectedIncidenceGraph L s))
    (e : K.edgeSet) (x : realizedRouteUnion L s P) {a : A}
    (hae : a ∈ e.1) (hax : (P.branch a : X) = x.1) :
    x = realizedRouteEdge L s P e 0 ∨ x = realizedRouteEdge L s P e 1 := by
  have haout : a = e.1.out.1 ∨ a = e.1.out.2 := by
    rw [← e.1.out_eq] at hae
    exact Sym2.mem_iff.mp hae
  rcases haout with rfl | rfl
  · apply Or.inl
    apply Subtype.ext
    exact hax.symm.trans (realizedRouteEdge_zero_coe L s P e).symm
  · apply Or.inr
    apply Subtype.ext
    exact hax.symm.trans (realizedRouteEdge_one_coe L s P e).symm

/-- Helper for Remark 64.2: distinct route-union edges intersect only at endpoints of both
edges. -/
private lemma realizedRouteEdge_inter_subset_endpoints
    {A : Type u} {X : Type v} [TopologicalSpace X]
    {K : SimpleGraph A} (L : FiniteLinearGraph.{v, v} X) (s : Set L.Edge)
    (P : KuratowskiPathSystem K (selectedIncidenceGraph L s))
    {e f : K.edgeSet} (hef : e ≠ f) :
    Set.range (realizedRouteEdge L s P e) ∩ Set.range (realizedRouteEdge L s P f) ⊆
      ({realizedRouteEdge L s P e 0, realizedRouteEdge L s P e 1} ∩
        {realizedRouteEdge L s P f 0, realizedRouteEdge L s P f 1} :
          Set (realizedRouteUnion L s P)) := by
  intro x hx
  obtain ⟨te, hte⟩ := hx.1
  obtain ⟨tf, htf⟩ := hx.2
  have hxe : x.1 ∈ Set.range (selectedWalkPath L s (P.route e)) :=
    ⟨te, congrArg Subtype.val hte⟩
  have hxf : x.1 ∈ Set.range (selectedWalkPath L s (P.route f)) :=
    ⟨tf, congrArg Subtype.val htf⟩
  obtain ⟨a, hae, haf, hax⟩ := P.realizedRoute_intersection_branch L s hef hxe hxf
  have heEndpoint := realizedRouteEdge_eq_endpoint_of_mem L s P e x hae hax
  have hfEndpoint := realizedRouteEdge_eq_endpoint_of_mem L s P f x haf hax
  -- Repackage the two endpoint alternatives as membership in the endpoint-set intersection.
  simpa only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff] using
    And.intro heEndpoint hfEndpoint

/-- Helper for Remark 64.2: the intersection of two distinct route-union edges contains at
most one point. -/
private lemma realizedRouteEdge_inter_subsingleton
    {A : Type u} {X : Type v} [TopologicalSpace X]
    {K : SimpleGraph A} (L : FiniteLinearGraph.{v, v} X) (s : Set L.Edge)
    (P : KuratowskiPathSystem K (selectedIncidenceGraph L s))
    {e f : K.edgeSet} (hef : e ≠ f) :
    (Set.range (realizedRouteEdge L s P e) ∩
      Set.range (realizedRouteEdge L s P f)).Subsingleton := by
  intro x hx y hy
  obtain ⟨te, hte⟩ := hx.1
  obtain ⟨tf, htf⟩ := hx.2
  obtain ⟨ue, hue⟩ := hy.1
  obtain ⟨uf, huf⟩ := hy.2
  have hxe : x.1 ∈ Set.range (selectedWalkPath L s (P.route e)) :=
    ⟨te, congrArg Subtype.val hte⟩
  have hxf : x.1 ∈ Set.range (selectedWalkPath L s (P.route f)) :=
    ⟨tf, congrArg Subtype.val htf⟩
  have hye : y.1 ∈ Set.range (selectedWalkPath L s (P.route e)) :=
    ⟨ue, congrArg Subtype.val hue⟩
  have hyf : y.1 ∈ Set.range (selectedWalkPath L s (P.route f)) :=
    ⟨uf, congrArg Subtype.val huf⟩
  obtain ⟨a, hae, haf, hax⟩ := P.realizedRoute_intersection_branch L s hef hxe hxf
  obtain ⟨b, hbe, hbf, hby⟩ := P.realizedRoute_intersection_branch L s hef hye hyf
  have hab : a = b := by
    by_contra hab
    apply hef
    apply Subtype.ext
    exact Sym2.eq_of_ne_mem hab hae hbe haf hbf
  apply Subtype.ext
  calc
    x.1 = P.branch a := hax.symm
    _ = P.branch b := congrArg (fun z ↦ (P.branch z : X)) hab
    _ = y.1 := hby

/-- Helper for Remark 64.2: full graph support puts every branch vertex in the route-union
carrier. -/
private lemma branch_mem_realizedRouteUnion
    {A : Type} {X : Type v} [TopologicalSpace X]
    {K : SimpleGraph A} (L : FiniteLinearGraph.{v, v} X) (s : Set L.Edge)
    (P : KuratowskiPathSystem K (selectedIncidenceGraph L s))
    (hsupport : K.support = Set.univ) (a : A) :
    (P.branch a : X) ∈ realizedRouteUnion L s P := by
  have haSupport : a ∈ K.support := by
    rw [hsupport]
    exact Set.mem_univ a
  obtain ⟨b, hab⟩ := K.mem_support.mp haSupport
  let e : K.edgeSet := ⟨s(a, b), hab⟩
  have haRoute : P.branch a ∈ (P.route e).support := by
    apply (P.branch_mem_route_support_iff e a).2
    exact Sym2.mem_mk_left a b
  -- The support/range bridge places the branch on the selected route indexed by `e`.
  rw [realizedRouteUnion, Set.mem_iUnion]
  exact ⟨e, (selectedEndpoint_mem_selectedWalkPath_range_iff L s (P.route e)
    (P.branch a)).2 haRoute⟩

/-- Helper for Remark 64.2: the branch map with codomain restricted to the route-union
carrier. -/
private def realizedBranch
    {A : Type} {X : Type v} [TopologicalSpace X]
    {K : SimpleGraph A} (L : FiniteLinearGraph.{v, v} X) (s : Set L.Edge)
    (P : KuratowskiPathSystem K (selectedIncidenceGraph L s))
    (hsupport : K.support = Set.univ) : A → realizedRouteUnion L s P :=
  fun a ↦ ⟨P.branch a, branch_mem_realizedRouteUnion L s P hsupport a⟩

/-- Helper for Remark 64.2: restricting the branch map to the route-union carrier preserves
injectivity. -/
private lemma realizedBranch_injective
    {A : Type} {X : Type v} [TopologicalSpace X]
    {K : SimpleGraph A} (L : FiniteLinearGraph.{v, v} X) (s : Set L.Edge)
    (P : KuratowskiPathSystem K (selectedIncidenceGraph L s))
    (hsupport : K.support = Set.univ) :
    Function.Injective (realizedBranch L s P hsupport) := by
  intro a b hab
  -- Coercion to the selected-endpoint type recovers the original injective branch map.
  exact P.branch_injective (Subtype.ext
    (congrArg (fun z : realizedRouteUnion L s P ↦ (z : X)) hab))

/-- Helper for Remark 64.2: abstract incidence is exactly incidence with the two endpoints
of the corresponding route-union edge. -/
private lemma realizedBranch_eq_endpoint_iff
    {A : Type} {X : Type v} [TopologicalSpace X]
    {K : SimpleGraph A} (L : FiniteLinearGraph.{v, v} X) (s : Set L.Edge)
    (P : KuratowskiPathSystem K (selectedIncidenceGraph L s))
    (hsupport : K.support = Set.univ) (e : K.edgeSet) (a : A) :
    a ∈ e.1 ↔
      realizedBranch L s P hsupport a = realizedRouteEdge L s P e 0 ∨
        realizedBranch L s P hsupport a = realizedRouteEdge L s P e 1 := by
  constructor
  · intro hae
    have haout : a = e.1.out.1 ∨ a = e.1.out.2 := by
      rw [← e.1.out_eq] at hae
      exact Sym2.mem_iff.mp hae
    rcases haout with rfl | rfl
    · apply Or.inl
      apply Subtype.ext
      exact (realizedRouteEdge_zero_coe L s P e).symm
    · apply Or.inr
      apply Subtype.ext
      exact (realizedRouteEdge_one_coe L s P e).symm
  · rintro (haZero | haOne)
    · have haout : a = e.1.out.1 := by
        apply P.branch_injective
        exact Subtype.ext (congrArg Subtype.val haZero |>.trans
          (realizedRouteEdge_zero_coe L s P e))
      rw [haout]
      exact Sym2.out_fst_mem e.1
    · have haout : a = e.1.out.2 := by
        apply P.branch_injective
        exact Subtype.ext (congrArg Subtype.val haOne |>.trans
          (realizedRouteEdge_one_coe L s P e))
      rw [haout]
      exact Sym2.out_snd_mem e.1

/-- Helper for Remark 64.2: the universe-lifted edge index uses the route selected by its
underlying abstract edge. -/
private noncomputable def liftedRealizedRouteEdge
    {A : Type} {X : Type v} [TopologicalSpace X]
    {K : SimpleGraph A} (L : FiniteLinearGraph.{v, v} X) (s : Set L.Edge)
    (P : KuratowskiPathSystem K (selectedIncidenceGraph L s)) :
    ULift.{v} K.edgeSet → unitInterval → realizedRouteUnion L s P :=
  fun e ↦ realizedRouteEdge L s P e.down

/-- Helper for Remark 64.2: each universe-lifted route edge is embedded. -/
private lemma liftedRealizedRouteEdge_isEmbedding
    {A : Type} {X : Type v} [TopologicalSpace X]
    {K : SimpleGraph A} (L : FiniteLinearGraph.{v, v} X) (s : Set L.Edge)
    (P : KuratowskiPathSystem K (selectedIncidenceGraph L s))
    (e : ULift.{v} K.edgeSet) :
    Topology.IsEmbedding (liftedRealizedRouteEdge L s P e) := by
  -- Removing the universe lift exposes the already verified route edge.
  exact realizedRouteEdge_isEmbedding L s P e.down

/-- Helper for Remark 64.2: the universe-lifted route edges still cover the route union. -/
private lemma liftedRealizedRouteEdge_iUnion_range
    {A : Type} {X : Type v} [TopologicalSpace X]
    {K : SimpleGraph A} (L : FiniteLinearGraph.{v, v} X) (s : Set L.Edge)
    (P : KuratowskiPathSystem K (selectedIncidenceGraph L s)) :
    ⋃ e : ULift.{v} K.edgeSet, Set.range (liftedRealizedRouteEdge L s P e) = Set.univ := by
  ext x
  constructor
  · exact fun _ ↦ Set.mem_univ x
  · intro _
    obtain ⟨e, he⟩ := Set.mem_iUnion.mp x.2
    rw [Set.mem_iUnion]
    refine ⟨ULift.up e, ?_⟩
    obtain ⟨t, ht⟩ := he
    exact ⟨t, Subtype.ext ht⟩

/-- Helper for Remark 64.2: distinct universe-lifted route edges meet only at endpoints. -/
private lemma liftedRealizedRouteEdge_inter_subset_endpoints
    {A : Type} {X : Type v} [TopologicalSpace X]
    {K : SimpleGraph A} (L : FiniteLinearGraph.{v, v} X) (s : Set L.Edge)
    (P : KuratowskiPathSystem K (selectedIncidenceGraph L s))
    {e f : ULift.{v} K.edgeSet} (hef : e ≠ f) :
    Set.range (liftedRealizedRouteEdge L s P e) ∩
        Set.range (liftedRealizedRouteEdge L s P f) ⊆
      ({liftedRealizedRouteEdge L s P e 0, liftedRealizedRouteEdge L s P e 1} ∩
        {liftedRealizedRouteEdge L s P f 0, liftedRealizedRouteEdge L s P f 1} :
          Set (realizedRouteUnion L s P)) := by
  have hdown : e.down ≠ f.down := by
    intro h
    exact hef (ULift.ext e f h)
  exact realizedRouteEdge_inter_subset_endpoints L s P hdown

/-- Helper for Remark 64.2: intersections of distinct universe-lifted route edges are
subsingletons. -/
private lemma liftedRealizedRouteEdge_inter_subsingleton
    {A : Type} {X : Type v} [TopologicalSpace X]
    {K : SimpleGraph A} (L : FiniteLinearGraph.{v, v} X) (s : Set L.Edge)
    (P : KuratowskiPathSystem K (selectedIncidenceGraph L s))
    {e f : ULift.{v} K.edgeSet} (hef : e ≠ f) :
    (Set.range (liftedRealizedRouteEdge L s P e) ∩
      Set.range (liftedRealizedRouteEdge L s P f)).Subsingleton := by
  have hdown : e.down ≠ f.down := by
    intro h
    exact hef (ULift.ext e f h)
  exact realizedRouteEdge_inter_subsingleton L s P hdown

/-- Helper for Remark 64.2: the realized routes form a finite linear graph on their union. -/
private noncomputable def realizedPathSystemLinearGraph
    {A : Type} {X : Type v} [TopologicalSpace X] [T2Space X]
    {K : SimpleGraph A} [Finite K.edgeSet]
    (L : FiniteLinearGraph.{v, v} X) (s : Set L.Edge)
    (P : KuratowskiPathSystem K (selectedIncidenceGraph L s)) :
    FiniteLinearGraph.{v, v} (realizedRouteUnion L s P) :=
  { t2Space := inferInstance
    Edge := ULift.{v} K.edgeSet
    edgeFinite := inferInstance
    edge := liftedRealizedRouteEdge L s P
    edgeEmbedding := liftedRealizedRouteEdge_isEmbedding L s P
    iUnion_range := liftedRealizedRouteEdge_iUnion_range L s P
    interSubsetEndpoints := liftedRealizedRouteEdge_inter_subset_endpoints L s P
    interSubsingleton := liftedRealizedRouteEdge_inter_subsingleton L s P }

/-- Helper for Remark 64.2: a full-support path system determines a linear realization on
the union of its realized routes. -/
private noncomputable def realizedPathSystemLinearRealization
    {A : Type} {X : Type v} [TopologicalSpace X] [T2Space X]
    {K : SimpleGraph A} [Finite K.edgeSet]
    (L : FiniteLinearGraph.{v, v} X) (s : Set L.Edge)
    (P : KuratowskiPathSystem K (selectedIncidenceGraph L s))
    (hsupport : K.support = Set.univ) : K.LinearRealization.{0, v} :=
  { Carrier := TopCat.of (realizedRouteUnion L s P)
    linearGraph := realizedPathSystemLinearGraph L s P
    vertex := realizedBranch L s P hsupport
    vertex_injective := realizedBranch_injective L s P hsupport
    edgeEquiv := Equiv.ulift.symm
    vertex_eq_endpoint_iff := realizedBranch_eq_endpoint_iff L s P hsupport }

/-- Helper for Remark 64.2: a path-system realization embeds in the selected union of the
original finite linear graph. -/
private lemma KuratowskiPathSystem.embedsEdgeUnion
    {A : Type} {X : Type v} [TopologicalSpace X]
    {K : SimpleGraph A} [Finite K.edgeSet]
    (L : FiniteLinearGraph.{v, v} X) (s : Set L.Edge)
    (P : KuratowskiPathSystem K (selectedIncidenceGraph L s))
    (hsupport : K.support = Set.univ) :
    ∃ S : K.LinearRealization.{0, v},
      ∃ e : S.Carrier → edgeUnion L s, Topology.IsEmbedding e := by
  -- Local instance justification (stored presentation data): the route-union subtype inherits
  -- Hausdorffness from the ambient structure field of `L`.
  letI : T2Space X := L.t2Space
  let S := realizedPathSystemLinearRealization L s P hsupport
  have hsubset : realizedRouteUnion L s P ⊆ edgeUnion L s := by
    intro x hx
    obtain ⟨e, he⟩ := Set.mem_iUnion.mp hx
    exact selectedWalkPath_range_subset L s (P.route e) he
  -- The canonical inclusion crosses the subtype boundary once and is an embedding.
  exact ⟨S, Set.inclusion hsubset, Topology.IsEmbedding.inclusion hsubset⟩

/-- Helper for Remark 64.2: every vertex of the utilities graph belongs to an edge. -/
private lemma utilitiesGraph_support :
    (completeBipartiteGraph (Fin 3) (Fin 3)).support = Set.univ := by
  apply Set.eq_univ_of_forall
  intro a
  rw [SimpleGraph.mem_support]
  cases a with
  | inl i =>
      -- Any vertex on the left is adjacent to vertex `0` on the right.
      exact ⟨Sum.inr 0, Or.inl ⟨rfl, rfl⟩⟩
  | inr i =>
      -- Any vertex on the right is adjacent to vertex `0` on the left.
      exact ⟨Sum.inl 0, Or.inr ⟨rfl, rfl⟩⟩

/-- Helper for Remark 64.2: every vertex of the complete graph on five vertices belongs to
an edge. -/
private lemma completeGraphFive_support :
    (SimpleGraph.completeGraph (Fin 5)).support = Set.univ := by
  -- A five-element vertex type is nontrivial, so the complete graph has full support.
  exact SimpleGraph.support_top_of_nontrivial

/-- Helper for Remark 64.2: a utilities-graph path system gives the required embedded
utilities-graph realization. -/
private lemma utilitiesPathSystem_embedsEdgeUnion
    {X : Type v} [TopologicalSpace X]
    (L : FiniteLinearGraph.{v, v} X) (s : Set L.Edge)
    (P : KuratowskiPathSystem (completeBipartiteGraph (Fin 3) (Fin 3))
      (selectedIncidenceGraph L s)) :
    ∃ S : (completeBipartiteGraph (Fin 3) (Fin 3)).LinearRealization.{0, v},
      ∃ e : S.Carrier → edgeUnion L s, Topology.IsEmbedding e := by
  -- Apply the generic route-union construction with the utilities graph's full support.
  exact P.embedsEdgeUnion L s utilitiesGraph_support

/-- Helper for Remark 64.2: a complete-five path system gives the required embedded
complete-five realization. -/
private lemma completeGraphFivePathSystem_embedsEdgeUnion
    {X : Type v} [TopologicalSpace X]
    (L : FiniteLinearGraph.{v, v} X) (s : Set L.Edge)
    (P : KuratowskiPathSystem (SimpleGraph.completeGraph (Fin 5))
      (selectedIncidenceGraph L s)) :
    ∃ S : (SimpleGraph.completeGraph (Fin 5)).LinearRealization.{0, v},
      ∃ e : S.Carrier → edgeUnion L s, Topology.IsEmbedding e := by
  -- Apply the generic route-union construction with the complete graph's full support.
  exact P.embedsEdgeUnion L s completeGraphFive_support

/-- Helper for Remark 64.2: a nonplanar finite linear graph has an inclusion-minimal
nonplanar union of realized edges. -/
private lemma existsMinimalNonplanarEdgeUnion {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X)
    (hX : ¬ ∃ f : X → ℝ × ℝ, Topology.IsEmbedding f) :
    ∃ s : Set L.Edge,
      (¬ ∃ f : edgeUnion L s → ℝ × ℝ, Topology.IsEmbedding f) ∧
        ∀ {t : Set L.Edge}, t ⊂ s →
          ∃ f : edgeUnion L t → ℝ × ℝ, Topology.IsEmbedding f := by
  classical
  -- Local instance justification (stored structure field): finiteness of the edge type is
  -- data in `L`, rather than an instance available to finite-set minimality.
  letI : Finite L.Edge := L.edgeFinite
  let nonplanar : Set (Set L.Edge) :=
    {s | ¬ ∃ f : edgeUnion L s → ℝ × ℝ, Topology.IsEmbedding f}
  have hfull : Set.univ ∈ nonplanar := by
    -- A plane embedding of the full edge union would transport to one of `X`.
    intro hplane
    obtain ⟨f, hf⟩ := hplane
    let e : edgeUnion L Set.univ ≃ₜ X :=
      (Homeomorph.setCongr (edgeUnion_univ L)).trans (Homeomorph.Set.univ X)
    have hembedding : Topology.IsEmbedding (f ∘ e.symm) :=
      hf.comp e.symm.isEmbedding
    exact hX ⟨f ∘ e.symm, hembedding⟩
  obtain ⟨s, hs⟩ := nonplanar.toFinite.exists_minimal ⟨Set.univ, hfull⟩
  refine ⟨s, hs.1, ?_⟩
  intro t hts
  -- Minimality rules out nonplanarity for every proper edge subset.
  by_contra ht
  exact hts.not_subset (hs.2 ht hts.subset)

/-- Helper for Remark 64.2: deleting a selected realized edge gives a proper subfamily. -/
private lemma selectedEdgeDeletion_ssubset {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge) (i : {i // i ∈ s}) :
    s \ {i.1} ⊂ s := by
  -- The deleted index belongs to `s`, so singleton deletion is strict.
  exact Set.sdiff_singleton_ssubset.mpr i.2

/-- Helper for Remark 64.2: a cyclic selected incidence graph has a cycle edge whose
corresponding realized edge can be deleted and the remaining union embedded in the plane. -/
private lemma existsCycleEdgeWithPlanarDeletion_of_not_isAcyclic
    {X : Type v} [TopologicalSpace X]
    (L : FiniteLinearGraph.{v, v} X) (s : Set L.Edge)
    (hcyclic : ¬ (selectedIncidenceGraph L s).IsAcyclic)
    (hproper : ∀ {t : Set L.Edge}, t ⊂ s →
      ∃ f : edgeUnion L t → ℝ × ℝ, Topology.IsEmbedding f) :
    ∃ (a : SelectedEndpoint L s)
        (c : (selectedIncidenceGraph L s).Walk a a),
      c.IsCycle ∧
        ∃ e : (selectedIncidenceGraph L s).edgeSet,
          e.1 ∈ c.edges ∧
            ∃ f : edgeUnion L
                (s \ {(selectedIncidenceGraph_edgeEquiv L s e).1}) → ℝ × ℝ,
              Topology.IsEmbedding f := by
  classical
  -- Route correction: extract only the concrete cycle and deleted edge here; the earlier
  -- all-at-once classifier mixed this finite step with the later cycle-bridge analysis.
  have hcycle : ∃ (a : SelectedEndpoint L s)
      (c : (selectedIncidenceGraph L s).Walk a a), c.IsCycle := by
    -- Negating acyclicity supplies a genuine simple cycle.
    by_contra hnone
    apply hcyclic
    intro a c hc
    exact hnone ⟨a, c, hc⟩
  obtain ⟨a, c, hc⟩ := hcycle
  have hedges : c.edges ≠ [] := by
    -- A cycle is nonempty, hence its edge list has a first member.
    intro hempty
    exact hc.not_nil (SimpleGraph.Walk.edges_eq_nil.mp hempty)
  obtain ⟨edge, tail, hedgeList⟩ := List.exists_cons_of_ne_nil hedges
  have hedgeMem : edge ∈ c.edges := by
    rw [hedgeList]
    exact List.mem_cons_self
  let e : (selectedIncidenceGraph L s).edgeSet :=
    ⟨edge, c.edges_subset_edgeSet hedgeMem⟩
  have hdelete :
      s \ {(selectedIncidenceGraph_edgeEquiv L s e).1} ⊂ s :=
    selectedEdgeDeletion_ssubset L s (selectedIncidenceGraph_edgeEquiv L s e)
  obtain ⟨f, hf⟩ := hproper hdelete
  -- Retain the chosen cycle edge together with the embedding supplied by edge criticality.
  exact ⟨a, c, hc, e, hedgeMem, f, hf⟩

/-- Helper for Remark 64.2: if every acyclic selected incidence graph is planar, then an
edge-critical nonplanar union has a concrete cycle edge with planar deletion. -/
private lemma existsCycleEdgeWithPlanarDeletion_of_edgeCriticalNonplanar
    {X : Type v} [TopologicalSpace X]
    (L : FiniteLinearGraph.{v, v} X) (s : Set L.Edge)
    (hnonplanar : ¬ ∃ f : edgeUnion L s → ℝ × ℝ, Topology.IsEmbedding f)
    (hacyclicPlane : (selectedIncidenceGraph L s).IsAcyclic →
      ∃ f : edgeUnion L s → ℝ × ℝ, Topology.IsEmbedding f)
    (hproper : ∀ {t : Set L.Edge}, t ⊂ s →
      ∃ f : edgeUnion L t → ℝ × ℝ, Topology.IsEmbedding f) :
    ∃ (a : SelectedEndpoint L s)
        (c : (selectedIncidenceGraph L s).Walk a a),
      c.IsCycle ∧
        ∃ e : (selectedIncidenceGraph L s).edgeSet,
          e.1 ∈ c.edges ∧
            ∃ f : edgeUnion L
                (s \ {(selectedIncidenceGraph_edgeEquiv L s e).1}) → ℝ × ℝ,
              Topology.IsEmbedding f := by
  -- Nonplanarity rules out the acyclic branch, after which the cycle-edge lemma applies.
  have hcyclic : ¬ (selectedIncidenceGraph L s).IsAcyclic := by
    intro hacyclic
    exact hnonplanar (hacyclicPlane hacyclic)
  exact existsCycleEdgeWithPlanarDeletion_of_not_isAcyclic L s hcyclic hproper

/-- Helper for Remark 64.2: an edge-critical finite linear graph is planar or contains an
embedded utilities-graph or complete-five realization. -/
private lemma edgeCriticalKuratowskiDichotomy {X : Type v} [TopologicalSpace X]
    (L : FiniteLinearGraph.{v, v} X) (s : Set L.Edge)
    (hproper : ∀ {t : Set L.Edge}, t ⊂ s →
      ∃ f : edgeUnion L t → ℝ × ℝ, Topology.IsEmbedding f) :
    (∃ f : edgeUnion L s → ℝ × ℝ, Topology.IsEmbedding f) ∨
      (∃ S : (completeBipartiteGraph (Fin 3) (Fin 3)).LinearRealization.{0, v},
        ∃ e : S.Carrier → edgeUnion L s, Topology.IsEmbedding e) ∨
      ∃ S : (SimpleGraph.completeGraph (Fin 5)).LinearRealization.{0, v},
        ∃ e : S.Carrier → edgeUnion L s, Topology.IsEmbedding e := by
  -- The classifier now returns only finite combinatorial path data; each obstruction branch is
  -- assembled by the verified generic route-union realization.
  rcases edgeCriticalIncidenceGraph_hasKuratowskiPathSystem L s hproper with
    hplane | hpath
  · exact Or.inl hplane
  · rcases hpath with hutilities | hcomplete
    · obtain ⟨P⟩ := hutilities
      exact Or.inr (Or.inl (utilitiesPathSystem_embedsEdgeUnion L s P))
    · obtain ⟨P⟩ := hcomplete
      exact Or.inr (Or.inr (completeGraphFivePathSystem_embedsEdgeUnion L s P))

/-- Helper for Remark 64.2: nonplanarity of a finite linear-graph carrier forces an
embedded utilities-graph or complete-five realization in that carrier. -/
private lemma finiteLinearGraphContainsKuratowskiOfNonplanar
    {X : Type v} [TopologicalSpace X] (L : FiniteLinearGraph.{v, v} X)
    (hX : ¬ ∃ f : X → ℝ × ℝ, Topology.IsEmbedding f) :
    (∃ S : (completeBipartiteGraph (Fin 3) (Fin 3)).LinearRealization.{0, v},
      ∃ e : S.Carrier → X, Topology.IsEmbedding e) ∨
      ∃ S : (SimpleGraph.completeGraph (Fin 5)).LinearRealization.{0, v},
        ∃ e : S.Carrier → X, Topology.IsEmbedding e := by
  obtain ⟨s, hs, hproper⟩ := existsMinimalNonplanarEdgeUnion L hX
  -- The planar branch contradicts the choice of `s`; either obstruction branch composes with
  -- the subtype inclusion into the original carrier.
  rcases edgeCriticalKuratowskiDichotomy L s hproper with hplane | hutilities | hcomplete
  · exact (hs hplane).elim
  · obtain ⟨S, e, he⟩ := hutilities
    have hambient : Topology.IsEmbedding (Subtype.val ∘ e) :=
      Topology.IsEmbedding.subtypeVal.comp he
    exact Or.inl ⟨S, Subtype.val ∘ e, hambient⟩
  · obtain ⟨S, e, he⟩ := hcomplete
    have hambient : Topology.IsEmbedding (Subtype.val ∘ e) :=
      Topology.IsEmbedding.subtypeVal.comp he
    exact Or.inr ⟨S, Subtype.val ∘ e, hambient⟩

/-- Remark 64.2 (2). Kuratowski's theorem: if a graph realization does not embed in
the plane, then it contains an embedded realization of the utilities graph or the
complete graph on five vertices. -/
theorem containsKuratowskiObstruction_of_not_isPlaneEmbeddable
    (R : G.LinearRealization.{u, v}) (h_nonplanar : ¬ R.IsPlaneEmbeddable) :
    R.ContainsKuratowskiObstruction := by
  -- Apply the carrier-level finite-linear-graph theorem and expose the obstruction predicate.
  rw [containsKuratowskiObstruction_iff]
  exact finiteLinearGraphContainsKuratowskiOfNonplanar R.linearGraph h_nonplanar

/-- Remark 64.2. A topological linear-graph realization embeds in the plane exactly when
it contains no embedded realization of the utilities graph or the complete graph on five
vertices. -/
theorem isPlaneEmbeddable_iff_not_containsKuratowskiObstruction
    (R : G.LinearRealization.{u, v}) :
    R.IsPlaneEmbeddable ↔ ¬ R.ContainsKuratowskiObstruction := by
  constructor
  · intro h_plane h_forbidden
    exact forbiddenGraphEmbedding_obstructsPlaneEmbedding R h_forbidden h_plane
  · intro h_forbidden
    by_contra h_nonplanar
    exact h_forbidden (containsKuratowskiObstruction_of_not_isPlaneEmbeddable R h_nonplanar)

end SimpleGraph.LinearRealization
