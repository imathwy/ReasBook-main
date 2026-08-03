module

public import Topology_Munkres_2000.Book.Example_50_6
public import Mathlib.Combinatorics.SimpleGraph.Paths

public section

universe u v

namespace SimpleGraph.LinearRealization

/-- Helper for Remark 64.2: `edgeUnion L s` is the union of the realized edges indexed by
`s`. -/
def edgeUnion {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge) : Set X :=
  ⋃ i ∈ s, L.edgeSet i

/-- Helper for Remark 64.2: membership in an edge union is witnessed by one selected edge. -/
lemma mem_edgeUnion_iff {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge) (x : X) :
    x ∈ edgeUnion L s ↔ ∃ i ∈ s, x ∈ L.edgeSet i := by
  -- Expose the two indexed unions once at their owning definition.
  simp only [edgeUnion, Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi, hx⟩
    exact ⟨i, hi, hx⟩
  · rintro ⟨i, hi, hx⟩
    exact ⟨i, hi, hx⟩

/-- Helper for Remark 64.2: the union of all realized edges is the whole carrier. -/
lemma edgeUnion_univ {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) : edgeUnion L Set.univ = Set.univ := by
  -- The membership condition is vacuous, leaving the stored edge cover.
  simp only [edgeUnion, Set.mem_univ, Set.iUnion_true, L.iUnion_edgeSet]

/-- Helper for Remark 64.2: the endpoints of a selected family of realized edges. -/
def selectedEndpointSet {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge) : Set X :=
  {x | ∃ i ∈ s, x = L.edge i 0 ∨ x = L.edge i 1}

/-- Helper for Remark 64.2: a selected endpoint is an endpoint of a selected edge. -/
lemma mem_selectedEndpointSet_iff {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge) (x : X) :
    x ∈ selectedEndpointSet L s ↔
      ∃ i ∈ s, x = L.edge i 0 ∨ x = L.edge i 1 := by
  -- This records the defining membership predicate for cross-module use.
  rfl

/-- Helper for Remark 64.2: the vertex type carried by the selected realized endpoints. -/
abbrev SelectedEndpoint {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge) :=
  selectedEndpointSet L s

/-- Helper for Remark 64.2: the initial endpoint of a selected edge belongs to the selected
endpoint set. -/
lemma selectedEdgeZero_mem {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge) (i : {i // i ∈ s}) :
    L.edge i.1 0 ∈ selectedEndpointSet L s := by
  -- The edge index and the left disjunct witness membership.
  exact ⟨i.1, i.2, Or.inl rfl⟩

/-- Helper for Remark 64.2: the terminal endpoint of a selected edge belongs to the selected
endpoint set. -/
lemma selectedEdgeOne_mem {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge) (i : {i // i ∈ s}) :
    L.edge i.1 1 ∈ selectedEndpointSet L s := by
  -- The edge index and the right disjunct witness membership.
  exact ⟨i.1, i.2, Or.inr rfl⟩

/-- Helper for Remark 64.2: the selected-endpoint vertex at parameter `0`. -/
def selectedEdgeZero {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge) (i : {i // i ∈ s}) :
    SelectedEndpoint L s :=
  ⟨L.edge i.1 0, selectedEdgeZero_mem L s i⟩

/-- Helper for Remark 64.2: the selected-endpoint vertex at parameter `1`. -/
def selectedEdgeOne {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge) (i : {i // i ∈ s}) :
    SelectedEndpoint L s :=
  ⟨L.edge i.1 1, selectedEdgeOne_mem L s i⟩

/-- Helper for Remark 64.2: the unordered endpoint pair of a selected realized edge. -/
def selectedEdgeEndpointPair {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge) (i : {i // i ∈ s}) :
    Sym2 (SelectedEndpoint L s) :=
  s(selectedEdgeZero L s i, selectedEdgeOne L s i)

/-- Helper for Remark 64.2: mapping a selected endpoint pair to the ambient carrier recovers
the stored edge endpoints. -/
lemma selectedEdgeEndpointPair_map_coe {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge) (i : {i // i ∈ s}) :
    Sym2.map (fun x : SelectedEndpoint L s ↦ (x : X)) (selectedEdgeEndpointPair L s i) =
      s(L.edge i.1 0, L.edge i.1 1) := by
  -- Unfold the endpoint constructors at their owner and compute the `Sym2` map.
  rfl

/-- Helper for Remark 64.2: the endpoints of a realized edge are distinct. -/
lemma edge_endpoint_ne {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (i : L.Edge) :
    L.edge i 0 ≠ L.edge i 1 := by
  -- Injectivity of the stored edge parameterization separates `0` and `1`.
  intro h
  exact zero_ne_one ((L.edgeEmbedding i).injective h)

/-- Helper for Remark 64.2: a realized edge is determined by its unordered pair of
endpoints. -/
lemma edge_eq_of_endpointPair_eq {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) {i j : L.Edge}
    (h : s(L.edge i 0, L.edge i 1) = s(L.edge j 0, L.edge j 1)) : i = j := by
  -- If the indices differed, both distinct endpoints of `i` would lie in the same
  -- subsingleton intersection.
  by_contra hij
  have hi0 : L.edge i 0 ∈ L.edgeSet i := by
    rw [L.edgeSet_def]
    exact Set.mem_range_self 0
  have hi1 : L.edge i 1 ∈ L.edgeSet i := by
    rw [L.edgeSet_def]
    exact Set.mem_range_self 1
  rcases Sym2.eq_iff.mp h with ⟨h00, h11⟩ | ⟨h01, h10⟩
  · have hj0 : L.edge i 0 ∈ L.edgeSet j := by
      rw [L.edgeSet_def]
      exact ⟨0, h00.symm⟩
    have hj1 : L.edge i 1 ∈ L.edgeSet j := by
      rw [L.edgeSet_def]
      exact ⟨1, h11.symm⟩
    exact edge_endpoint_ne L i (L.inter_subsingleton hij ⟨hi0, hj0⟩ ⟨hi1, hj1⟩)
  · have hj1 : L.edge i 0 ∈ L.edgeSet j := by
      rw [L.edgeSet_def]
      exact ⟨1, h01.symm⟩
    have hj0 : L.edge i 1 ∈ L.edgeSet j := by
      rw [L.edgeSet_def]
      exact ⟨0, h10.symm⟩
    exact edge_endpoint_ne L i (L.inter_subsingleton hij ⟨hi0, hj1⟩ ⟨hi1, hj0⟩)

/-- Helper for Remark 64.2: the finite endpoint-incidence graph of a selected family of
realized edges. -/
def selectedIncidenceGraph {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge) :
    SimpleGraph (SelectedEndpoint L s) :=
  SimpleGraph.fromEdgeSet (Set.range (selectedEdgeEndpointPair L s))

/-- Helper for Remark 64.2: the endpoint pair of a selected edge is not diagonal. -/
lemma selectedEdgeEndpointPair_not_isDiag {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge) (i : {i // i ∈ s}) :
    ¬ (selectedEdgeEndpointPair L s i).IsDiag := by
  -- Diagonality would identify the two subtype endpoints and hence their values in `X`.
  rw [selectedEdgeEndpointPair, Sym2.mk_isDiag_iff]
  intro h
  exact edge_endpoint_ne L i.1 (congrArg Subtype.val h)

/-- Helper for Remark 64.2: the incidence-graph edge set is exactly the range of selected
endpoint pairs. -/
lemma selectedIncidenceGraph_edgeSet {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge) :
    (selectedIncidenceGraph L s).edgeSet = Set.range (selectedEdgeEndpointPair L s) := by
  -- `fromEdgeSet` removes only diagonal pairs, and selected edges have distinct endpoints.
  rw [selectedIncidenceGraph, SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  constructor
  · exact fun he ↦ he.1
  · intro he
    refine ⟨he, ?_⟩
    obtain ⟨i, rfl⟩ := he
    exact selectedEdgeEndpointPair_not_isDiag L s i

/-- Helper for Remark 64.2: distinct selected edges have distinct incidence-graph endpoint
pairs. -/
lemma selectedEdgeEndpointPair_injective {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge) :
    Function.Injective (selectedEdgeEndpointPair L s) := by
  -- Map a pair equality back to ambient endpoints, then use uniqueness of realized edges.
  intro i j h
  apply Subtype.ext
  apply edge_eq_of_endpointPair_eq L
  have hm := congrArg (Sym2.map (fun x : SelectedEndpoint L s ↦ (x : X))) h
  simpa only [selectedEdgeEndpointPair, Sym2.map_mk, selectedEdgeZero, selectedEdgeOne] using hm

/-- Helper for Remark 64.2: every selected endpoint pair is an edge of the endpoint-incidence
graph. -/
lemma selectedEdgeEndpointPair_mem {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge) (i : {i // i ∈ s}) :
    selectedEdgeEndpointPair L s i ∈ (selectedIncidenceGraph L s).edgeSet := by
  -- The incidence edge-set description puts each endpoint pair in the graph by construction.
  rw [selectedIncidenceGraph_edgeSet]
  exact Set.mem_range_self i

/-- Helper for Remark 64.2: a selected realized edge determines its edge in the
endpoint-incidence graph. -/
def selectedEdgeToIncidenceEdge {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge) :
    {i // i ∈ s} → (selectedIncidenceGraph L s).edgeSet :=
  fun i ↦ ⟨selectedEdgeEndpointPair L s i, selectedEdgeEndpointPair_mem L s i⟩

/-- Helper for Remark 64.2: selected realized edges are in bijection with the edges of their
endpoint-incidence graph. -/
lemma selectedEdgeToIncidenceEdge_bijective {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge) :
    Function.Bijective (selectedEdgeToIncidenceEdge L s) := by
  constructor
  · -- Injectivity is precisely uniqueness of a realized edge from its endpoint pair.
    intro i j h
    apply selectedEdgeEndpointPair_injective L s
    exact congrArg Subtype.val h
  · -- Every incidence edge has a selected endpoint-pair witness.
    intro e
    have he : e.1 ∈ Set.range (selectedEdgeEndpointPair L s) := by
      rw [← selectedIncidenceGraph_edgeSet]
      exact e.2
    obtain ⟨i, hi⟩ := he
    refine ⟨i, ?_⟩
    apply Subtype.ext
    simpa only [selectedEdgeToIncidenceEdge] using hi

/-- Helper for Remark 64.2: the canonical equivalence sends each incidence edge back to the
unique selected realized edge with that unordered endpoint pair. -/
noncomputable def selectedIncidenceGraph_edgeEquiv {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge) :
    (selectedIncidenceGraph L s).edgeSet ≃ {i // i ∈ s} :=
  (Equiv.ofBijective (selectedEdgeToIncidenceEdge L s)
    (selectedEdgeToIncidenceEdge_bijective L s)).symm

/-- Helper for Remark 64.2: applying the incidence-edge equivalence recovers the original
unordered endpoint pair. -/
lemma selectedIncidenceGraph_edgeEquiv_endpointPair {X : Type u}
    [TopologicalSpace X] (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge)
    (e : (selectedIncidenceGraph L s).edgeSet) :
    selectedEdgeEndpointPair L s (selectedIncidenceGraph_edgeEquiv L s e) = e.1 := by
  -- The inverse law for the selected-edge map gives equality in the incidence edge subtype.
  have h := (selectedIncidenceGraph_edgeEquiv L s).symm_apply_apply e
  exact congrArg Subtype.val h

/-- Helper for Remark 64.2: an internally disjoint path model of a simple graph `K` inside
a simple graph `H`. -/
structure KuratowskiPathSystem {A : Type u} {B : Type v}
    (K : SimpleGraph A) (H : SimpleGraph B) where
  branch : A → B
  branch_injective : Function.Injective branch
  route : ∀ e : K.edgeSet, H.Walk (branch e.1.out.1) (branch e.1.out.2)
  route_isPath : ∀ e, (route e).IsPath
  branch_mem_route_support_iff : ∀ e x, branch x ∈ (route e).support ↔ x ∈ e.1
  route_intersection : ∀ {e f : K.edgeSet}, e ≠ f → ∀ {x : B},
    x ∈ (route e).support → x ∈ (route f).support →
      ∃ a, a ∈ e.1 ∧ a ∈ f.1 ∧ branch a = x

/-- Helper for Remark 64.2: the two branch vertices belonging to an edge in a Kuratowski path
system are distinct. -/
lemma KuratowskiPathSystem.branch_out_ne {A : Type u} {B : Type v}
    {K : SimpleGraph A} {H : SimpleGraph B} (P : KuratowskiPathSystem K H)
    (e : K.edgeSet) : P.branch e.1.out.1 ≠ P.branch e.1.out.2 := by
  -- A graph edge is not diagonal, and the branch map is injective.
  apply P.branch_injective.ne
  intro hout
  apply K.not_isDiag_of_mem_edgeSet e.2
  rw [← e.1.out_eq, Sym2.mk_isDiag_iff]
  exact hout

/-- Helper for Remark 64.2: every route in a Kuratowski path system is nonempty. -/
lemma KuratowskiPathSystem.route_not_nil {A : Type u} {B : Type v}
    {K : SimpleGraph A} {H : SimpleGraph B} (P : KuratowskiPathSystem K H)
    (e : K.edgeSet) : ¬ (P.route e).Nil := by
  -- A nil walk would have equal endpoints, contrary to branch-vertex distinctness.
  exact SimpleGraph.Walk.not_nil_of_ne (P.branch_out_ne e)

/-- Helper for Remark 64.2: the first branch endpoint lies on its path-system route. -/
lemma KuratowskiPathSystem.branch_out_fst_mem_route {A : Type u} {B : Type v}
    {K : SimpleGraph A} {H : SimpleGraph B} (P : KuratowskiPathSystem K H)
    (e : K.edgeSet) : P.branch e.1.out.1 ∈ (P.route e).support := by
  -- The route's exact branch-incidence field applies to the first member of the edge.
  exact (P.branch_mem_route_support_iff e e.1.out.1).2 (Sym2.out_fst_mem e.1)

/-- Helper for Remark 64.2: the second branch endpoint lies on its path-system route. -/
lemma KuratowskiPathSystem.branch_out_snd_mem_route {A : Type u} {B : Type v}
    {K : SimpleGraph A} {H : SimpleGraph B} (P : KuratowskiPathSystem K H)
    (e : K.edgeSet) : P.branch e.1.out.2 ∈ (P.route e).support := by
  -- The route's exact branch-incidence field applies to the second member of the edge.
  exact (P.branch_mem_route_support_iff e e.1.out.2).2 (Sym2.out_snd_mem e.1)

/-- Helper for Remark 64.2: choose one of a selected edge's endpoints using a Boolean. -/
def selectedEndpointOfBool {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge) :
    {i // i ∈ s} × Bool → SelectedEndpoint L s :=
  fun p ↦ if p.2 then selectedEdgeOne L s p.1 else selectedEdgeZero L s p.1

/-- Helper for Remark 64.2: every selected endpoint is obtained from a selected edge and one
of its two Boolean endpoint choices. -/
lemma selectedEndpointOfBool_surjective {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge) :
    Function.Surjective (selectedEndpointOfBool L s) := by
  intro a
  obtain ⟨i, hi, ha | ha⟩ := a.2
  · refine ⟨(⟨i, hi⟩, false), ?_⟩
    apply Subtype.ext
    exact ha.symm
  · refine ⟨(⟨i, hi⟩, true), ?_⟩
    apply Subtype.ext
    exact ha.symm

/-- Helper for Remark 64.2: the selected realized-edge subtype is finite. -/
lemma selectedEdge_finite {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge) : Finite {i // i ∈ s} := by
  -- Local instance justification (stored presentation data): finiteness is carried by `L`
  -- as a field rather than registered globally for its edge type.
  letI : Finite L.Edge := L.edgeFinite
  infer_instance

/-- Helper for Remark 64.2: the selected endpoint type is finite. -/
lemma selectedEndpoint_finite {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge) : Finite (SelectedEndpoint L s) := by
  -- Local instance justification (theorem-local selected family): its finite edge subtype is
  -- supplied by the preceding presentation-specific lemma.
  letI : Finite {i // i ∈ s} := selectedEdge_finite L s
  exact Finite.of_surjective (selectedEndpointOfBool L s)
    (selectedEndpointOfBool_surjective L s)

/-- Helper for Remark 64.2: the edge type of the selected endpoint-incidence graph is finite. -/
lemma selectedIncidenceGraph_edgeFinite {X : Type u} [TopologicalSpace X]
    (L : FiniteLinearGraph.{u, v} X) (s : Set L.Edge) :
    Finite (selectedIncidenceGraph L s).edgeSet := by
  -- Local instance justification (theorem-local selected family): transport finiteness across
  -- the canonical selected-edge equivalence.
  letI : Finite {i // i ∈ s} := selectedEdge_finite L s
  exact Finite.of_injective (selectedIncidenceGraph_edgeEquiv L s)
    (selectedIncidenceGraph_edgeEquiv L s).injective

end SimpleGraph.LinearRealization
