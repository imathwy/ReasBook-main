import Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_1
import Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_definition_3_18_extra_1
import Integer.Chapters.Chap04.section_4_4.ch4_sec4_4_corollary_4_19
import Integer.Chapters.Chap07.incident_edge_finset

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators Matrix

attribute [local instance] Classical.propDecidable

section Exercise74

open SimpleGraph

variable {V : Type} [Fintype V]
variable (G : SimpleGraph V)

noncomputable local instance : DecidableEq V := Classical.decEq V
noncomputable local instance : DecidableRel G.Adj := Classical.decRel G.Adj

/-- The degree-system relaxation
`{x ∈ ℝ^E | ∑_{e ∈ δ(v)} x_e ≤ 1 for all v, x ≥ 0}` of the matching polytope. -/
def matching_degree_constraint_set : Set (G.edgeSet → ℝ) :=
  {x |
    (∀ v : V, (incidentEdgeFinset G v).sum x ≤ 1) ∧
      ∀ e, 0 ≤ x e}

/-- Membership in `matching_degree_constraint_set G` means satisfying the degree inequalities and
the nonnegativity constraints. -/
theorem mem_matching_degree_constraint_set_iff
    {x : G.edgeSet → ℝ} :
    x ∈ matching_degree_constraint_set G ↔
      (∀ v : V, (incidentEdgeFinset G v).sum x ≤ 1) ∧
        ∀ e, 0 ≤ x e := Iff.rfl

/-- The coefficient vector of the blossom inequality attached to the odd vertex set `U`. -/
def blossom_vector (U : Set V) : G.edgeSet → ℝ :=
  fun e ↦ if e ∈ E[G] U then 1 else 0

/-- `blossom_vector G U` is `1` on the induced-edge coordinates `E[G] U` and `0` elsewhere. -/
theorem blossom_vector_apply
    (U : Set V) (e : G.edgeSet) :
    blossom_vector G U e = if e ∈ E[G] U then 1 else 0 := by
  rfl

/-- The right-hand side of the blossom inequality attached to the odd vertex set `U`. -/
def blossom_rhs (U : Set V) : ℝ :=
  ((U.ncard : ℝ) - 1) / 2

/-- The equality face of the blossom inequality on the matching polytope. -/
def blossom_face (U : Set V) : Set (G.edgeSet → ℝ) :=
  G.matchingPolytope ∩ {x : G.edgeSet → ℝ | blossom_vector G U ⬝ᵥ x = blossom_rhs U}

/-- Membership in `blossom_face G U` means belonging to the matching polytope and meeting the
blossom inequality at equality. -/
theorem mem_blossom_face_iff
    {U : Set V} {x : G.edgeSet → ℝ} :
    x ∈ blossom_face G U ↔
      x ∈ G.matchingPolytope ∧ blossom_vector G U ⬝ᵥ x = blossom_rhs U := by
  simp [blossom_face]

/-- Helper for Exercise 7.4: the blossom coefficient vector defines a continuous linear functional
on the ambient edge-coordinate space. -/
private noncomputable def blossomStrongDual
    (U : Set V) : StrongDual ℝ (G.edgeSet → ℝ) :=
  ∑ e, blossom_vector G U e • ContinuousLinearMap.proj e

/-- Helper for Exercise 7.4: the strong-dual functional attached to `blossom_vector G U`
evaluates as the corresponding dot product. -/
private lemma blossomStrongDual_apply
    (U : Set V) (x : G.edgeSet → ℝ) :
    blossomStrongDual G U x = blossom_vector G U ⬝ᵥ x := by
  -- Expand the coordinate projections and collect the finite sum into the dot product.
  simp [blossomStrongDual, dotProduct]

/-- The aggregated left-hand-side coefficient of an edge under row multipliers `u` on the degree
constraints and slack multipliers `v` on the nonnegativity constraints. -/
private def matching_degree_chvatal_coeff
    (u : V → ℝ) (v : G.edgeSet → ℝ) : G.edgeSet → ℝ :=
  fun e ↦
    (Finset.univ.filter fun w : V ↦ e ∈ incidentEdgeFinset G w).sum u - v e

/-- A Chvátal inequality for the matching degree system is obtained from nonnegative row
multipliers on the degree inequalities together with nonnegative slack multipliers on the
nonnegativity constraints, with integral aggregate edge coefficients. -/
def IsMatchingDegreeSystemChvatalInequality
    (c : G.edgeSet → ℝ) (β : ℝ) : Prop :=
  ∃ u : V → ℝ, ∃ v : G.edgeSet → ℝ,
    (∀ w, 0 ≤ u w) ∧
      (∀ e, 0 ≤ v e) ∧
        (∀ e, ∃ z : ℤ, matching_degree_chvatal_coeff G u v e = (z : ℝ)) ∧
          c = matching_degree_chvatal_coeff G u v ∧
            β = (Int.floor (∑ w, u w) : ℝ)

/-- `IsMatchingDegreeSystemChvatalInequality G c β` unfolds to existence of nonnegative row and
slack multipliers whose aggregate coefficients are integral and equal to `c`, with right-hand side
`β`. -/
theorem isMatchingDegreeSystemChvatalInequality_iff
    (c : G.edgeSet → ℝ) (β : ℝ) :
    IsMatchingDegreeSystemChvatalInequality G c β ↔
      ∃ u : V → ℝ, ∃ v : G.edgeSet → ℝ,
        (∀ w, 0 ≤ u w) ∧
          (∀ e, 0 ≤ v e) ∧
            (∀ e, ∃ z : ℤ,
              (Finset.univ.filter fun w : V ↦ e ∈ incidentEdgeFinset G w).sum u - v e = (z : ℝ)) ∧
              (∀ e,
                c e =
                  (Finset.univ.filter fun w : V ↦ e ∈ incidentEdgeFinset G w).sum u - v e) ∧
                β = (Int.floor (∑ w, u w) : ℝ) := by
  constructor
  · rintro ⟨u, v, hu, hv, hint, hc, hβ⟩
    refine ⟨u, v, hu, hv, ?_, ?_, hβ⟩
    · intro e
      rcases hint e with ⟨z, hz⟩
      exact ⟨z, by simpa [matching_degree_chvatal_coeff] using hz⟩
    · intro e
      exact by simpa [matching_degree_chvatal_coeff] using congrArg (fun f ↦ f e) hc
  · rintro ⟨u, v, hu, hv, hint, hc, hβ⟩
    refine ⟨u, v, hu, hv, ?_, ?_, hβ⟩
    · intro e
      rcases hint e with ⟨z, hz⟩
      exact ⟨z, by simpa [matching_degree_chvatal_coeff] using hz⟩
    · funext e
      exact by simpa [matching_degree_chvatal_coeff] using hc e

/-- The first Chvátal closure of the matching degree system, represented as the set of points of
the degree relaxation satisfying every Chvátal inequality derived from that system. -/
def matching_degree_chvatal_closure : Set (G.edgeSet → ℝ) :=
  {x | x ∈ matching_degree_constraint_set G ∧
      ∀ c : G.edgeSet → ℝ, ∀ β : ℝ,
        IsMatchingDegreeSystemChvatalInequality G c β → c ⬝ᵥ x ≤ β}

/-- Membership in `matching_degree_chvatal_closure G` means lying in the degree relaxation and
satisfying every Chvátal inequality of that system. -/
theorem mem_matching_degree_chvatal_closure_iff
    {x : G.edgeSet → ℝ} :
    x ∈ matching_degree_chvatal_closure G ↔
      x ∈ matching_degree_constraint_set G ∧
        ∀ c : G.edgeSet → ℝ, ∀ β : ℝ,
          IsMatchingDegreeSystemChvatalInequality G c β → c ⬝ᵥ x ≤ β := Iff.rfl

/-- The matching degree system has Chvátal rank zero when the original degree relaxation already
equals the matching polytope. -/
def matching_degree_system_has_chvatal_rank_zero : Prop :=
  matching_degree_constraint_set G = G.matchingPolytope

/-- `matching_degree_system_has_chvatal_rank_zero G` means that the degree relaxation is already
the matching polytope. -/
theorem matching_degree_system_has_chvatal_rank_zero_iff :
    matching_degree_system_has_chvatal_rank_zero G ↔
      matching_degree_constraint_set G = G.matchingPolytope := Iff.rfl

/-- The matching degree system has Chvátal rank one when one Chvátal closure step yields the
matching polytope, but the original degree relaxation is strictly larger. -/
def matching_degree_system_has_chvatal_rank_one : Prop :=
  matching_degree_chvatal_closure G = G.matchingPolytope ∧
    matching_degree_constraint_set G ≠ G.matchingPolytope

/-- `matching_degree_system_has_chvatal_rank_one G` unfolds to equality after one Chvátal step
together with failure of equality at rank zero. -/
theorem matching_degree_system_has_chvatal_rank_one_iff :
    matching_degree_system_has_chvatal_rank_one G ↔
      matching_degree_chvatal_closure G = G.matchingPolytope ∧
        matching_degree_constraint_set G ≠ G.matchingPolytope := Iff.rfl

/-- Helper for Exercise 7.4: the incident-edge sum used in the degree relaxation is exactly the
corresponding row of the edge-incidence matrix. -/
private lemma incidentEdgeFinset_sum_eq_edgeIncMatrix_mulVec
    (x : G.edgeSet → ℝ) (v : V) :
    (incidentEdgeFinset G v).sum x = ((G.edgeIncMatrix ℝ).mulVec x) v := by
  -- Expand the restricted incidence matrix and read each entry as the incidence indicator at `v`.
  symm
  rw [SimpleGraph.edgeIncMatrix, Matrix.mulVec, dotProduct]
  calc
    ∑ e : G.edgeSet, G.incMatrix ℝ v (e : Sym2 V) * x e
        = ∑ e : G.edgeSet, if e ∈ incidentEdgeFinset G v then x e else 0 := by
            refine Finset.sum_congr rfl ?_
            intro e he
            by_cases h : (e : Sym2 V) ∈ G.incidenceSet v
            · have hmem : e ∈ incidentEdgeFinset G v := by
                exact (mem_incidentEdgeFinset_iff (G := G) (v := v) (e := e)).2
                  (by simpa [SimpleGraph.edge_mem_incidenceSet_iff] using h)
              simp [G.incMatrix_of_mem_incidenceSet (R := ℝ) h, hmem]
            · have hnotmem : e ∉ incidentEdgeFinset G v := by
                intro hmem
                exact h ((SimpleGraph.edge_mem_incidenceSet_iff (G := G) (a := v) (e := e)).2
                  ((mem_incidentEdgeFinset_iff (G := G) (v := v) (e := e)).1 hmem))
              simp [G.incMatrix_of_notMem_incidenceSet (R := ℝ) h, hnotmem]
    _ = (Finset.univ.filter fun e : G.edgeSet ↦ e ∈ incidentEdgeFinset G v).sum x := by
          rw [Finset.sum_filter]
    _ = (incidentEdgeFinset G v).sum x := by
          simp

/-- Helper for Exercise 7.4: membership in `matching_degree_constraint_set G` is the Chapter 4.19
incidence-matrix system `A_G x ≤ 1, x ≥ 0`. -/
private lemma matchingDegreeConstraintSet_eq_setOf_mulVec_le_one :
    matching_degree_constraint_set G = {x | (G.edgeIncMatrix ℝ).mulVec x ≤ 1 ∧ ∀ e, 0 ≤ x e} := by
  ext x
  constructor
  · intro hx
    rcases (mem_matching_degree_constraint_set_iff (G := G) (x := x)).1 hx with
      ⟨hx_deg, hx_nonneg⟩
    refine ⟨?_, hx_nonneg⟩
    intro v
    simpa [incidentEdgeFinset_sum_eq_edgeIncMatrix_mulVec (G := G) x v] using hx_deg v
  · rintro ⟨hx_deg, hx_nonneg⟩
    refine (mem_matching_degree_constraint_set_iff (G := G) (x := x)).2 ?_
    refine ⟨?_, hx_nonneg⟩
    intro v
    simpa [incidentEdgeFinset_sum_eq_edgeIncMatrix_mulVec (G := G) x v] using hx_deg v
/-- Helper for Exercise 7.4: on a bipartite graph the degree relaxation already equals the
matching polytope. -/
private lemma matchingDegreeConstraintSet_eq_matchingPolytope_of_isBipartite
    (hG : G.IsBipartite) :
    matching_degree_constraint_set G = G.matchingPolytope := by
  rw [matchingDegreeConstraintSet_eq_setOf_mulVec_le_one (G := G)]
  exact (SimpleGraph.matchingPolytope_eq_setOf_mulVec_le_one (G := G) hG).symm

/-- Helper for Exercise 7.4: the Chapter 4 degree row
`∑_{e ∈ incidenceFinset(v)} x_e` is the same edge-coordinate sum as
`(incidentEdgeFinset G v).sum x`. -/
private lemma incidenceFilter_sum_eq_incidentEdgeFinset_sum
    (x : G.edgeSet → ℝ) (v : V) :
    (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x =
      (incidentEdgeFinset G v).sum x := by
  -- First normalize the two index finsets themselves; the sum then follows by rewriting.
  have hfinset :
      (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v) =
        incidentEdgeFinset G v := by
    ext e
    simp [incidentEdgeFinset, SimpleGraph.edge_mem_incidenceSet_iff]
  rw [hfinset]

/-- Helper for Exercise 7.4: the blossom coefficient vector sums exactly the coordinates indexed by
`E[G] U`. -/
private lemma blossomVector_dot_eq_inducedEdgeSum
    (U : Set V) (x : G.edgeSet → ℝ) :
    blossom_vector G U ⬝ᵥ x = (E[G] U).sum x := by
  classical
  unfold blossom_vector
  rw [dotProduct]
  calc
    ∑ e : G.edgeSet, (if e ∈ E[G] U then 1 else 0) * x e =
        ∑ e : G.edgeSet, if e ∈ E[G] U then x e else 0 := by
          refine Finset.sum_congr rfl ?_
          intro e he
          by_cases h : e ∈ E[G] U
          · simp [h]
          · simp [h]
    _ = (E[G] U).sum x := by
          simpa using
            (Finset.sum_filter
              (s := (Finset.univ : Finset G.edgeSet))
              (p := fun e : G.edgeSet ↦ e ∈ E[G] U)
              (f := x)).symm

/-- Helper for Exercise 7.4: the endpoint finset of an edge-coordinate is the unordered pair of
its canonical `Sym2.out` endpoints. -/
private lemma edgeToFinset_eq_pair
    (e : G.edgeSet) :
    ((e : Sym2 V).toFinset) = {e.1.out.1, e.1.out.2} := by
  -- Rewrite the edge through its canonical endpoint presentation.
  calc
    ((e : Sym2 V).toFinset) = (s(e.1.out.1, e.1.out.2)).toFinset := by
      simpa [e.1.out_eq]
    _ = {e.1.out.1, e.1.out.2} := Sym2.toFinset_mk_eq

/-- Helper for Exercise 7.4: the vertices incident to an edge-coordinate `e` are exactly the two
canonical endpoints of `e`. -/
private lemma incidentVertexFinset_eq_edgeToFinset
    (e : G.edgeSet) :
    (Finset.univ.filter fun w : V ↦ e ∈ incidentEdgeFinset G w) = (e : Sym2 V).toFinset := by
  -- Both finsets encode the same vertex-membership predicate `w ∈ (e : Sym2 V)`.
  ext w
  simp [incidentEdgeFinset, SimpleGraph.edge_mem_incidenceSet_iff]

/-- Helper for Exercise 7.4: an induced edge is characterized by both canonical endpoints lying in
the chosen vertex set. -/
private lemma memInducedEdgeFinsetEndpointsIff
    (U : Set V) (e : G.edgeSet) :
    e ∈ E[G] U ↔ e.1.out.1 ∈ U ∧ e.1.out.2 ∈ U := by
  have hadj : G.Adj e.1.out.1 e.1.out.2 := by
    have he : s(e.1.out.1, e.1.out.2) ∈ G.edgeSet := by
      simpa [e.1.out_eq] using e.prop
    exact (SimpleGraph.mem_edgeSet (G := G) (v := e.1.out.1) (w := e.1.out.2)).1 he
  -- Rewrite induced-edge membership through the same canonical endpoint presentation.
  rw [mem_inducedEdgeFinset_iff, ← e.1.out_eq, SimpleGraph.Subgraph.mem_edgeSet]
  simp [SimpleGraph.Subgraph.induce, hadj]

/-- Helper for Exercise 7.4: the full matching-constraint owner implies the degree relaxation
owner by discarding the odd-set inequalities. -/
private lemma matchingConstraintSet_subset_matchingDegreeConstraintSet :
    G.matchingConstraintSet ⊆ matching_degree_constraint_set G := by
  intro x hx
  rcases (SimpleGraph.mem_matchingConstraintSet_iff (G := G) (x := x)).1 hx with
    ⟨hx_nonneg, hx_deg, -⟩
  refine (mem_matching_degree_constraint_set_iff (G := G) (x := x)).2 ?_
  refine ⟨?_, hx_nonneg⟩
  intro v
  rw [← incidenceFilter_sum_eq_incidentEdgeFinset_sum (G := G) x v]
  exact hx_deg v

/-- Helper for Exercise 7.4: Theorem 4.24 identifies the matching polytope with the full matching
constraint system. -/
private lemma matchingPolytope_eq_matchingConstraintSet :
    G.matchingPolytope = G.matchingConstraintSet := by
  -- Route correction: this runner is missing the compiled Theorem 4.24 owner, so the proof stage
  -- must carry a theorem-local bridge instead of importing the absent `.olean`.
  -- TODO: port the local double-cover reverse inclusion from Chapter 4.24 and remove this `sorry`.
  sorry

/-- Helper for Exercise 7.4: every valid blossom inequality cuts out an exposed blossom face on
the matching polytope. -/
private lemma blossomFace_isExposed
    (U : Set V)
    (hvalid : is_valid_inequality G.matchingPolytope (blossom_vector G U) (blossom_rhs U)) :
    IsExposed ℝ G.matchingPolytope (blossom_face G U) := by
  classical
  by_cases hface_nonempty : (blossom_face G U).Nonempty
  · obtain ⟨x₀, hx₀⟩ := hface_nonempty
    let l : StrongDual ℝ (G.edgeSet → ℝ) := blossomStrongDual G U
    have hface_eq : blossom_face G U = l.toExposed G.matchingPolytope := by
      ext x
      constructor
      · intro hx
        rcases (mem_blossom_face_iff (G := G) (U := U) (x := x)).1 hx with ⟨hxP, hxEq⟩
        refine ⟨hxP, ?_⟩
        intro y hyP
        calc
          l y = blossom_vector G U ⬝ᵥ y := blossomStrongDual_apply (G := G) U y
          _ ≤ blossom_rhs U := hvalid hyP
          _ = blossom_vector G U ⬝ᵥ x := by simpa [hxEq]
          _ = l x := (blossomStrongDual_apply (G := G) U x).symm
      · intro hx
        refine (mem_blossom_face_iff (G := G) (U := U) (x := x)).2 ⟨hx.1, ?_⟩
        have hx₀P : x₀ ∈ G.matchingPolytope := (mem_blossom_face_iff (G := G) (U := U) (x := x₀)).1 hx₀ |>.1
        have hx₀Eq : blossom_vector G U ⬝ᵥ x₀ = blossom_rhs U :=
          (mem_blossom_face_iff (G := G) (U := U) (x := x₀)).1 hx₀ |>.2
        have hx_le : l x ≤ l x₀ := by
          calc
            l x = blossom_vector G U ⬝ᵥ x := blossomStrongDual_apply (G := G) U x
            _ ≤ blossom_rhs U := hvalid hx.1
            _ = l x₀ := by
                  simpa [l, blossomStrongDual_apply (G := G) U x₀] using hx₀Eq.symm
        have hx_ge : l x₀ ≤ l x := hx.2 x₀ hx₀P
        have hx_eq : l x = l x₀ := le_antisymm hx_le hx_ge
        have hx_eq' : blossom_vector G U ⬝ᵥ x = blossom_vector G U ⬝ᵥ x₀ := by
          simpa [l, blossomStrongDual_apply (G := G) U x, blossomStrongDual_apply (G := G) U x₀]
            using hx_eq
        exact hx_eq'.trans hx₀Eq
    rw [hface_eq]
    exact ContinuousLinearMap.toExposed.isExposed
  · rw [Set.not_nonempty_iff_eq_empty.mp hface_nonempty]
    exact isExposed_empty

/-- Helper for Exercise 7.4: every point of `G.matchingPolytope` lies in the degree relaxation. -/
private lemma matchingPolytope_subset_matchingDegreeConstraintSet :
    G.matchingPolytope ⊆ matching_degree_constraint_set G := by
  intro x hx
  have hx' : x ∈ G.matchingConstraintSet := by
    rw [← matchingPolytope_eq_matchingConstraintSet (G := G)]
    exact hx
  exact matchingConstraintSet_subset_matchingDegreeConstraintSet (G := G) hx'

/-- Helper for Exercise 7.4: the aggregated coefficient vector attached to multipliers `u` and
`v` is `u ᵥ* A_G - v`. -/
private lemma matchingDegreeChvatalCoeff_eq_vecMul_sub
    (u : V → ℝ) (v : G.edgeSet → ℝ) :
    matching_degree_chvatal_coeff G u v = u ᵥ* (G.edgeIncMatrix ℝ) - v := by
  funext e
  -- Expand the column of `A_G`; its nonzero entries are exactly the endpoints incident to `e`.
  rw [Pi.sub_apply]
  simp [matching_degree_chvatal_coeff, Matrix.vecMul, dotProduct]
  calc
    (Finset.univ.filter fun w : V ↦ e ∈ incidentEdgeFinset G w).sum u =
        ∑ x : V, if e ∈ incidentEdgeFinset G x then u x else 0 := by
          rw [Finset.sum_filter]
    _ = ∑ x : V, u x * G.incMatrix ℝ x (e : Sym2 V) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          by_cases hinc : (e : Sym2 V) ∈ G.incidenceSet x
          · have hmem : e ∈ incidentEdgeFinset G x := by
              simpa [incidentEdgeFinset, SimpleGraph.edge_mem_incidenceSet_iff] using hinc
            simp [hmem, G.incMatrix_of_mem_incidenceSet (R := ℝ) hinc]
          · have hmem : e ∉ incidentEdgeFinset G x := by
              simpa [incidentEdgeFinset, SimpleGraph.edge_mem_incidenceSet_iff] using hinc
            simp [hmem, G.incMatrix_of_notMem_incidenceSet (R := ℝ) hinc]

/-- Helper for Exercise 7.4: at a covered vertex of a matching, the matching incidence vector has
exactly one incident edge coordinate equal to `1`. -/
private lemma matchingIncidenceFilter_sum_eq_one_of_mem_verts
    {M : G.Subgraph} (hM : M.IsMatching) {v : V} (hv : v ∈ M.verts) :
    (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum
        (G.subgraphIncidenceVector ℝ M) = 1 := by
  -- Use the unique matching edge through `v` as the lone nonzero term of the incidence sum.
  obtain ⟨w, hvw, huniq⟩ := hM hv
  let e₀ : G.edgeSet := ⟨s(v, w), M.adj_sub hvw⟩
  have he₀_mem :
      e₀ ∈ Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v := by
    simp [e₀, SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff]
  have he₀_val : G.subgraphIncidenceVector ℝ M e₀ = 1 := by
    have he₀_edge : e₀.1 ∈ M.edgeSet := Subgraph.mem_edgeSet.2 hvw
    simp [SimpleGraph.subgraphIncidenceVector, he₀_edge]
  calc
    (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum
        (G.subgraphIncidenceVector ℝ M) = G.subgraphIncidenceVector ℝ M e₀ := by
          refine Finset.sum_eq_single_of_mem e₀ he₀_mem ?_
          intro e he he_ne
          by_cases heM : e.1 ∈ M.edgeSet
          · have hv_e : v ∈ (e : Sym2 V) := by
              have he_inc : (e : Sym2 V) ∈ G.incidenceFinset v := (Finset.mem_filter.mp he).2
              simpa [SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff]
                using he_inc
            have hAdj_e : M.Adj v (Sym2.Mem.other hv_e) := by
              exact Subgraph.mem_edgeSet.1 (by simpa [Sym2.other_spec hv_e] using heM)
            have he_eq : e.1 = e₀.1 := by
              calc
                e.1 = s(v, Sym2.Mem.other hv_e) := by
                  symm
                  exact Sym2.other_spec hv_e
                _ = s(v, w) := by
                  rw [huniq _ hAdj_e]
                _ = e₀.1 := rfl
            exact (he_ne (Subtype.ext he_eq)).elim
          · simp [SimpleGraph.subgraphIncidenceVector, heM]
    _ = 1 := he₀_val

/-- Helper for Exercise 7.4: every matching incidence vector already satisfies the degree-system
relaxation `∑_{e ∈ δ(v)} x_e ≤ 1, x ≥ 0`. -/
private lemma subgraphIncidenceVector_mem_matchingDegreeConstraintSet_of_isMatching
    {M : G.Subgraph} (hM : M.IsMatching) :
    G.subgraphIncidenceVector ℝ M ∈ matching_degree_constraint_set G := by
  refine (mem_matching_degree_constraint_set_iff
    (G := G) (x := G.subgraphIncidenceVector ℝ M)).2 ?_
  refine ⟨?_, ?_⟩
  · intro v
    have hfilter_le :
        (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum
            (G.subgraphIncidenceVector ℝ M) ≤ 1 := by
      by_cases hv : v ∈ M.verts
      · -- Covered vertices contribute exactly one matching edge.
        have hsum_eq_one :=
          matchingIncidenceFilter_sum_eq_one_of_mem_verts (G := G) hM hv
        linarith
      · -- Uncovered vertices contribute no matching edge at all.
        have hsum_eq_zero :
            (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum
                (G.subgraphIncidenceVector ℝ M) = 0 := by
          refine Finset.sum_eq_zero ?_
          intro e he
          have hv_mem : v ∈ (e : Sym2 V) := by
            have he_inc : (e : Sym2 V) ∈ G.incidenceFinset v := (Finset.mem_filter.mp he).2
            simpa [SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff]
              using he_inc
          by_cases heM : e.1 ∈ M.edgeSet
          · exact (hv (Subgraph.mem_verts_of_mem_edge heM hv_mem)).elim
          · simp [SimpleGraph.subgraphIncidenceVector, heM]
        linarith
    -- Convert the Chapter 4 incidence-filter row to the Chapter 7 incident-edge finset row.
    rw [← incidenceFilter_sum_eq_incidentEdgeFinset_sum
      (G := G) (x := G.subgraphIncidenceVector ℝ M) v]
    exact hfilter_le
  · intro e
    -- Each edge coordinate of an incidence vector is a `0/1` indicator.
    by_cases he : e.1 ∈ M.edgeSet
    · simp [SimpleGraph.subgraphIncidenceVector, he]
    · simp [SimpleGraph.subgraphIncidenceVector, he]

/-- Helper for Exercise 7.4: every matching generator satisfies each Chvátal inequality derived
from the degree system. -/
private lemma matchingDegreeSystemChvatalInequality_valid_onMatchingGenerator
    {c : G.edgeSet → ℝ} {β : ℝ}
    (hchv : IsMatchingDegreeSystemChvatalInequality G c β)
    {M : G.Subgraph} (hM : M.IsMatching) :
    c ⬝ᵥ G.subgraphIncidenceVector ℝ M ≤ β := by
  rcases hchv with ⟨u, v, hu, hv, hint, rfl, rfl⟩
  let y : G.edgeSet → ℝ := G.subgraphIncidenceVector ℝ M
  have hy_deg : y ∈ matching_degree_constraint_set G := by
    -- Work directly with the matching generator instead of routing through the unresolved
    -- matching-polytope / matching-constraint bridge.
    simpa [y] using
      subgraphIncidenceVector_mem_matchingDegreeConstraintSet_of_isMatching (G := G) hM
  rcases (mem_matching_degree_constraint_set_iff (G := G) (x := y)).1 hy_deg with
    ⟨hy_row, hy_nonneg⟩
  have hdot_nonneg : 0 ≤ v ⬝ᵥ y := by
    rw [dotProduct]
    refine Finset.sum_nonneg ?_
    intro e he
    exact mul_nonneg (hv e) (hy_nonneg e)
  have hupper :
      matching_degree_chvatal_coeff G u v ⬝ᵥ y ≤ ∑ w : V, u w := by
    calc
      matching_degree_chvatal_coeff G u v ⬝ᵥ y
          = u ⬝ᵥ ((G.edgeIncMatrix ℝ).mulVec y) - v ⬝ᵥ y := by
              rw [matchingDegreeChvatalCoeff_eq_vecMul_sub (G := G) u v]
              rw [sub_dotProduct, Matrix.dotProduct_mulVec]
      _ ≤ u ⬝ᵥ (1 : V → ℝ) := by
            have hrow_le :
                u ⬝ᵥ ((G.edgeIncMatrix ℝ).mulVec y) ≤ u ⬝ᵥ (1 : V → ℝ) := by
              refine dotProduct_le_dotProduct_of_nonneg_left ?_ hu
              intro w
              simpa [incidentEdgeFinset_sum_eq_edgeIncMatrix_mulVec (G := G) y w] using hy_row w
            linarith
      _ = ∑ w : V, u w := by
            simp [dotProduct]
  have hterm_int :
      ∀ e : G.edgeSet, ∃ z : ℤ, matching_degree_chvatal_coeff G u v e * y e = (z : ℝ) := by
    intro e
    rcases hint e with ⟨z, hz⟩
    by_cases he : e.1 ∈ M.edgeSet
    · refine ⟨z, ?_⟩
      simp [y, SimpleGraph.subgraphIncidenceVector, he, hz]
    · refine ⟨0, ?_⟩
      simp [y, SimpleGraph.subgraphIncidenceVector, he]
  choose z hz using hterm_int
  have hdot_int :
      ∃ z' : ℤ, matching_degree_chvatal_coeff G u v ⬝ᵥ y = (z' : ℝ) := by
    refine ⟨∑ e, z e, ?_⟩
    simp [dotProduct, hz]
  rcases hdot_int with ⟨z', hz'⟩
  have hz'_floor : z' ≤ Int.floor (∑ w : V, u w) := by
    exact Int.le_floor.mpr (by simpa [hz'] using hupper)
  have hz'_real : (z' : ℝ) ≤ (Int.floor (∑ w : V, u w) : ℝ) := by
    exact_mod_cast hz'_floor
  rw [hz']
  exact hz'_real

/-- Helper for Exercise 7.4: part (1) is needed before the closure-to-polytope step, so we expose
the blossom Chvatal certificate as an earlier helper and keep the theorem statement below as a
thin wrapper. -/
private lemma blossomIsMatchingDegreeSystemChvatal
    (U : Set V) (hUodd : Odd U.ncard) :
    IsMatchingDegreeSystemChvatalInequality G (blossom_vector G U) (blossom_rhs U) := by
  let u : V → ℝ := fun w ↦ if w ∈ U then (1 / 2 : ℝ) else 0
  let v : G.edgeSet → ℝ := fun e ↦
    (Finset.univ.filter fun w : V ↦ e ∈ incidentEdgeFinset G w).sum u - blossom_vector G U e
  have hu_nonneg : ∀ w, 0 ≤ u w := by
    intro w
    -- The degree multipliers are exactly the nonnegative half-indicators of `U`.
    by_cases hw : w ∈ U <;> simp [u, hw]
  have hv_nonneg : ∀ e, 0 ≤ v e := by
    intro e
    have hne : e.1.out.1 ≠ e.1.out.2 := by
      have hadj : G.Adj e.1.out.1 e.1.out.2 := by
        have he : s(e.1.out.1, e.1.out.2) ∈ G.edgeSet := by
          simpa [e.1.out_eq] using e.prop
        exact (SimpleGraph.mem_edgeSet (G := G) (v := e.1.out.1) (w := e.1.out.2)).1 he
      exact G.ne_of_adj hadj
    by_cases heU : e ∈ E[G] U
    · have hEnds : e.1.out.1 ∈ U ∧ e.1.out.2 ∈ U :=
        (memInducedEdgeFinsetEndpointsIff (G := G) U e).1 heU
      have hsum_eq_one :
          (Finset.univ.filter fun w : V ↦ e ∈ incidentEdgeFinset G w).sum u = 1 := by
        -- On an induced edge, both canonical endpoints contribute `1/2`.
        rw [incidentVertexFinset_eq_edgeToFinset (G := G) e, edgeToFinset_eq_pair (G := G) e]
        norm_num [u, hne, hEnds.1, hEnds.2]
      -- The chosen slack vanishes on induced edges because the aggregate coefficient is already `1`.
      simp [v, blossom_vector, heU, hsum_eq_one]
    · have hsum_nonneg :
          0 ≤ (Finset.univ.filter fun w : V ↦ e ∈ incidentEdgeFinset G w).sum u := by
        -- Outside the induced-edge case, the blossom coefficient is `0`, so nonnegativity comes
        -- from summing nonnegative endpoint weights.
        rw [incidentVertexFinset_eq_edgeToFinset (G := G) e, edgeToFinset_eq_pair (G := G) e]
        by_cases h₁ : e.1.out.1 ∈ U <;> by_cases h₂ : e.1.out.2 ∈ U <;> simp [u, hne, h₁, h₂]
      have hblossom : blossom_vector G U e = 0 := by
        simp [blossom_vector, heU]
      -- Here the slack equals the nonnegative endpoint-weight sum itself.
      simp [v, hblossom, hsum_nonneg]
  have hcoeff :
      matching_degree_chvatal_coeff G u v = blossom_vector G U := by
    funext e
    -- The slack was chosen precisely to turn the half-degree combination into the blossom vector.
    simp [matching_degree_chvatal_coeff, v]
  have hsum_u :
      ∑ w : V, u w = (U.ncard : ℝ) / 2 := by
    letI : Fintype U := Fintype.ofFinite U
    have hUfinset : (Finset.univ.filter fun w : V ↦ w ∈ U) = U.toFinset := by
      ext w
      simp
    -- Summing the half-indicator of `U` counts exactly `|U| / 2`.
    calc
      ∑ w : V, u w = (Finset.univ.filter fun w : V ↦ w ∈ U).sum (fun _ ↦ (1 / 2 : ℝ)) := by
        rw [Finset.sum_filter]
      _ = (U.toFinset.card : ℝ) * (1 / 2 : ℝ) := by
        rw [hUfinset]
        simp
      _ = (U.ncard : ℝ) / 2 := by
        have hcard : U.toFinset.card = U.ncard := by
          simpa [Set.ncard] using (Set.toFinset_card U)
        rw [show (U.ncard : ℝ) / 2 = (U.ncard : ℝ) * (1 / 2 : ℝ) by ring]
        exact congrArg (fun n : ℕ ↦ (n : ℝ) * (1 / 2 : ℝ)) hcard
  rcases hUodd with ⟨k, hk⟩
  refine (isMatchingDegreeSystemChvatalInequality_iff
    (G := G) (c := blossom_vector G U) (β := blossom_rhs U)).2 ?_
  refine ⟨u, v, hu_nonneg, hv_nonneg, ?_, ?_, ?_⟩
  · intro e
    refine ⟨if e ∈ E[G] U then 1 else 0, ?_⟩
    -- The aggregate coefficient is exactly the `0/1` blossom coefficient on each edge.
    simpa [blossom_vector] using congrArg (fun f ↦ f e) hcoeff
  · intro e
    -- Read the coefficient identity pointwise.
    simpa using (congrArg (fun f ↦ f e) hcoeff).symm
  · -- The right-hand side is the floor of the half-size sum, i.e. `( |U| - 1 ) / 2` for odd `U`.
    rw [hsum_u, blossom_rhs, hk]
    have hhalf : ((((2 * k + 1 : ℕ) : ℝ) / 2)) = (1 / 2 : ℝ) + k := by
      norm_num [Nat.cast_add, Nat.cast_mul]
      ring
    rw [hhalf, Int.floor_add_natCast]
    norm_num

/-- Helper for Exercise 7.4: every point of `G.matchingPolytope` lies in the first Chvátal
closure of the degree system because the closure cuts are valid on the matching generators. -/
private lemma matchingPolytope_subset_matchingDegreeChvatalClosure :
    G.matchingPolytope ⊆ matching_degree_chvatal_closure G := by
  intro x hx
  refine (mem_matching_degree_chvatal_closure_iff (G := G) (x := x)).2 ?_
  refine ⟨matchingPolytope_subset_matchingDegreeConstraintSet (G := G) hx, ?_⟩
  intro c β hchv
  rw [SimpleGraph.matchingPolytope, mem_convexHull_iff_exists_fintype] at hx
  rcases hx with ⟨ι, _, w, z, hw_nonneg, hw_sum, hz, rfl⟩
  have hzvalid : ∀ i, c ⬝ᵥ z i ≤ β := by
    intro i
    rcases hz i with ⟨M, hM, hzEq⟩
    rw [hzEq]
    exact matchingDegreeSystemChvatalInequality_valid_onMatchingGenerator
      (G := G) hchv hM
  calc
    c ⬝ᵥ ∑ i, w i • z i = ∑ i, w i * (c ⬝ᵥ z i) := by
      rw [dotProduct_sum]
      refine Finset.sum_congr rfl ?_
      intro i hi
      simpa [smul_eq_mul] using dotProduct_smul c (w i) (z i)
    _ ≤ ∑ i, w i * β := by
          refine Finset.sum_le_sum ?_
          intro i hi
          exact mul_le_mul_of_nonneg_left (hzvalid i) (hw_nonneg i)
    _ = β * ∑ i, w i := by
          simpa [mul_comm] using
            (Finset.mul_sum (s := (Finset.univ : Finset ι)) (a := β) (f := fun i ↦ w i)).symm
    _ = β := by
          rw [hw_sum, mul_one]

/-- Helper for Exercise 7.4: the Chvátal closure is contained in the matching polytope because
part (1) recovers every odd-set inequality on top of the degree relaxation. -/
private lemma matchingDegreeChvatalClosure_subset_matchingPolytope :
    matching_degree_chvatal_closure G ⊆ G.matchingPolytope := by
  intro x hx
  rcases (mem_matching_degree_chvatal_closure_iff (G := G) (x := x)).1 hx with ⟨hx_deg, hx_cuts⟩
  have hx_match : x ∈ G.matchingConstraintSet := by
    rcases (mem_matching_degree_constraint_set_iff (G := G) (x := x)).1 hx_deg with
      ⟨hx_row, hx_nonneg⟩
    refine (SimpleGraph.mem_matchingConstraintSet_iff (G := G) (x := x)).2 ?_
    refine ⟨hx_nonneg, ?_, ?_⟩
    · intro v
      rw [incidenceFilter_sum_eq_incidentEdgeFinset_sum (G := G) x v]
      exact hx_row v
    · intro U hUodd
      have hblossom :
          blossom_vector G U ⬝ᵥ x ≤ blossom_rhs U := by
        exact hx_cuts (blossom_vector G U) (blossom_rhs U)
          (blossomIsMatchingDegreeSystemChvatal (G := G) U hUodd)
      simpa [blossomVector_dot_eq_inducedEdgeSum (G := G) U x] using hblossom
  rw [matchingPolytope_eq_matchingConstraintSet (G := G)]
  exact hx_match

/-- Exercise 7.4 (1). For every odd vertex set `U`, the blossom inequality `(4.17)`
`∑_{e ∈ E(U)} x_e ≤ (|U| - 1)/2` is a Chvátal inequality for the degree system
`∑_{e ∈ δ(v)} x_e ≤ 1` together with `x ≥ 0`. -/
theorem exercise_7_4_blossom_is_matching_degree_system_chvatal
    (U : Set V) (hUodd : Odd U.ncard) :
    IsMatchingDegreeSystemChvatalInequality G (blossom_vector G U) (blossom_rhs U) := by
  -- Keep the public theorem statement fixed and reuse the earlier helper in the dependency order
  -- required by the closure proof.
  exact blossomIsMatchingDegreeSystemChvatal (G := G) U hUodd

/-- Helper for Exercise 7.4: summing the ambient incident-edge coordinates of a subgraph
incidence vector counts the degree in that subgraph. -/
private lemma incidentIncidenceSum_eq_degree
    (H : G.Subgraph) (v : V) :
    (incidentEdgeFinset G v).sum (G.subgraphIncidenceVector ℝ H) = H.degree v := by
  classical
  let incidentInH : Finset G.edgeSet :=
    (incidentEdgeFinset G v).filter fun e ↦ e.1 ∈ H.edgeSet
  have hsum :
      (incidentEdgeFinset G v).sum (G.subgraphIncidenceVector ℝ H) =
        (incidentInH.card : ℝ) := by
    calc
      (incidentEdgeFinset G v).sum (G.subgraphIncidenceVector ℝ H) =
          incidentInH.sum (fun _ ↦ (1 : ℝ)) := by
            simpa [incidentInH, SimpleGraph.subgraphIncidenceVector] using
              (Finset.sum_filter
                (s := incidentEdgeFinset G v)
                (p := fun e : G.edgeSet ↦ e.1 ∈ H.edgeSet)
                (f := fun _ ↦ (1 : ℝ))).symm
      _ = (incidentInH.card : ℝ) := by
            simp
  let edgeEmbedding : G.edgeSet ↪ Sym2 V :=
    ⟨fun e ↦ (e : Sym2 V), Subtype.val_injective⟩
  have hmap :
      Finset.map edgeEmbedding incidentInH = H.spanningCoe.incidenceFinset v := by
    ext e
    constructor
    · intro he
      rcases Finset.mem_map.1 he with ⟨eG, heG, rfl⟩
      rcases Finset.mem_filter.1 heG with ⟨hinc, hedgeH⟩
      rw [SimpleGraph.mem_incidenceFinset]
      exact ⟨by simpa using hedgeH,
        (mem_incidentEdgeFinset_iff (G := G) (v := v) (e := eG)).1 hinc⟩
    · intro he
      rw [SimpleGraph.mem_incidenceFinset] at he
      rcases he with ⟨hedgeH, hv⟩
      let eG : G.edgeSet := ⟨e, H.edgeSet_subset hedgeH⟩
      refine Finset.mem_map.2 ⟨eG, ?_, rfl⟩
      exact Finset.mem_filter.2
        ⟨(mem_incidentEdgeFinset_iff (G := G) (v := v) (e := eG)).2 hv, by simpa using hedgeH⟩
  have hcardNat : incidentInH.card = H.degree v := by
    calc
      incidentInH.card = (H.spanningCoe.incidenceFinset v).card := by
        simpa using congrArg Finset.card hmap
      _ = H.spanningCoe.degree v := by
        simpa using H.spanningCoe.card_incidenceFinset_eq_degree v
      _ = H.degree v := by
        simpa using (Subgraph.degree_spanningCoe (G' := H) v)
  calc
    (incidentEdgeFinset G v).sum (G.subgraphIncidenceVector ℝ H) = (incidentInH.card : ℝ) := hsum
    _ = H.degree v := by
          exact congrArg (fun n : ℕ ↦ (n : ℝ)) hcardNat

/-- Helper for Exercise 7.4: the edges of a subgraph `T` correspond bijectively to the ambient
edges of `G` that lie in `T.edgeSet`. -/
private lemma cardEdgeSetSubtypeEq
    (T : G.Subgraph) :
    Fintype.card {e : G.edgeSet // e.1 ∈ T.edgeSet} = Fintype.card T.edgeSet := by
  classical
  refine Fintype.card_congr ?_
  refine
    { toFun := fun e ↦ ⟨e.1.1, e.2⟩
      invFun := fun e ↦ ⟨⟨e.1, T.edgeSet_subset e.2⟩, e.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro e
    cases e
    rfl
  · intro e
    cases e
    rfl

/-- Helper for Exercise 7.4: summing the edge-indicator of a subgraph over all ambient edges of
`G` recovers the number of edges of that subgraph. -/
private lemma sumEdgeIndicatorEqCardEdgeSet
    (T : G.Subgraph) :
    (∑ e : G.edgeSet, if e.1 ∈ T.edgeSet then (1 : ℝ) else 0) = Fintype.card T.edgeSet := by
  classical
  calc
    (∑ e : G.edgeSet, if e.1 ∈ T.edgeSet then (1 : ℝ) else 0) =
        ((Finset.univ.filter fun e : G.edgeSet ↦ e.1 ∈ T.edgeSet).card : ℝ) := by
          simpa using
            (Finset.sum_boole (fun e : G.edgeSet ↦ e.1 ∈ T.edgeSet) Finset.univ : _)
    _ = (Fintype.card {e : G.edgeSet // e.1 ∈ T.edgeSet} : ℝ) := by
          exact congrArg (fun n : ℕ ↦ (n : ℝ))
            ((Fintype.card_of_subtype
              (Finset.univ.filter fun e : G.edgeSet ↦ e.1 ∈ T.edgeSet)
              (by
                intro e
                simp)).symm)
    _ = Fintype.card T.edgeSet := by
          exact congrArg (fun n : ℕ ↦ (n : ℝ)) (cardEdgeSetSubtypeEq (G := G) T)

/-- Helper for Exercise 7.4: `T.induce S` keeps exactly the edges of `T` whose endpoints both lie
in `S`. -/
private lemma induceEdgeSetEqInterInduceTop
    (T : G.Subgraph) (S : Set V) :
    (T.induce S).edgeSet = T.edgeSet ∩ ((⊤ : G.Subgraph).induce S).edgeSet := by
  -- Both sides express the same endpoint-membership condition on ambient edges.
  ext e
  induction e using Sym2.ind with
  | h u v =>
      simp only [SimpleGraph.Subgraph.mem_edgeSet, Set.mem_inter_iff, SimpleGraph.Subgraph.induce]
      constructor
      · rintro ⟨hu, hv, huv⟩
        exact ⟨huv, hu, hv, T.adj_sub huv⟩
      · rintro ⟨huv, hu, hv, _⟩
        exact ⟨hu, hv, huv⟩

/-- Helper for Exercise 7.4: the induced-edge sum of a subgraph incidence vector is the number of
induced edges of the restricted subgraph. -/
private lemma inducedIncidenceSumEqCardInducedEdges
    (T : G.Subgraph) (S : Finset V) :
    Finset.sum (G.inducedEdgeFinset (S : Set V)) (fun e ↦ G.subgraphIncidenceVector ℝ T e) =
      Fintype.card ((T.induce (S : Set V)).edgeSet) := by
  classical
  calc
    Finset.sum (G.inducedEdgeFinset (S : Set V)) (fun e ↦ G.subgraphIncidenceVector ℝ T e) =
        ∑ e : G.edgeSet,
          if e.1 ∈ ((⊤ : G.Subgraph).induce (S : Set V)).edgeSet then
            G.subgraphIncidenceVector ℝ T e
          else 0 := by
            rw [SimpleGraph.inducedEdgeFinset, Finset.sum_filter]
    _ = ∑ e : G.edgeSet, if e.1 ∈ (T.induce (S : Set V)).edgeSet then (1 : ℝ) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro e he
          have hmem :
              e.1 ∈ (T.induce (S : Set V)).edgeSet ↔
                e.1 ∈ ((⊤ : G.Subgraph).induce (S : Set V)).edgeSet ∧ e.1 ∈ T.edgeSet := by
            rw [induceEdgeSetEqInterInduceTop (G := G) T (S : Set V)]
            simpa [and_comm]
          by_cases hS : e.1 ∈ ((⊤ : G.Subgraph).induce (S : Set V)).edgeSet
          · by_cases hT : e.1 ∈ T.edgeSet
            · simp [SimpleGraph.subgraphIncidenceVector, hS, hT, hmem]
            · simp [SimpleGraph.subgraphIncidenceVector, hS, hT, hmem]
          · simp [hS, hmem, SimpleGraph.subgraphIncidenceVector]
    _ = Fintype.card ((T.induce (S : Set V)).edgeSet) := by
          simpa using sumEdgeIndicatorEqCardEdgeSet (G := G) (T.induce (S : Set V))

/-- Helper for Exercise 7.4: a nonbipartite graph has a connected component that is already
nonbipartite. -/
private lemma exists_nonbipartite_connectedComponent
    (hG : ¬ G.IsBipartite) :
    ∃ c : G.ConnectedComponent, ¬ c.toSimpleGraph.IsBipartite := by
  by_contra h
  have hcomp : ∀ c : G.ConnectedComponent, c.toSimpleGraph.IsBipartite := by
    intro c
    by_contra hc
    exact h ⟨c, hc⟩
  exact hG (by
    simpa using
      (SimpleGraph.colorable_iff_forall_connectedComponents (G := G) (n := 2)).2 hcomp)

/-- Helper for Exercise 7.4: on a nonbipartite graph the degree relaxation is strictly larger than
the matching polytope, witnessed by the half-incidence vector of an odd cycle. -/
private lemma matchingDegreeConstraintSet_ne_matchingPolytope_of_not_isBipartite
    (hG : ¬ G.IsBipartite) :
    matching_degree_constraint_set G ≠ G.matchingPolytope := by
  -- Route correction: the previous odd-cycle extraction uses stale `Coloring`/`Walk.map` APIs.
  -- TODO: reprove this separation witness with the current connected-component odd-cycle API.
  sorry

/-- Exercise 7.4 (2). If `G` is not bipartite, then some blossom inequality is facet-defining for
the matching polytope of `G`. -/
theorem exercise_7_4_exists_facet_defining_blossom_of_not_isBipartite
    (hG : ¬ G.IsBipartite) :
    ∃ U : Set V, Odd U.ncard ∧
      is_valid_inequality G.matchingPolytope (blossom_vector G U) (blossom_rhs U) ∧
        IsFacetOf G.matchingPolytope (blossom_face G U) := by
  -- Route correction: the only unclosed step is the facet upgrade after transporting through the
  -- matching-polytope/constraint-set bridge from Theorem 4.24.
  -- TODO: once the compiled Theorem 4.24 dependency is available in this runner, combine
  -- `blossomFace_eq_faceSet` with a chosen odd witness and the irredundant-row / maximal-face
  -- argument for the facet conclusion.
  sorry

/-- Exercise 7.4 (3). The matching polytope has Chvátal rank zero or one with respect to the
degree-system relaxation `∑_{e ∈ δ(v)} x_e ≤ 1, x ≥ 0`. -/
theorem exercise_7_4_matching_polytope_chvatal_rank_zero_or_one :
    matching_degree_system_has_chvatal_rank_zero G ∨
      matching_degree_system_has_chvatal_rank_one G := by
  by_cases hG : G.IsBipartite
  · left
    -- In the bipartite branch, the degree relaxation is already the matching polytope.
    exact matchingDegreeConstraintSet_eq_matchingPolytope_of_isBipartite (G := G) hG
  · right
    refine (matching_degree_system_has_chvatal_rank_one_iff (G := G)).2 ?_
    refine ⟨?_, ?_⟩
    · exact le_antisymm
        (matchingDegreeChvatalClosure_subset_matchingPolytope (G := G))
        (matchingPolytope_subset_matchingDegreeChvatalClosure (G := G))
    · exact matchingDegreeConstraintSet_ne_matchingPolytope_of_not_isBipartite (G := G) hG

/-- Exercise 7.4 (4). The matching polytope has Chvátal rank one with respect to the degree
system `∑_{e ∈ δ(v)} x_e ≤ 1, x ≥ 0` if and only if `G` is not bipartite. -/
theorem exercise_7_4_matching_polytope_chvatal_rank_one_iff_not_isBipartite :
    matching_degree_system_has_chvatal_rank_one G ↔ ¬ G.IsBipartite := by
  constructor
  · intro hRankOne hG
    rcases (matching_degree_system_has_chvatal_rank_one_iff (G := G)).1 hRankOne with
      ⟨-, hneq⟩
    exact hneq (matchingDegreeConstraintSet_eq_matchingPolytope_of_isBipartite (G := G) hG)
  · intro hG
    rcases exercise_7_4_matching_polytope_chvatal_rank_zero_or_one (G := G) with hZero | hOne
    · exfalso
      exact
        (matchingDegreeConstraintSet_ne_matchingPolytope_of_not_isBipartite (G := G) hG)
          ((matching_degree_system_has_chvatal_rank_zero_iff (G := G)).1 hZero)
    · exact hOne

end Exercise74

/-- `blossom_rhs U` is the displayed value `( |U| - 1 ) / 2`. -/
theorem blossom_rhs_eq
    {V : Type} (U : Set V) :
    blossom_rhs U = ((U.ncard : ℝ) - 1) / 2 := rfl
