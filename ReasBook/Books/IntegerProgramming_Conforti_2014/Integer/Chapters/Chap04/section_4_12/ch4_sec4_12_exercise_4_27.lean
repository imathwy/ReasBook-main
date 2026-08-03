import Integer.Chapters.Chap03.section_3_5_2.ch3_sec3_5_2_corollary_3_14
import Integer.Chapters.Chap03.section_3_4_1.ch3_sec3_4_1_definition_3_4_1_extra_1
import Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_exercise_3_25
import Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_theorem_3_24
import Integer.Chapters.Chap03.section_3_10.ch3_sec3_10_theorem_3_34
import Integer.Chapters.Chap03.section_3_14.ch3_sec3_14_corollary_3_41

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators symmDiff

attribute [local instance] Classical.propDecidable

-- Primary domain: finite graph matchings and matching polytopes.
-- Core/canonical owners reused below: `SimpleGraph.Subgraph.IsMatching`,
-- `SimpleGraph.subgraphIncidenceVector`, `SimpleGraph.matchingPolytope`,
-- and the Chapter 3 edge/skeleton owners `IsEdgeOf` and `polytope_skeleton`.

universe u

namespace SimpleGraph

/-- The `0,1` incidence vector of a subgraph of `G`, viewed in the edge coordinates of `G` with
values in `R`. -/
def subgraphIncidenceVector {V : Type u} (G : SimpleGraph V) (R : Type*) [Zero R] [One R]
    (M : G.Subgraph) : G.edgeSet → R :=
  fun e ↦ if e.1 ∈ M.edgeSet then 1 else 0

/-- The matching polytope of `G`, defined as the convex hull of the incidence vectors of the
matchings of `G`. -/
def matchingPolytope {V : Type u} (G : SimpleGraph V) : Set (G.edgeSet → ℝ) :=
  convexHull ℝ {x | ∃ M : G.Subgraph, M.IsMatching ∧ x = G.subgraphIncidenceVector ℝ M}

/-- A graph is a cycle or a path when it is exactly the spanning coercion of the subgraph traced by
some cycle walk, or exactly the spanning coercion of the subgraph traced by some nontrivial path
walk. -/
def IsCycleOrPath {V : Type u} (H : SimpleGraph V) : Prop :=
  (∃ v, ∃ p : H.Walk v v, p.IsCycle ∧ p.toSubgraph.spanningCoe = H) ∨
    ∃ u v, u ≠ v ∧ ∃ p : H.Walk u v, p.IsPath ∧ p.toSubgraph.spanningCoe = H

end SimpleGraph

section EdgeOwners

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Helper for Exercise 4.27: an edge of `P` is a one-dimensional convex extreme subset of `P`. -/
@[mk_iff]
class IsEdgeOf (P F : Set E) : Prop where
  /-- The carrier of an edge is convex. -/
  convex : Convex ℝ F
  /-- The subset `F` is extreme in `P`. -/
  isExtreme : IsExtreme ℝ P F
  /-- The direction of the affine span of `F` is one-dimensional. -/
  finrank_direction_eq_one : Module.finrank ℝ (affineSpan ℝ F).direction = 1

/-- Helper for Exercise 4.27: an edge is in particular an extreme subset. -/
instance instIsExtremeOfIsEdgeOf {P F : Set E} [h : IsEdgeOf P F] : IsExtreme ℝ P F :=
  h.isExtreme

/-- Helper for Exercise 4.27: a nondegenerate extreme segment is exactly an edge segment. -/
theorem isEdgeOf_segment_iff {P : Set E} {v w : E} (hvw : v ≠ w) :
    IsEdgeOf P (segment ℝ v w) ↔ IsExtreme ℝ P (segment ℝ v w) := by
  constructor
  · intro h
    -- Every edge is extreme by definition.
    exact h.isExtreme
  · intro h
    -- The affine span of a nondegenerate segment is one-dimensional.
    refine ⟨convex_segment _ _, h, ?_⟩
    rw [direction_affineSpan, vectorSpan_segment]
    simpa using finrank_span_singleton (vsub_ne_zero.2 hvw.symm)

/-- Helper for Exercise 4.27: the edge condition on a segment is symmetric in its endpoints. -/
theorem isEdgeOf_segment_symm {P : Set E} {v w : E} :
    IsEdgeOf P (segment ℝ v w) ↔ IsEdgeOf P (segment ℝ w v) := by
  by_cases hvw : v = w
  · subst hvw
    rfl
  · rw [isEdgeOf_segment_iff hvw, isEdgeOf_segment_iff (Ne.symm hvw)]
    simp [segment_symm]

/-- Helper for Exercise 4.27: the skeleton of `P` is the graph on its extreme points whose edges
are the edge segments of `P`. -/
def polytope_skeleton (P : Set E) : SimpleGraph (P.extremePoints ℝ) :=
  SimpleGraph.fromRel fun v w ↦ IsEdgeOf P (segment ℝ (v : E) (w : E))

/-- Helper for Exercise 4.27: adjacency in the skeleton means distinct vertices joined by an edge
segment of `P`. -/
theorem polytope_skeleton_adj_iff {P : Set E} {v w : P.extremePoints ℝ} :
    (polytope_skeleton P).Adj v w ↔
      v ≠ w ∧ IsEdgeOf P (segment ℝ (v : E) (w : E)) := by
  -- Unfold the graph relation and normalize the endpoint symmetry once.
  simp [polytope_skeleton, isEdgeOf_segment_symm]

end EdgeOwners

private abbrev componentGraph {V : Type u} {G : SimpleGraph V}
    (c : G.ConnectedComponent) : SimpleGraph c.supp :=
  c.toSimpleGraph

private abbrev componentEdgeNonempty {V : Type u} {G : SimpleGraph V}
    (c : G.ConnectedComponent) : Prop :=
  (componentGraph c).edgeSet.Nonempty

private abbrev componentSpanningGraph {V : Type u} {G : SimpleGraph V}
    (c : G.ConnectedComponent) : SimpleGraph V :=
  (componentGraph c).spanningCoe

private abbrev componentSpanningEdgeSet {V : Type u} {G : SimpleGraph V}
    (c : G.ConnectedComponent) : Set (Sym2 V) :=
  (componentSpanningGraph c).edgeSet

private abbrev walkSpanningGraph {V : Type u} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) : SimpleGraph V :=
  p.toSubgraph.spanningCoe

section Exercise_4_27

variable {V : Type u}
variable (G : SimpleGraph V)

local instance : DecidableEq V := Classical.decEq V
local instance : DecidableRel G.Adj := Classical.decRel G.Adj

section FinitePart_1

/-- Helper for Exercise 4.27: a matching incidence vector is an extreme point of the matching
polytope. -/
theorem subgraphIncidenceVector_mem_extremePoints_matchingPolytope
    {M : G.Subgraph} (hM : M.IsMatching) :
    G.subgraphIncidenceVector ℝ M ∈ (G.matchingPolytope).extremePoints ℝ := by
  let S : Set (G.edgeSet → ℝ) :=
    {x | ∃ T : G.Subgraph, T.IsMatching ∧ x = G.subgraphIncidenceVector ℝ T}
  have hS_zero_one :
      S ⊆ Set.univ.pi fun _ : G.edgeSet ↦ ({0, 1} : Set ℝ) := by
    intro x hx
    rcases hx with ⟨T, hT, rfl⟩
    rw [Set.mem_univ_pi]
    intro e
    by_cases he : e.1 ∈ T.edgeSet
    · simp [SimpleGraph.subgraphIncidenceVector, he]
    · simp [SimpleGraph.subgraphIncidenceVector, he]
  have hzero_one_unit_box :
      Set.univ.pi (fun _ : G.edgeSet ↦ ({0, 1} : Set ℝ)) ⊆
        Set.univ.pi (fun _ : G.edgeSet ↦ Set.Icc (0 : ℝ) 1) := by
    intro x hx
    rw [Set.mem_univ_pi] at hx ⊢
    intro e
    have hxe : x e = 0 ∨ x e = 1 := by
      simpa using hx e
    rcases hxe with h0 | h1
    · rw [h0]
      simp
    · rw [h1]
      simp
  have hS_unit_box :
      S ⊆ Set.univ.pi (fun _ : G.edgeSet ↦ Set.Icc (0 : ℝ) 1) :=
    hS_zero_one.trans hzero_one_unit_box
  have hHull_unit_box :
      convexHull ℝ S ⊆ Set.univ.pi (fun _ : G.edgeSet ↦ Set.Icc (0 : ℝ) 1) := by
    refine convexHull_min hS_unit_box ?_
    exact convex_pi fun _ _ ↦ convex_Icc (0 : ℝ) 1
  have hxS : G.subgraphIncidenceVector ℝ M ∈ S := ⟨M, hM, rfl⟩
  have hxHull : G.subgraphIncidenceVector ℝ M ∈ convexHull ℝ S :=
    subset_convexHull ℝ S hxS
  have hxBoxExtreme :
      G.subgraphIncidenceVector ℝ M ∈
        (Set.univ.pi (fun _ : G.edgeSet ↦ Set.Icc (0 : ℝ) 1)).extremePoints ℝ := by
    rw [extremePoints_pi]
    simpa [zero_le_one] using hS_zero_one hxS
  simpa [SimpleGraph.matchingPolytope, S] using
    inter_extremePoints_subset_extremePoints_of_subset hHull_unit_box ⟨hxHull, hxBoxExtreme⟩

variable [Finite V]
local instance : Fintype V := Fintype.ofFinite V

/-- Exercise 4.27 (1). Two matching incidence vectors span an edge of the matching polytope
exactly when the symmetric difference of the matchings is a path or a cycle. -/
theorem matchingIncidenceVector_segment_isEdgeOf_iff_symmDiff_isCycleOrPath
    {M N : G.Subgraph} (hM : M.IsMatching) (hN : N.IsMatching) :
    IsEdgeOf G.matchingPolytope
      (segment ℝ (G.subgraphIncidenceVector ℝ M) (G.subgraphIncidenceVector ℝ N)) ↔
      (M.spanningCoe ∆ N.spanningCoe).IsCycleOrPath := by
  admit

/-- Helper for Exercise 4.27: adjacency in the matching-polytope skeleton is the path-or-cycle
criterion on the symmetric difference. -/
theorem matchingIncidenceVector_adjacent_vertices_iff_symmDiff_isCycleOrPath
    {M N : G.Subgraph} (hM : M.IsMatching) (hN : N.IsMatching) :
    (polytope_skeleton G.matchingPolytope).Adj
        ⟨G.subgraphIncidenceVector ℝ M,
          subgraphIncidenceVector_mem_extremePoints_matchingPolytope G hM⟩
        ⟨G.subgraphIncidenceVector ℝ N,
          subgraphIncidenceVector_mem_extremePoints_matchingPolytope G hN⟩ ↔
      (M.spanningCoe ∆ N.spanningCoe).IsCycleOrPath := by
  rw [polytope_skeleton_adj_iff,
    matchingIncidenceVector_segment_isEdgeOf_iff_symmDiff_isCycleOrPath G hM hN]
  constructor
  · rintro ⟨hMN, hcycleOrPath⟩
    exact hcycleOrPath
  · intro hcycleOrPath
    refine ⟨?_, hcycleOrPath⟩
    intro hMN
    have hbot_not_cycleOrPath : ¬ (⊥ : SimpleGraph V).IsCycleOrPath := by
      intro h
      rcases h with ⟨v, p, hpCycle, _⟩ | ⟨u, v, huv, p, hpPath, _⟩
      · cases p with
        | nil =>
            exact hpCycle.not_nil (by simp)
        | cons h p =>
            cases h
      · cases p with
        | nil =>
            exact huv rfl
        | cons h p =>
            cases h
    have hval :
        G.subgraphIncidenceVector ℝ M = G.subgraphIncidenceVector ℝ N :=
      congrArg Subtype.val hMN
    have hspan : M.spanningCoe = N.spanningCoe := by
      ext v w
      constructor
      · intro hMvw
        let e : G.edgeSet := ⟨s(v, w), M.adj_sub hMvw⟩
        have heq : G.subgraphIncidenceVector ℝ M e = G.subgraphIncidenceVector ℝ N e := by
          simpa using congrFun hval e
        have hNe : e.1 ∈ N.edgeSet := by
          by_cases heN : e.1 ∈ N.edgeSet
          · exact heN
          · have hMe : e.1 ∈ M.edgeSet := SimpleGraph.Subgraph.mem_edgeSet.2 hMvw
            exfalso
            simp [SimpleGraph.subgraphIncidenceVector, hMe, heN] at heq
        simpa [e] using (SimpleGraph.Subgraph.mem_edgeSet.1 hNe)
      · intro hNvw
        let e : G.edgeSet := ⟨s(v, w), N.adj_sub hNvw⟩
        have heq : G.subgraphIncidenceVector ℝ M e = G.subgraphIncidenceVector ℝ N e := by
          simpa using congrFun hval e
        have hMe : e.1 ∈ M.edgeSet := by
          by_cases heM : e.1 ∈ M.edgeSet
          · exact heM
          · have hNe : e.1 ∈ N.edgeSet := SimpleGraph.Subgraph.mem_edgeSet.2 hNvw
            exfalso
            simpa [SimpleGraph.subgraphIncidenceVector, hNe, heM] using heq.symm
        simpa [e] using (SimpleGraph.Subgraph.mem_edgeSet.1 hMe)
    exact hbot_not_cycleOrPath (by simpa [hspan] using hcycleOrPath)

end FinitePart_1

section FinitePart_2

/-- The incidence vectors of the matchings of `G` with exactly `k` edges. -/
def cardinalityKMatchingIncidenceSet (k : ℕ) : Set (G.edgeSet → ℝ) :=
  {x | ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = k ∧ x = G.subgraphIncidenceVector ℝ M}

/-- Membership in `cardinalityKMatchingIncidenceSet G k` means being the incidence vector of a
matching of `G` with cardinality `k`. -/
lemma mem_cardinalityKMatchingIncidenceSet_iff {k : ℕ} {x : G.edgeSet → ℝ} :
    x ∈ cardinalityKMatchingIncidenceSet G k ↔
      ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = k ∧ x = G.subgraphIncidenceVector ℝ M := by
  rfl

/-- Exercise 4.27 (2). The `k`-matching slice of the matching polytope is the convex hull of the
incidence vectors of the matchings with exactly `k` edges. -/
theorem matchingPolytope_inter_cardinality_hyperplane_eq_convexHull
    [Fintype V]
    (k : ℕ) (hk_pos : 1 ≤ k) (hk_le_card : k ≤ Fintype.card V) :
    G.matchingPolytope ∩ {x : G.edgeSet → ℝ | ∑ e, x e = (k : ℝ)} =
      convexHull ℝ (cardinalityKMatchingIncidenceSet G k) := by
  let _ := hk_pos
  let _ := hk_le_card
  admit

end FinitePart_2

end Exercise_4_27
