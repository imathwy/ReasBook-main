import Integer.Chapters.Chap04.section_4_5.ch4_sec4_5_theorem_4_25

-- This file reuses the Chapter 4.25 graph-coordinate owners
-- `SimpleGraph.subgraphIncidenceVector` and `SimpleGraph.inducedEdgeFinset`,
-- and restores the cut-edge notation locally for the Proposition 8.9 proof.

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace SimpleGraph

/-- Helper for Proposition 8.9: the cut edges `δ(S)` in the ambient edge coordinates of `G`. -/
def cutEdgeFinset {V : Type*} (G : SimpleGraph V) [Fintype V] (S : Set V) : Finset G.edgeSet :=
  Finset.univ.filter fun e ↦ ∃ u ∈ S, ∃ v ∉ S, s(u, v) = (e : Sym2 V)

/-- Helper for Proposition 8.9: the cut-edge notation on ambient graph coordinates. -/
notation "δ[" G "] " S:arg => cutEdgeFinset G S

/-- Helper for Proposition 8.9: the induced-edge notation on ambient graph coordinates. -/
notation "E[" G "] " U:arg => SimpleGraph.inducedEdgeFinset G U

/-- Helper for Proposition 8.9: an ambient edge-coordinate belongs to `δ[G] S` exactly when one
endpoint lies in `S` and the other lies outside `S`. -/
theorem mem_cutEdgeFinset_iff {V : Type*} {G : SimpleGraph V} [Fintype V] {S : Set V}
    {e : G.edgeSet} :
    e ∈ δ[G] S ↔ ∃ u ∈ S, ∃ v ∉ S, s(u, v) = (e : Sym2 V) := by
  simp [cutEdgeFinset]

section Proposition_8_9

variable {V : Type*} [Fintype V]
variable {G : SimpleGraph V}

namespace Subgraph

section

variable [DecidableRel G.Adj]

/-- A spanning subgraph of `G` is a 1-tree with distinguished root `root` when the root has degree
`2` and deleting the root leaves a tree. -/
def IsOneTree (H : G.Subgraph) (root : V) : Prop :=
  H.IsSpanning ∧
    H.degree root = 2 ∧
      (H.deleteVerts ({root} : Set V)).coe.IsTree

end

/-- A subgraph is a 1-tree with distinguished root `root` exactly when it is spanning, the root
has degree `2`, and deleting the root leaves a tree. -/
theorem isOneTree_iff {H : G.Subgraph} {root : V} :
    H.IsOneTree root ↔
      H.IsSpanning ∧
        H.degree root = 2 ∧
          (H.deleteVerts ({root} : Set V)).coe.IsTree :=
  Iff.rfl

/-- A 1-tree is spanning. -/
theorem IsOneTree.isSpanning {H : G.Subgraph} {root : V} (hH : H.IsOneTree root) :
    H.IsSpanning :=
  hH.1

/-- In a 1-tree the distinguished root has degree `2`. -/
theorem IsOneTree.degree_root_eq_two {H : G.Subgraph} {root : V} (hH : H.IsOneTree root) :
    H.degree root = 2 :=
  hH.2.1

/-- Deleting the distinguished root from a 1-tree leaves a tree. -/
theorem IsOneTree.deleteVerts_singleton_coe_isTree
    {H : G.Subgraph} {root : V} (hH : H.IsOneTree root) :
    (H.deleteVerts ({root} : Set V)).coe.IsTree :=
  hH.2.2

end Subgraph

section

variable [DecidableRel G.Adj]
variable (G : SimpleGraph V) (root : V)

/-- The incidence vectors of the 1-trees of `G` with distinguished root `root`. -/
def oneTreeVertices (G : SimpleGraph V) (root : V) : Set (G.edgeSet → ℝ) :=
  {x | ∃ H : G.Subgraph, H.IsOneTree root ∧ x = G.subgraphIncidenceVector ℝ H}

/-- A vector belongs to `G.oneTreeVertices root` exactly when it is the incidence vector of a
1-tree of `G` with distinguished root `root`. -/
theorem mem_oneTreeVertices_iff
    (G : SimpleGraph V)
    (root : V)
    {x : G.edgeSet → ℝ} :
    x ∈ G.oneTreeVertices root ↔
      ∃ H : G.Subgraph, H.IsOneTree root ∧ x = G.subgraphIncidenceVector ℝ H :=
  Iff.rfl

/-- The incidence vector of a 1-tree belongs to `G.oneTreeVertices root`. -/
theorem subgraphIncidenceVector_mem_oneTreeVertices
    {H : G.Subgraph}
    (hH : H.IsOneTree root) :
    G.subgraphIncidenceVector ℝ H ∈ G.oneTreeVertices root :=
  (G.mem_oneTreeVertices_iff root).2 ⟨H, hH, rfl⟩

/-- The 1-tree polytope of `G` with distinguished root `root`, defined as the convex hull of the
incidence vectors of the 1-trees of `G`. -/
def oneTreePolytope (G : SimpleGraph V) (root : V) : Set (G.edgeSet → ℝ) :=
  convexHull ℝ (G.oneTreeVertices root)

/-- The 1-tree polytope is the convex hull of the 1-tree incidence vectors. -/
theorem oneTreePolytope_eq_convexHull :
    G.oneTreePolytope root = convexHull ℝ (G.oneTreeVertices root) :=
  rfl

/-- The linear relaxation of the textbook 1-tree system `(8.7)`: box constraints, the root-degree
equation, the total-edge equation, and all subtour inequalities on subsets avoiding the root. -/
def oneTreeLinearRelaxation (G : SimpleGraph V) (root : V) : Set (G.edgeSet → ℝ) :=
  {x | (∀ e, 0 ≤ x e ∧ x e ≤ 1) ∧
      (δ[G] ({root} : Set V)).sum x = (2 : ℝ) ∧
      (∑ e, x e) = (Fintype.card V : ℝ) ∧
      ∀ S : Finset V, S.Nonempty → root ∉ S →
        (E[G] (S : Set V)).sum x ≤ (S.card - 1 : ℝ)}

/-- Membership in `G.oneTreeLinearRelaxation root` is exactly the conjunction of the box
constraints, the root-degree equation, the total-edge equation, and the subtour inequalities on
subsets that avoid the distinguished root. -/
theorem mem_oneTreeLinearRelaxation_iff
    (G : SimpleGraph V)
    (root : V)
    {x : G.edgeSet → ℝ} :
    x ∈ G.oneTreeLinearRelaxation root ↔
      (∀ e, 0 ≤ x e ∧ x e ≤ 1) ∧
      (δ[G] ({root} : Set V)).sum x = (2 : ℝ) ∧
      (∑ e, x e) = (Fintype.card V : ℝ) ∧
      ∀ S : Finset V, S.Nonempty → root ∉ S →
        (E[G] (S : Set V)).sum x ≤ (S.card - 1 : ℝ) := Iff.rfl

/-- Helper for Proposition 8.9: an ambient edge lies in the induced deleted-root edge block
exactly when neither endpoint is the distinguished root. -/
private lemma mem_deletedRootInducedEdgeFinset_iff
    (e : G.edgeSet) :
    e ∈ E[G] ({root}ᶜ : Set V) ↔ e.1.out.1 ≠ root ∧ e.1.out.2 ≠ root := by
  -- Rewrite induced-edge membership through the canonical endpoint presentation of `e`.
  have hadj : G.Adj e.1.out.1 e.1.out.2 := by
    have he : s(e.1.out.1, e.1.out.2) ∈ G.edgeSet := by
      simpa [e.1.out_eq] using e.prop
    exact (SimpleGraph.mem_edgeSet (G := G) (v := e.1.out.1) (w := e.1.out.2)).1 he
  rw [mem_inducedEdgeFinset_iff, ← e.1.out_eq, SimpleGraph.Subgraph.mem_edgeSet]
  simp [SimpleGraph.Subgraph.induce, hadj]

/-- Helper for Proposition 8.9: an ambient edge lies in the root cut exactly when one canonical
endpoint is the distinguished root and the other is not. -/
private lemma mem_rootCutEdgeFinset_iff
    (e : G.edgeSet) :
    e ∈ δ[G] ({root} : Set V) ↔
      (e.1.out.1 = root ∧ e.1.out.2 ≠ root) ∨
        (e.1.out.2 = root ∧ e.1.out.1 ≠ root) := by
  constructor
  · intro he
    rcases (mem_cutEdgeFinset_iff (G := G) (S := ({root} : Set V)) (e := e)).1 he with
      ⟨u, hu, v, hv, huv⟩
    -- Normalize the cut-edge witness to the concrete endpoints of `e`.
    rw [← e.1.out_eq] at huv
    rw [Sym2.eq_iff] at huv
    rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨by simpa using hu, by simpa using hv⟩
    · exact Or.inr ⟨by simpa using hu, by simpa using hv⟩
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · exact (mem_cutEdgeFinset_iff (G := G) (S := ({root} : Set V)) (e := e)).2
        ⟨e.1.out.1, by simpa [h₁], e.1.out.2, by simpa [h₂], e.1.out_eq⟩
    · exact (mem_cutEdgeFinset_iff (G := G) (S := ({root} : Set V)) (e := e)).2
        ⟨e.1.out.2, by simpa [h₁], e.1.out.1, by simpa [h₂],
          Sym2.eq_swap.trans e.1.out_eq⟩

/-- Helper for Proposition 8.9: every ambient edge belongs to exactly one of the root-cut and
deleted-root edge blocks. -/
private lemma mem_deletedRootInducedEdgeFinset_iff_not_mem_rootCut
    (e : G.edgeSet) :
    e ∈ E[G] ({root}ᶜ : Set V) ↔ e ∉ δ[G] ({root} : Set V) := by
  -- An edge in a simple graph has two distinct endpoints, so the only alternative to lying in the
  -- root cut is to avoid the root entirely.
  have hadj : G.Adj e.1.out.1 e.1.out.2 := by
    have he : s(e.1.out.1, e.1.out.2) ∈ G.edgeSet := by
      simpa [e.1.out_eq] using e.prop
    exact (SimpleGraph.mem_edgeSet (G := G) (v := e.1.out.1) (w := e.1.out.2)).1 he
  have hneq : e.1.out.1 ≠ e.1.out.2 := G.ne_of_adj hadj
  constructor
  · intro he hcut
    rcases (mem_deletedRootInducedEdgeFinset_iff (G := G) (root := root) e).1 he with ⟨h₁, h₂⟩
    rcases (mem_rootCutEdgeFinset_iff (G := G) (root := root) e).1 hcut with
      (⟨hroot, _⟩ | ⟨hroot, _⟩)
    · exact h₁ hroot
    · exact h₂ hroot
  · intro hnot
    by_cases h₁ : e.1.out.1 = root
    · have h₂ : e.1.out.2 ≠ root := by
        intro h₂
        exact hneq (h₁.trans h₂.symm)
      exact False.elim (hnot ((mem_rootCutEdgeFinset_iff (G := G) (root := root) e).2
        (Or.inl ⟨h₁, h₂⟩)))
    · by_cases h₂ : e.1.out.2 = root
      · exact False.elim (hnot ((mem_rootCutEdgeFinset_iff (G := G) (root := root) e).2
          (Or.inr ⟨h₂, h₁⟩)))
      · exact (mem_deletedRootInducedEdgeFinset_iff (G := G) (root := root) e).2 ⟨h₁, h₂⟩

/-- Helper for Proposition 8.9: on a singleton, cut-edge membership is equivalent to the edge
containing the distinguished root. -/
private lemma mem_rootCutEdgeFinset_iff_mem_root
    (e : G.edgeSet) :
    e ∈ δ[G] ({root} : Set V) ↔ root ∈ (e : Sym2 V) := by
  have hadj : G.Adj e.1.out.1 e.1.out.2 := by
    have he : s(e.1.out.1, e.1.out.2) ∈ G.edgeSet := by
      simpa [e.1.out_eq] using e.prop
    exact (SimpleGraph.mem_edgeSet (G := G) (v := e.1.out.1) (w := e.1.out.2)).1 he
  have hneq : e.1.out.1 ≠ e.1.out.2 := G.ne_of_adj hadj
  constructor
  · intro hcut
    rcases (mem_rootCutEdgeFinset_iff (G := G) (root := root) e).1 hcut with
      (⟨h₁, _⟩ | ⟨h₂, _⟩)
    · rw [← e.1.out_eq]
      exact Sym2.mem_iff.2 (Or.inl h₁.symm)
    · rw [← e.1.out_eq]
      exact Sym2.mem_iff.2 (Or.inr h₂.symm)
  · intro hroot
    rw [← e.1.out_eq] at hroot
    rcases Sym2.mem_iff.1 hroot with h₁ | h₂
    · exact (mem_rootCutEdgeFinset_iff (G := G) (root := root) e).2
        (Or.inl ⟨h₁.symm, by
          intro h₂'
          exact hneq (h₁.symm.trans h₂'.symm)⟩)
    · exact (mem_rootCutEdgeFinset_iff (G := G) (root := root) e).2
        (Or.inr ⟨h₂.symm, by
          intro h₁'
          exact hneq (h₁'.trans h₂)⟩)

/-- Helper for Proposition 8.9: the ambient total edge sum splits into the root-cut block and the
deleted-root block. -/
theorem sumEdges_eq_rootCut_sum_add_deletedRoot_sum
    (x : G.edgeSet → ℝ) :
    (∑ e : G.edgeSet, x e) =
      (δ[G] ({root} : Set V)).sum x + (E[G] ({root}ᶜ : Set V)).sum x := by
  -- Split the universal edge sum by membership in the root cut, then rewrite the complementary
  -- filter as the deleted-root edge block.
  let p : G.edgeSet → Prop :=
    fun e ↦ ∃ u ∈ ({root} : Set V), ∃ v ∉ ({root} : Set V), s(u, v) = (e : Sym2 V)
  have hrootFilter :
      Finset.univ.filter p =
        δ[G] ({root} : Set V) := by
    -- This is the defining filter for the root cut.
    rfl
  have hdeletedFilter :
      Finset.univ.filter (fun e : G.edgeSet ↦ ¬ p e) =
        E[G] ({root}ᶜ : Set V) := by
    -- The complement of the root cut is exactly the deleted-root induced edge block.
    ext e
    simp [p, cutEdgeFinset,
      mem_deletedRootInducedEdgeFinset_iff_not_mem_rootCut (G := G) (root := root) e]
  calc
    (∑ e : G.edgeSet, x e) =
        (Finset.univ.filter p).sum x +
          (Finset.univ.filter (fun e : G.edgeSet ↦ ¬ p e)).sum x := by
            simpa using
              (Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
                (p := p) x).symm
    _ = (δ[G] ({root} : Set V)).sum x +
          (Finset.univ.filter (fun e : G.edgeSet ↦ ¬ p e)).sum x := by
            rw [hrootFilter]
    _ = (δ[G] ({root} : Set V)).sum x + (E[G] ({root}ᶜ : Set V)).sum x := by
            rw [hdeletedFilter]

/-- Helper for Proposition 8.9: the defining inequalities of `G.oneTreeLinearRelaxation root` are
preserved under convex combinations. -/
theorem convex_oneTreeLinearRelaxation :
    Convex ℝ (G.oneTreeLinearRelaxation root) := by
  intro x hx y hy a b ha hb hab
  rcases (G.mem_oneTreeLinearRelaxation_iff root).1 hx with
    ⟨hx_box, hx_root, hx_total, hx_subtour⟩
  rcases (G.mem_oneTreeLinearRelaxation_iff root).1 hy with
    ⟨hy_box, hy_root, hy_total, hy_subtour⟩
  refine (G.mem_oneTreeLinearRelaxation_iff root).2 ?_
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e
    rcases hx_box e with ⟨hx_nonneg, hx_le_one⟩
    rcases hy_box e with ⟨hy_nonneg, hy_le_one⟩
    constructor
    · -- Coordinatewise lower bounds are preserved by nonnegative affine combinations.
      exact add_nonneg (mul_nonneg ha hx_nonneg) (mul_nonneg hb hy_nonneg)
    · -- Coordinatewise upper bounds use the normalization `a + b = 1`.
      have hxScaled : a * x e ≤ a * 1 := mul_le_mul_of_nonneg_left hx_le_one ha
      have hyScaled : b * y e ≤ b * 1 := mul_le_mul_of_nonneg_left hy_le_one hb
      have hupper : a * x e + b * y e ≤ a + b := by
        simpa using add_le_add hxScaled hyScaled
      calc
        (a • x + b • y) e = a * x e + b * y e := by
          simp [Pi.add_apply, Pi.smul_apply]
        _ ≤ a + b := hupper
        _ = (1 : ℝ) := hab
  · -- The root-degree equation is affine-linear in the edge coordinates.
    calc
      (δ[G] ({root} : Set V)).sum (a • x + b • y)
          = a * (δ[G] ({root} : Set V)).sum x +
              b * (δ[G] ({root} : Set V)).sum y := by
            simp [Pi.add_apply, Pi.smul_apply, Finset.mul_sum, Finset.sum_add_distrib]
      _ = a * 2 + b * 2 := by rw [hx_root, hy_root]
      _ = (2 : ℝ) := by nlinarith
  · -- The total-edge equation is affine-linear for the same reason.
    calc
      (∑ e, (a • x + b • y) e) = a * (∑ e, x e) + b * (∑ e, y e) := by
        simp [Pi.add_apply, Pi.smul_apply, Finset.mul_sum, Finset.sum_add_distrib]
      _ = a * (Fintype.card V : ℝ) + b * (Fintype.card V : ℝ) := by
        rw [hx_total, hy_total]
      _ = (Fintype.card V : ℝ) := by nlinarith
  · intro S hS hrootS
    have hxS := hx_subtour S hS hrootS
    have hyS := hy_subtour S hS hrootS
    -- Each deleted-root subtour inequality is preserved coordinatewise under the same weights.
    calc
      (E[G] (S : Set V)).sum (a • x + b • y)
          = a * (E[G] (S : Set V)).sum x +
              b * (E[G] (S : Set V)).sum y := by
            simp [Pi.add_apply, Pi.smul_apply, Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ a * (S.card - 1 : ℝ) + b * (S.card - 1 : ℝ) := by
            gcongr
      _ = (S.card - 1 : ℝ) := by
            nlinarith

/-- Helper for Proposition 8.9: the deleted-root subgraph has the same native edge set as the
subgraph induced on the complement of `{root}`. -/
private theorem deleteVerts_edgeSet_eq_induce_compl_singleton
    {H : G.Subgraph} :
    (H.deleteVerts ({root} : Set V)).edgeSet = (H.induce ({root}ᶜ : Set V)).edgeSet := by
  -- Both owners keep exactly the edges of `H` whose endpoints avoid the distinguished root.
  ext e
  induction e using Sym2.ind with
  | h u v =>
      rw [SimpleGraph.Subgraph.mem_edgeSet, SimpleGraph.Subgraph.mem_edgeSet]
      rw [SimpleGraph.Subgraph.deleteVerts_adj]
      constructor
      · rintro ⟨huH, hu, hvH, hv, huv⟩
        exact ⟨hu, hv, huv⟩
      · rintro ⟨hu, hv, huv⟩
        exact ⟨huv.fst_mem, hu, huv.snd_mem, hv, huv⟩

/-- Helper for Proposition 8.9: summing the ambient incidence vector on deleted-root coordinates
counts the edges of `H.deleteVerts {root}`. -/
private theorem deletedRootInduced_sum_eq_card_deleteVerts
    {H : G.Subgraph} :
    (E[G] ({root}ᶜ : Set V)).sum (G.subgraphIncidenceVector ℝ H) =
      Fintype.card ((H.deleteVerts ({root} : Set V)).edgeSet) := by
  classical
  let S : Finset V := Finset.univ.erase root
  have hS : (S : Set V) = ({root}ᶜ : Set V) := by
    -- The finite owner `erase root` is exactly the complement of the singleton.
    ext v
    simp [S]
  -- Rewrite the deleted-root block through the canonical induced-edge owner from Chapter 4.25.
  calc
    (E[G] ({root}ᶜ : Set V)).sum (G.subgraphIncidenceVector ℝ H)
        = (E[G] (S : Set V)).sum (G.subgraphIncidenceVector ℝ H) := by
            rw [← hS]
    _ = Fintype.card ((H.induce (S : Set V)).edgeSet) := by
          simpa using induced_incidence_sum_eq_card_induced_edges G H S
    _ = Fintype.card ((H.deleteVerts ({root} : Set V)).edgeSet) := by
          rw [deleteVerts_edgeSet_eq_induce_compl_singleton (G := G) (root := root) (H := H),
            hS]

/-- Helper for Proposition 8.9: summing the root-cut coordinates of an incidence vector counts
the edges of `H` incident to the distinguished root. -/
private theorem rootCutIncidenceSum_eq_degree
    {H : G.Subgraph} :
    (δ[G] ({root} : Set V)).sum (G.subgraphIncidenceVector ℝ H) = H.degree root := by
  classical
  let rootCutInH : Finset G.edgeSet :=
    (δ[G] ({root} : Set V)).filter fun e ↦ e.1 ∈ H.edgeSet
  have hsum :
      (δ[G] ({root} : Set V)).sum (G.subgraphIncidenceVector ℝ H) =
        (rootCutInH.card : ℝ) := by
    -- Expand the indicator and keep only the root-cut edges that actually belong to `H`.
    calc
      (δ[G] ({root} : Set V)).sum (G.subgraphIncidenceVector ℝ H) =
          rootCutInH.sum (fun _ ↦ (1 : ℝ)) := by
            simpa [rootCutInH, SimpleGraph.subgraphIncidenceVector] using
              (Finset.sum_filter
                (s := δ[G] ({root} : Set V))
                (p := fun e : G.edgeSet ↦ e.1 ∈ H.edgeSet)
                (f := fun _ ↦ (1 : ℝ))).symm
      _ = (rootCutInH.card : ℝ) := by
            simp
  let edgeEmbedding : G.edgeSet ↪ Sym2 V :=
    ⟨fun e ↦ (e : Sym2 V), Subtype.val_injective⟩
  have hmap :
      Finset.map edgeEmbedding rootCutInH = H.spanningCoe.incidenceFinset root := by
    -- After forgetting the ambient-edge subtype, the filtered root-cut edges are exactly the
    -- incident edges of `root` in the spanning coercion of `H`.
    ext e
    constructor
    · intro he
      rcases Finset.mem_map.1 he with ⟨eG, heG, rfl⟩
      rcases Finset.mem_filter.1 heG with ⟨hcut, hedgeH⟩
      rw [SimpleGraph.mem_incidenceFinset]
      exact ⟨by simpa using hedgeH,
        (mem_rootCutEdgeFinset_iff_mem_root (G := G) (root := root) eG).1 hcut⟩
    · intro he
      rw [SimpleGraph.mem_incidenceFinset] at he
      rcases he with ⟨hedgeH, hroot⟩
      let eG : G.edgeSet := ⟨e, H.edgeSet_subset hedgeH⟩
      have hcut : eG ∈ δ[G] ({root} : Set V) := by
        exact (mem_rootCutEdgeFinset_iff_mem_root (G := G) (root := root) eG).2 (by simpa using hroot)
      refine Finset.mem_map.2 ⟨eG, ?_, rfl⟩
      exact Finset.mem_filter.2 ⟨hcut, by simpa using hedgeH⟩
  have hcardNat : rootCutInH.card = H.degree root := by
    -- Convert the filtered cardinality into the incidence-finset cardinal of `H.spanningCoe`.
    calc
      rootCutInH.card = (H.spanningCoe.incidenceFinset root).card := by
        simpa using congrArg Finset.card hmap
      _ = H.spanningCoe.degree root := by
        simpa using H.spanningCoe.card_incidenceFinset_eq_degree root
      _ = H.degree root := by
        simpa using (Subgraph.degree_spanningCoe (G' := H) root)
  calc
    (δ[G] ({root} : Set V)).sum (G.subgraphIncidenceVector ℝ H) = (rootCutInH.card : ℝ) := hsum
    _ = H.degree root := by
          exact congrArg (fun n : ℕ ↦ (n : ℝ)) hcardNat

/-- Helper for Proposition 8.9: a 1-tree contributes exactly `|V| - 2` deleted-root edges in the
ambient coordinates. -/
theorem deletedRootIncidenceSum_eq_card_sub_two_of_isOneTree
    {H : G.Subgraph}
    (hH : H.IsOneTree root) :
    (E[G] ({root}ᶜ : Set V)).sum (G.subgraphIncidenceVector ℝ H) =
      (Fintype.card V - 2 : ℝ) := by
  classical
  have hTree := hH.deleteVerts_singleton_coe_isTree
  have hcoeEdgeCard :
      ((H.deleteVerts ({root} : Set V)).coe.edgeSet).ncard =
        ((H.deleteVerts ({root} : Set V)).edgeSet).ncard := by
    -- Forgetting the deleted-root vertex subtype does not change the edge count.
    calc
      ((H.deleteVerts ({root} : Set V)).coe.edgeSet).ncard =
          (Sym2.map ((↑) : (H.deleteVerts ({root} : Set V)).verts → V) ''
            (H.deleteVerts ({root} : Set V)).coe.edgeSet).ncard := by
              symm
              exact Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)
      _ = ((H.deleteVerts ({root} : Set V)).edgeSet).ncard := by
            rw [(H.deleteVerts ({root} : Set V)).image_coe_edgeSet_coe]
  have htreeCard :
      ((H.deleteVerts ({root} : Set V)).coe.edgeSet).ncard + 1 =
        ((H.deleteVerts ({root} : Set V)).verts).ncard := by
    -- A finite tree has one fewer edge than vertices.
    have htreeCardNat := (SimpleGraph.isTree_iff_connected_and_card.mp hTree).2
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq] at htreeCardNat
    exact htreeCardNat
  have hvertsCard :
      ((H.deleteVerts ({root} : Set V)).verts).ncard = Fintype.card V - 1 := by
    -- Deleting the root from a spanning subgraph leaves exactly the complement subtype `{v ≠ root}`.
    have hvertsEq :
        (H.deleteVerts ({root} : Set V)).verts = {v : V | v ≠ root} := by
      ext v
      simp [hH.isSpanning v]
    rw [hvertsEq]
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
    exact Set.card_ne_eq (α := V) root
  have hdeletedCardNat :
      ((H.deleteVerts ({root} : Set V)).edgeSet).ncard = Fintype.card V - 2 := by
    omega
  have hcardV_ge_two : 2 ≤ Fintype.card V := by
    -- The distinguished root has degree `2`, so the ambient graph has at least two other vertices.
    have hdegLt : H.spanningCoe.degree root < Fintype.card V := by
      simpa using (SimpleGraph.degree_lt_card_verts (G := H.spanningCoe) root)
    have hdegEq : H.spanningCoe.degree root = 2 := by
      rw [Subgraph.degree_spanningCoe]
      exact hH.degree_root_eq_two
    omega
  -- Rewrite the deleted-root block as the edge count of `H.deleteVerts {root}` and then
  -- specialize the tree cardinality.
  calc
    (E[G] ({root}ᶜ : Set V)).sum (G.subgraphIncidenceVector ℝ H) =
        Fintype.card ((H.deleteVerts ({root} : Set V)).edgeSet) := by
          exact deletedRootInduced_sum_eq_card_deleteVerts (G := G) (root := root) (H := H)
    _ = (((H.deleteVerts ({root} : Set V)).edgeSet).ncard : ℝ) := by
          rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
    _ = ((Fintype.card V - 2 : ℕ) : ℝ) := by
          exact congrArg (fun n : ℕ ↦ (n : ℝ)) hdeletedCardNat
    _ = (Fintype.card V : ℝ) - 2 := by
          rw [Nat.cast_sub hcardV_ge_two]
          norm_num

/-- Helper for Proposition 8.9: the root-cut coordinates of a 1-tree incidence vector sum to `2`.
-/
theorem rootCutIncidenceSum_eq_two_of_isOneTree
    {H : G.Subgraph}
    (hH : H.IsOneTree root) :
    (δ[G] ({root} : Set V)).sum (G.subgraphIncidenceVector ℝ H) = (2 : ℝ) := by
  -- Reinterpret the root-cut count as the root degree and use the defining `1`-tree axiom.
  calc
    (δ[G] ({root} : Set V)).sum (G.subgraphIncidenceVector ℝ H) = H.degree root := by
      exact rootCutIncidenceSum_eq_degree (G := G) (root := root) (H := H)
    _ = (2 : ℝ) := by
          exact congrArg (fun n : ℕ ↦ (n : ℝ)) hH.degree_root_eq_two

/-- Helper for Proposition 8.9: a 1-tree incidence vector has total edge sum `|V|`. -/
theorem subgraphIncidenceVector_total_sum_of_isOneTree
    {H : G.Subgraph}
    (hH : H.IsOneTree root) :
    (∑ e : G.edgeSet, G.subgraphIncidenceVector ℝ H e) = (Fintype.card V : ℝ) := by
  -- Split the ambient edge sum into the root-cut and deleted-root blocks, then evaluate each
  -- block by the dedicated one-tree counting lemmas above.
  calc
    (∑ e : G.edgeSet, G.subgraphIncidenceVector ℝ H e) =
        (δ[G] ({root} : Set V)).sum (G.subgraphIncidenceVector ℝ H) +
          (E[G] ({root}ᶜ : Set V)).sum (G.subgraphIncidenceVector ℝ H) := by
            rw [sumEdges_eq_rootCut_sum_add_deletedRoot_sum (G := G) (root := root)
              (x := G.subgraphIncidenceVector ℝ H)]
    _ = (2 : ℝ) + (Fintype.card V - 2 : ℝ) := by
          rw [rootCutIncidenceSum_eq_two_of_isOneTree (G := G) (root := root) hH,
            deletedRootIncidenceSum_eq_card_sub_two_of_isOneTree (G := G) (root := root) hH]
    _ = (Fintype.card V : ℝ) := by
          ring

/-- Helper for Proposition 8.9: forgetting the ambient subtype on a subgraph preserves the edge
cardinality. -/
private theorem card_coe_edgeSet_eq_card_edgeSet
    {W : Type*} {K : SimpleGraph W} [Fintype W] [DecidableRel K.Adj] (L : K.Subgraph) :
    Fintype.card L.coe.edgeSet = Fintype.card L.edgeSet := by
  -- The native edge set is the image of the subtype-owner edge set under the canonical vertex
  -- inclusion, so both have the same finite cardinality.
  calc
    Fintype.card L.coe.edgeSet = Nat.card L.coe.edgeSet := by
      rw [Nat.card_eq_fintype_card]
    _ = Nat.card L.edgeSet := by
      rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
      calc
        L.coe.edgeSet.ncard =
            (Sym2.map ((↑) : L.verts → W) '' L.coe.edgeSet).ncard := by
              symm
              exact Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)
        _ = L.edgeSet.ncard := by
              rw [L.image_coe_edgeSet_coe]
    _ = Fintype.card L.edgeSet := by
      rw [Nat.card_eq_fintype_card]

/-- Helper for Proposition 8.9: forgetting the ambient subtype on a subgraph preserves the edge
cardinality at the `Nat.card` level, which avoids instance-sensitive rewrites later. -/
private theorem natCard_coe_edgeSet_eq_natCard_edgeSet
    {W : Type*} {K : SimpleGraph W} (L : K.Subgraph) :
    Nat.card L.coe.edgeSet = Nat.card L.edgeSet := by
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  calc
    L.coe.edgeSet.ncard =
        (Sym2.map ((↑) : L.verts → W) '' L.coe.edgeSet).ncard := by
          symm
          exact Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)
    _ = L.edgeSet.ncard := by
          rw [L.image_coe_edgeSet_coe]

/-- Helper for Proposition 8.9: a finite acyclic graph has at most one fewer edge than vertices. -/
private theorem isAcyclic_card_edgeSet_le_card_verts_sub_one
    {W : Type*} [Fintype W] {K : SimpleGraph W} (hK : K.IsAcyclic) :
    Fintype.card K.edgeSet ≤ Fintype.card W - 1 := by
  classical
  by_cases hW : IsEmpty W
  · let _ : IsEmpty W := hW
    simp
  · let _ : Nonempty W := not_isEmpty_iff.mp hW
    obtain ⟨T, hTK, -, hT⟩ :=
      SimpleGraph.Connected.exists_isTree_le_of_le_of_isAcyclic
        (G := (⊤ : SimpleGraph W)) (H := K) SimpleGraph.connected_top le_top hK
    have hEdgeLe : Fintype.card K.edgeSet ≤ Fintype.card T.edgeSet := by
      rw [← K.edgeFinset_card, ← T.edgeFinset_card]
      exact Finset.card_mono (SimpleGraph.edgeFinset_mono hTK)
    have hTreeCard : Fintype.card T.edgeSet + 1 = Fintype.card W := by
      rw [SimpleGraph.card_edgeSet]
      exact hT.card_edgeFinset
    omega

/-- Helper for Proposition 8.9: if a vertex subset avoids the distinguished root, then inducing
after deleting the root has the same ambient edge set as inducing directly. -/
private theorem induce_edgeSet_eq_deleteVerts_induce_edgeSet_of_root_not_mem
    {H : G.Subgraph}
    (hHSpanning : H.IsSpanning)
    {S : Finset V}
    (hrootS : root ∉ S) :
    (H.induce (S : Set V)).edgeSet =
      ((H.deleteVerts ({root} : Set V)).induce (S : Set V)).edgeSet := by
  ext e
  induction e using Sym2.ind with
  | h u v =>
      rw [SimpleGraph.Subgraph.mem_edgeSet, SimpleGraph.Subgraph.mem_edgeSet]
      rw [SimpleGraph.Subgraph.induce_adj, SimpleGraph.Subgraph.induce_adj]
      rw [SimpleGraph.Subgraph.deleteVerts_adj]
      constructor
      · rintro ⟨huS, hvS, huv⟩
        have huNotRoot : u ∉ ({root} : Set V) := by
          simp only [Set.mem_singleton_iff]
          intro huRoot
          exact hrootS (by simpa [huRoot] using huS)
        have hvNotRoot : v ∉ ({root} : Set V) := by
          simp only [Set.mem_singleton_iff]
          intro hvRoot
          exact hrootS (by simpa [hvRoot] using hvS)
        exact ⟨huS, hvS, hHSpanning u, huNotRoot, hHSpanning v, hvNotRoot, huv⟩
      · rintro ⟨huS, hvS, _, _, _, _, huv⟩
        exact ⟨huS, hvS, huv⟩

/-- Helper for Proposition 8.9: on any root-free vertex subset, a 1-tree induces at most
`|S| - 1` ambient edges. -/
private theorem deletedRootInducedEdgeCard_eq
    {H : G.Subgraph}
    (hHSpanning : H.IsSpanning)
    {S : Finset V}
    (hrootS : root ∉ S) :
    Fintype.card ((H.induce (S : Set V)).edgeSet) =
      Fintype.card ((((H.deleteVerts ({root} : Set V)).coe).induce
        {v : (H.deleteVerts ({root} : Set V)).verts | (v : V) ∈ (S : Set V)}).edgeSet) := by
  classical
  let T : G.Subgraph := H.deleteVerts ({root} : Set V)
  let U : Set T.verts := {v | (v : V) ∈ (S : Set V)}
  have hsubset : (S : Set V) ⊆ T.verts := by
    intro v hvS
    refine ⟨hHSpanning v, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro hvRoot
    exact hrootS (by simpa [hvRoot] using hvS)
  have hIso :
      (T.induce (S : Set V)).coe ≃g T.coe.induce U :=
    SimpleGraph.Subgraph.coeInduceIso (G' := T) (s := (S : Set V)) hsubset
  have hInducedCard :
      Fintype.card ((H.induce (S : Set V)).edgeSet) =
        Fintype.card ((T.coe.induce U).edgeSet) := by
    -- Route correction: rewrite the ambient induced graph through the deleted-root owner once,
    -- then compare edge counts through `Subgraph.coeInduceIso` instead of further owner transport.
    rw [induce_edgeSet_eq_deleteVerts_induce_edgeSet_of_root_not_mem
      (G := G) (root := root) hHSpanning hrootS]
    have hIsoCard :
        Fintype.card ((T.induce (S : Set V)).coe.edgeSet) =
          Fintype.card ((T.coe.induce U).edgeSet) := by
      rw [SimpleGraph.card_edgeSet, SimpleGraph.card_edgeSet]
      simpa using hIso.card_edgeFinset_eq
    calc
      Fintype.card ((T.induce (S : Set V)).edgeSet) =
          Fintype.card ((T.induce (S : Set V)).coe.edgeSet) := by
            rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
            exact (natCard_coe_edgeSet_eq_natCard_edgeSet (L := T.induce (S : Set V))).symm
      _ = Fintype.card ((T.coe.induce U).edgeSet) := hIsoCard
  simpa [T, U] using hInducedCard

/-- Helper for Proposition 8.9: viewing a root-free ambient vertex subset inside the deleted-root
owner does not change its cardinality. -/
private theorem deletedRootVertexSet_card_eq
    {H : G.Subgraph}
    (hHSpanning : H.IsSpanning)
    {S : Finset V}
    (hrootS : root ∉ S) :
    Fintype.card {v : (H.deleteVerts ({root} : Set V)).verts // (v : V) ∈ (S : Set V)} = S.card := by
  classical
  let T : G.Subgraph := H.deleteVerts ({root} : Set V)
  have hsubset : (S : Set V) ⊆ T.verts := by
    intro v hvS
    refine ⟨hHSpanning v, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro hvRoot
    exact hrootS (by simpa [hvRoot] using hvS)
  let U : Set T.verts := {v | (v : V) ∈ (S : Set V)}
  have hUCard : Fintype.card U = S.card := by
    let e : ↥U ≃ {v : V // v ∈ (S : Set V)} := {
      toFun := fun v ↦ ⟨v.1.1, v.2⟩
      invFun := fun v ↦ ⟨⟨v.1, hsubset v.2⟩, v.2⟩
      left_inv := by
        intro v
        cases v
        rfl
      right_inv := by
        intro v
        cases v
        rfl }
    calc
      Fintype.card U = Fintype.card {v : V // v ∈ (S : Set V)} := Fintype.card_congr e
      _ = S.card := by
            simpa using (Fintype.card_subtype fun v : V ↦ v ∈ (S : Set V))
  simpa [T, U] using hUCard

/-- Helper for Proposition 8.9: the deleted-root induced owner satisfies the forest edge bound on
its native subtype vertex set. -/
private theorem deletedRootOwnerInducedCard_le_deletedRootVertexCard_sub_one
    {H : G.Subgraph}
    (hH : H.IsOneTree root)
    {S : Finset V} :
    Fintype.card ((((H.deleteVerts ({root} : Set V)).coe).induce
      {v : (H.deleteVerts ({root} : Set V)).verts | (v : V) ∈ (S : Set V)}).edgeSet) ≤
        Fintype.card {v : (H.deleteVerts ({root} : Set V)).verts // (v : V) ∈ (S : Set V)} - 1 := by
  let U : Set (H.deleteVerts ({root} : Set V)).verts := {v | (v : V) ∈ (S : Set V)}
  have hAcyclic :
      (((H.deleteVerts ({root} : Set V)).coe).induce U).IsAcyclic := by
    -- The deleted-root owner remains acyclic after inducing on the root-free subtype set.
    exact hH.deleteVerts_singleton_coe_isTree.isAcyclic.induce U
  -- Apply the generic forest bound in the owner normal form, keeping the `S.card` rewrite out of
  -- this theorem.
  simpa [U] using
    isAcyclic_card_edgeSet_le_card_verts_sub_one
      (K := (((H.deleteVerts ({root} : Set V)).coe).induce U)) hAcyclic

/-- Helper for Proposition 8.9: the deleted-root induced owner satisfies the forest edge bound on
every root-free vertex subset. -/
private theorem deletedRootOwnerInducedCard_le_card_sub_one
    {H : G.Subgraph}
    (hH : H.IsOneTree root)
    {S : Finset V}
    (hrootS : root ∉ S) :
    Fintype.card ((((H.deleteVerts ({root} : Set V)).coe).induce
      {v : (H.deleteVerts ({root} : Set V)).verts | (v : V) ∈ (S : Set V)}).edgeSet) ≤
        S.card - 1 := by
  -- Route correction: first prove the forest bound in the deleted-root owner's native subtype
  -- cardinality, then rewrite that cardinality once to `S.card`.
  calc
    Fintype.card ((((H.deleteVerts ({root} : Set V)).coe).induce
      {v : (H.deleteVerts ({root} : Set V)).verts | (v : V) ∈ (S : Set V)}).edgeSet) ≤
        Fintype.card {v : (H.deleteVerts ({root} : Set V)).verts // (v : V) ∈ (S : Set V)} - 1 := by
          exact deletedRootOwnerInducedCard_le_deletedRootVertexCard_sub_one
            (G := G) (root := root) hH
    _ = S.card - 1 := by
          rw [deletedRootVertexSet_card_eq (G := G) (root := root) hH.isSpanning hrootS]

/-- Helper for Proposition 8.9: on any root-free vertex subset, a 1-tree induces at most
`|S| - 1` ambient edges. -/
theorem deletedRootInduceCard_le_card_sub_one_of_isOneTree
    {H : G.Subgraph}
    (hH : H.IsOneTree root)
    (S : Finset V)
    (hrootS : root ∉ S) :
    Fintype.card ((H.induce (S : Set V)).edgeSet) ≤ S.card - 1 := by
  -- Transport the ambient induced subgraph to the deleted-root owner, apply the forest bound
  -- there, and transport the edge count back.
  calc
    Fintype.card ((H.induce (S : Set V)).edgeSet) =
        Fintype.card ((((H.deleteVerts ({root} : Set V)).coe).induce
          {v : (H.deleteVerts ({root} : Set V)).verts | (v : V) ∈ (S : Set V)}).edgeSet) := by
            exact deletedRootInducedEdgeCard_eq (G := G) (root := root) hH.isSpanning hrootS
    _ ≤ S.card - 1 := by
          exact deletedRootOwnerInducedCard_le_card_sub_one
            (G := G) (root := root) hH hrootS

/-- Helper for Proposition 8.9: every 1-tree incidence vector satisfies the linear relaxation. -/
theorem subgraphIncidenceVector_mem_oneTreeLinearRelaxation
    {H : G.Subgraph}
    (hH : H.IsOneTree root) :
    G.subgraphIncidenceVector ℝ H ∈ G.oneTreeLinearRelaxation root := by
  refine (G.mem_oneTreeLinearRelaxation_iff root).2 ?_
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e
    constructor
    · -- Incidence vectors are coordinatewise nonnegative.
      exact subgraphIncidenceVector_nonneg G H e
    · -- Each incidence coordinate is an indicator, so it is at most `1`.
      by_cases he : e.1 ∈ H.edgeSet
      · simp [SimpleGraph.subgraphIncidenceVector, he]
      · simp [SimpleGraph.subgraphIncidenceVector, he]
  · -- The root-cut block of a 1-tree incidence vector sums to `2`.
    exact rootCutIncidenceSum_eq_two_of_isOneTree (G := G) (root := root) hH
  · -- The total edge sum of a 1-tree incidence vector is `|V|`.
    exact subgraphIncidenceVector_total_sum_of_isOneTree (G := G) (root := root) hH
  · intro S hS hrootS
    -- Rewrite the subtour inequality as an induced-edge count and apply the deleted-root tree
    -- bound proved above.
    calc
      (E[G] (S : Set V)).sum (G.subgraphIncidenceVector ℝ H) =
          Fintype.card ((H.induce (S : Set V)).edgeSet) := by
            simpa using induced_incidence_sum_eq_card_induced_edges G H S
      _ ≤ (S.card - 1 : ℝ) := by
            have hnat :
                Fintype.card ((H.induce (S : Set V)).edgeSet) ≤ S.card - 1 :=
              deletedRootInduceCard_le_card_sub_one_of_isOneTree
                (G := G) (root := root) hH S hrootS
            have hnat_add : Fintype.card ((H.induce (S : Set V)).edgeSet) + 1 ≤ S.card := by
              have hlt : Fintype.card ((H.induce (S : Set V)).edgeSet) < S.card := by
                exact lt_of_le_of_lt hnat
                  (Nat.sub_lt (Finset.card_pos.mpr hS) (by decide))
              exact Nat.succ_le_of_lt hlt
            have hreal_add : (Fintype.card ((H.induce (S : Set V)).edgeSet) : ℝ) + 1 ≤ S.card := by
              exact_mod_cast hnat_add
            nlinarith

/-- Proposition 8.9. The 1-tree polytope of `G` is described by the linear relaxation of the
constraints in `(8.7)`, with `root` representing the distinguished textbook vertex `1`. -/
theorem oneTreePolytope_eq_oneTreeLinearRelaxation
    (G : SimpleGraph V)
    (root : V) :
    G.oneTreePolytope root = G.oneTreeLinearRelaxation root := by
  apply le_antisymm
  · -- Every 1-tree vertex already satisfies the linear relaxation, so the convex hull does too.
    rw [G.oneTreePolytope_eq_convexHull]
    refine convexHull_min ?_ (G.convex_oneTreeLinearRelaxation root)
    intro x hx
    rcases (G.mem_oneTreeVertices_iff root).1 hx with ⟨H, hH, rfl⟩
    exact G.subgraphIncidenceVector_mem_oneTreeLinearRelaxation (root := root) hH
  · -- Route correction: the reverse inclusion should now start from the ambient decomposition
    -- `x = xRoot + xDel`, then transport `xDel` to the deleted-root tree polytope and handle the
    -- root-cut slice as the convex hull of two-edge root-pair vertices.
    -- TODO: prove the reverse inclusion by the replan route: split an arbitrary relaxation point
    -- into root-cut and deleted-root parts, transport the deleted-root factor to Chapter 4.25,
    -- place the root factor in the convex hull of root-pair vertices, and assemble generator
    -- inclusion into `oneTreeVertices`.
    sorry

end

end Proposition_8_9

end SimpleGraph
