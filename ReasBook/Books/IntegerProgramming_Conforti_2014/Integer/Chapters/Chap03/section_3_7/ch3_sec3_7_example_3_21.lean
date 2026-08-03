import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

-- Semantic search tool `lean_leansearch` was not available in this environment; this file uses
-- a concrete complete-graph edge indexing by non-diagonal unordered pairs of vertices.

/-- The edge coordinates of the complete graph on `Fin n`, indexed by unordered pairs of distinct
vertices. -/
abbrev complete_graph_edges (n : ℕ) := {e : Sym2 (Fin n) // ¬ e.IsDiag}

/-- The canonical reinterpretation of a complete-graph edge coordinate as an edge of
`SimpleGraph.completeGraph (Fin n)`. -/
def completeGraphEdge {n : ℕ} (e : complete_graph_edges n) :
    (SimpleGraph.completeGraph (Fin n)).edgeSet :=
  ⟨e.1, by simpa using e.2⟩

/-- `complete_graph_edges n` coerces canonically to the edge type of
`SimpleGraph.completeGraph (Fin n)`. -/
instance {n : ℕ} : Coe (complete_graph_edges n) ((SimpleGraph.completeGraph (Fin n)).edgeSet) where
  coe := completeGraphEdge

/-- The canonical equivalence between the complete-graph edge coordinates `complete_graph_edges n`
and the edge type of `SimpleGraph.completeGraph (Fin n)`. -/
def completeGraphEdgeEquiv {n : ℕ} :
    complete_graph_edges n ≃ (SimpleGraph.completeGraph (Fin n)).edgeSet where
  toFun := completeGraphEdge
  invFun := fun e ↦ ⟨e.1, by simpa using e.2⟩
  left_inv := by
    intro e
    cases e
    rfl
  right_inv := by
    intro e
    cases e
    rfl

@[simp] theorem completeGraphEdge_coe {n : ℕ} (e : complete_graph_edges n) :
    ((e : (SimpleGraph.completeGraph (Fin n)).edgeSet) : Sym2 (Fin n)) = e.1 :=
  rfl

/-- The complete graph on `Fin n` has `n.choose 2` edge coordinates. -/
theorem card_complete_graph_edges (n : ℕ) :
    Fintype.card (complete_graph_edges n) = Nat.choose n 2 := by
  simpa [complete_graph_edges] using
    (Sym2.card_subtype_not_diag :
      Fintype.card {e : Sym2 (Fin n) // ¬ e.IsDiag} = (Fintype.card (Fin n)).choose 2)

/-- Two positions in a permutation of `Fin n` are consecutive when they differ by one. -/
def permutation_positions_consecutive {n : ℕ} (i j : Fin n) : Prop :=
  i.1 + 1 = j.1 ∨ j.1 + 1 = i.1

private def path_position_left {n : ℕ} (k : Fin (n - 1)) : Fin n :=
  ⟨k.1, by
    have hk : k.1 < n - 1 := k.2
    omega⟩

private def path_position_right {n : ℕ} (k : Fin (n - 1)) : Fin n :=
  ⟨k.1 + 1, by
    have hk : k.1 < n - 1 := k.2
    omega⟩

/-- Helper for Example 3.21: consecutive positions in a permutation always determine a non-diagonal
edge of the complete graph. -/
theorem path_edge_not_isDiag {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : Fin (n - 1)) :
    ¬ (s(σ (path_position_left k), σ (path_position_right k)) : Sym2 (Fin n)).IsDiag := by
  -- Consecutive positions are distinct, and a permutation preserves that distinction.
  rw [Sym2.mk_isDiag_iff]
  intro hdiag
  have hpos : path_position_left k = path_position_right k := σ.injective hdiag
  have hval := congrArg Fin.val hpos
  have hk : k.1 < n - 1 := k.2
  simp [path_position_left, path_position_right] at hval

/-- Helper for Example 3.21: the `k`-th edge of the path encoded by `σ`. -/
def path_edge_of_index {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : Fin (n - 1)) :
    complete_graph_edges n :=
  ⟨s(σ (path_position_left k), σ (path_position_right k)), path_edge_not_isDiag σ k⟩

/-- Helper for Example 3.21: the set of all edges appearing in the Hamiltonian path encoded by `σ`,
enumerated by consecutive positions. -/
def hamiltonian_path_edge_finset {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Finset (complete_graph_edges n) :=
  Finset.univ.image (path_edge_of_index σ)

/-- The edge `e` belongs to the Hamiltonian path determined by the permutation `σ` when it
appears among the `n - 1` consecutive edges of `σ`. -/
def is_hamiltonian_path_edge {n : ℕ} (σ : Equiv.Perm (Fin n)) (e : complete_graph_edges n) : Prop :=
  e ∈ hamiltonian_path_edge_finset σ

/-- The incidence vector of the Hamiltonian path of the complete graph on `Fin n` determined by
the permutation `σ`. -/
def hamiltonian_path_incidence_vector {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    complete_graph_edges n → ℝ :=
  fun e ↦ if e ∈ hamiltonian_path_edge_finset σ then 1 else 0

/-- The Hamiltonian-path polytope of the complete graph on `n` vertices is the convex hull of the
incidence vectors of Hamiltonian paths induced by permutations of the vertex set. -/
def hamiltonian_path_polytope (n : ℕ) : Set (complete_graph_edges n → ℝ) :=
  convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin n) ↦ hamiltonian_path_incidence_vector σ)

/-- The Hamiltonian-path polytope is the convex hull of the permutation-induced
Hamiltonian-path incidence vectors. -/
theorem hamiltonian_path_polytope_eq_convexHull (n : ℕ) :
    hamiltonian_path_polytope n =
      convexHull ℝ
        (Set.range fun σ : Equiv.Perm (Fin n) ↦ hamiltonian_path_incidence_vector σ) := by
  rfl

/-- Helper for Example 3.21: every witness for `is_hamiltonian_path_edge` comes from one of the
`n - 1` consecutive position pairs. -/
theorem is_hamiltonian_path_edge_iff_exists_index {n : ℕ} (σ : Equiv.Perm (Fin n))
    (e : complete_graph_edges n) :
    is_hamiltonian_path_edge σ e ↔ ∃ k : Fin (n - 1), path_edge_of_index σ k = e := by
  simp [is_hamiltonian_path_edge, hamiltonian_path_edge_finset]

/-- Helper for Example 3.21: distinct consecutive positions define distinct path edges. -/
theorem path_edge_of_index_injective {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Function.Injective (path_edge_of_index σ) := by
  intro i j hij
  have hval :
      s(σ (path_position_left i), σ (path_position_right i)) =
        s(σ (path_position_left j), σ (path_position_right j)) := by
    simpa [path_edge_of_index] using congrArg Subtype.val hij
  rw [Sym2.eq_iff] at hval
  rcases hval with hpair | hpair
  · -- If the ordered pairs agree, then the left endpoints already determine the index.
    have hleft :
        path_position_left i = path_position_left j := σ.injective hpair.1
    have hleft_val : i.1 = j.1 := by
      simpa [path_position_left] using congrArg Fin.val hleft
    exact Fin.ext hleft_val
  · -- The swapped case would force two consecutive positions to overlap inconsistently.
    have hleft :
        path_position_left i = path_position_right j := σ.injective hpair.1
    have hright :
        path_position_right i = path_position_left j := σ.injective hpair.2
    have hleft_val := congrArg Fin.val hleft
    have hright_val := congrArg Fin.val hright
    have hi : i.1 < n - 1 := i.2
    have hj : j.1 < n - 1 := j.2
    simp [path_position_left, path_position_right] at hleft_val hright_val
    omega

/-- Helper for Example 3.21: the path-edge finset has exactly `n - 1` elements. -/
theorem hamiltonian_path_edge_finset_card {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (hamiltonian_path_edge_finset σ).card = n - 1 := by
  -- The path edges are the image of all `n - 1` consecutive indices under an injective map.
  rw [hamiltonian_path_edge_finset]
  rw [Finset.card_image_of_injective _ (path_edge_of_index_injective σ)]
  simp

/-- Every Hamiltonian-path incidence vector of the complete graph on `n` vertices has exactly
`n - 1` edges. -/
theorem hamiltonian_path_incidence_vector_sum (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    ∑ e, hamiltonian_path_incidence_vector σ e = ((n - 1 : ℕ) : ℝ) := by
  classical
  -- Summing the `0/1` incidence coordinates counts the edges in the underlying path.
  calc
    ∑ e, hamiltonian_path_incidence_vector σ e = (hamiltonian_path_edge_finset σ).card := by
      simp [hamiltonian_path_incidence_vector]
    _ = ((n - 1 : ℕ) : ℝ) := by
      exact_mod_cast hamiltonian_path_edge_finset_card σ

/-- Every point of the Hamiltonian-path polytope of the complete graph on `n` vertices lies in the
hyperplane where the sum of the edge coordinates is `n - 1`. -/
theorem hamiltonian_path_polytope_subset_constant_sum_hyperplane (n : ℕ) :
    hamiltonian_path_polytope n ⊆
      {x : complete_graph_edges n → ℝ | ∑ e, x e = ((n - 1 : ℕ) : ℝ)} :=
  by
  -- The defining vertices satisfy the equation, and the equation cuts out a convex hyperplane.
  rw [hamiltonian_path_polytope_eq_convexHull]
  refine convexHull_min ?_ ?_
  · intro x hx
    rcases hx with ⟨σ, rfl⟩
    simpa using hamiltonian_path_incidence_vector_sum n σ
  · simpa using
      (convex_hyperplane ((Pi.basisFun ℝ (complete_graph_edges n)).sumCoords).isLinear
        (((n - 1 : ℕ) : ℝ)))

/-- Helper for Example 3.21: the distinguished reference edge `{0,1}` is non-diagonal once
`n ≥ 2`. -/
theorem reference_edge_not_isDiag {n : ℕ} (hn : 2 ≤ n) :
    ¬ (s((⟨0, by omega⟩ : Fin n), (⟨1, by omega⟩ : Fin n)) : Sym2 (Fin n)).IsDiag := by
  -- The distinguished endpoints are visibly different.
  rw [Sym2.mk_isDiag_iff]
  intro hdiag
  have hval := congrArg Fin.val hdiag
  norm_num at hval

/-- Helper for Example 3.21: the distinguished reference edge `{0,1}` in the complete graph on
`Fin n`. -/
def reference_edge (n : ℕ) (hn : 2 ≤ n) : complete_graph_edges n :=
  ⟨s((⟨0, by omega⟩ : Fin n), (⟨1, by omega⟩ : Fin n)), reference_edge_not_isDiag hn⟩

/-- Helper for Example 3.21: the coordinate-sum kernel is spanned by the standard basis differences
against a reference coordinate. -/
theorem sum_zero_submodule_eq_span_reference_differences
    (ι : Type*) [Finite ι] (i₀ : ι) :
    LinearMap.ker (Pi.basisFun ℝ ι).sumCoords =
      Submodule.span ℝ (Set.range fun i : ι ↦
        Pi.basisFun ℝ ι i - Pi.basisFun ℝ ι i₀) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  refine le_antisymm ?_ ?_
  · intro x hx
    have hx0 : (Pi.basisFun ℝ ι).sumCoords x = 0 := by
      simpa using hx
    have hdecomp :
        x = ∑ i, x i • (Pi.basisFun ℝ ι i - Pi.basisFun ℝ ι i₀) := by
      -- Coordinatewise, the reference-coordinate correction vanishes because the total sum is zero.
      ext j
      have hcoord : ∑ i, (x i • Pi.basisFun ℝ ι i) j = x j := by
        simpa using congrArg (fun y : ι → ℝ ↦ y j) ((Pi.basisFun ℝ ι).sum_repr x)
      by_cases hj : j = i₀
      · symm
        have hsum : ∑ i, x i = 0 := by
          simpa using hx0
        calc
          (∑ i, x i • (Pi.basisFun ℝ ι i - Pi.basisFun ℝ ι i₀)) j
              = ∑ i, (x i • Pi.basisFun ℝ ι i) j - ∑ i, x i := by
                  rw [hj]
                  simp [Pi.sub_apply, Pi.smul_apply, Pi.basisFun_apply, mul_sub, mul_one,
                    Finset.sum_sub_distrib]
          _ = x j - 0 := by rw [hcoord, hsum]
          _ = x j := by simp
      · symm
        calc
          (∑ i, x i • (Pi.basisFun ℝ ι i - Pi.basisFun ℝ ι i₀)) j
              = ∑ i, (x i • Pi.basisFun ℝ ι i) j := by
                  simp [Pi.sub_apply, Pi.smul_apply, Pi.basisFun_apply, hj]
          _ = x j := hcoord
    -- After the decomposition, each summand belongs to the generating span.
    rw [hdecomp]
    exact Submodule.sum_mem _ fun i _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · -- Each basis difference has coordinate sum zero.
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    change (Pi.basisFun ℝ ι i - Pi.basisFun ℝ ι i₀) ∈
      LinearMap.ker (Pi.basisFun ℝ ι).sumCoords
    simp

/-- Helper for Example 3.21: the coordinate-sum kernel on `ι → ℝ` has codimension one whenever
`ι` is nonempty. -/
theorem coordinate_sum_ker_finrank
    (ι : Type*) [Fintype ι] [Nonempty ι] :
    Module.finrank ℝ (LinearMap.ker (Pi.basisFun ℝ ι).sumCoords) = Fintype.card ι - 1 := by
  classical
  let i₀ : ι := Classical.choice ‹Nonempty ι›
  have hne : (Pi.basisFun ℝ ι).sumCoords ≠ 0 := by
    intro hzero
    have hvalue :=
      congrArg (fun f : (ι → ℝ) →ₗ[ℝ] ℝ ↦ f (Pi.basisFun ℝ ι i₀)) hzero
    simp at hvalue
  have hdim :
      Module.finrank ℝ (LinearMap.ker (Pi.basisFun ℝ ι).sumCoords) + 1 =
        Module.finrank ℝ (ι → ℝ) := by
    simpa using
      (Module.Dual.finrank_ker_add_one_of_ne_zero (f := (Pi.basisFun ℝ ι).sumCoords) hne)
  -- Rank-nullity for a nonzero linear functional gives codimension one.
  rw [Module.finrank_fintype_fun_eq_card] at hdim
  omega

/-- Helper for Example 3.21: the direction of the affine span is contained in the zero-sum
hyperplane determined by the edge-coordinate sum. -/
theorem hamiltonian_path_polytope_direction_le_sumCoords_ker (n : ℕ) :
    (affineSpan ℝ (hamiltonian_path_polytope n)).direction ≤
      LinearMap.ker (Pi.basisFun ℝ (complete_graph_edges n)).sumCoords := by
  let sumCoords := (Pi.basisFun ℝ (complete_graph_edges n)).sumCoords
  let x₀ : complete_graph_edges n → ℝ :=
    hamiltonian_path_incidence_vector (Equiv.refl (Fin n))
  let H : AffineSubspace ℝ (complete_graph_edges n → ℝ) :=
    AffineSubspace.mk' (k := ℝ) (P := complete_graph_edges n → ℝ) x₀ (LinearMap.ker sumCoords)
  have hx₀_mem : x₀ ∈ hamiltonian_path_polytope n := by
    -- The identity permutation contributes one generating vertex of the polytope.
    rw [hamiltonian_path_polytope_eq_convexHull]
    change hamiltonian_path_incidence_vector (Equiv.refl (Fin n)) ∈
      convexHull ℝ
        (Set.range fun σ : Equiv.Perm (Fin n) ↦ hamiltonian_path_incidence_vector σ)
    exact subset_convexHull ℝ _ (Set.mem_range_self (Equiv.refl (Fin n)))
  have hx₀_sum : sumCoords x₀ = ((n - 1 : ℕ) : ℝ) := by
    simpa [sumCoords, x₀] using hamiltonian_path_incidence_vector_sum n (Equiv.refl (Fin n))
  have hpoly_mem_H : hamiltonian_path_polytope n ⊆ H := by
    intro x hx
    change x ∈ AffineSubspace.mk' x₀ (LinearMap.ker sumCoords)
    rw [AffineSubspace.mem_mk']
    have hx_sum : sumCoords x = ((n - 1 : ℕ) : ℝ) := by
      simpa [sumCoords] using hamiltonian_path_polytope_subset_constant_sum_hyperplane n hx
    -- Equal coordinate sums make the difference lie in the kernel.
    change sumCoords (x - x₀) = 0
    rw [LinearMap.map_sub, hx_sum, hx₀_sum, sub_self]
  have h_aff : affineSpan ℝ (hamiltonian_path_polytope n) ≤ H := by
    exact affineSpan_le.2 hpoly_mem_H
  simpa [H, sumCoords] using
    (AffineSubspace.direction_le h_aff)

/-- Helper for Example 3.21: relabel a complete-graph edge by a permutation of the vertices. -/
def relabel_edge {n : ℕ} (π : Equiv.Perm (Fin n)) :
    complete_graph_edges n ≃ complete_graph_edges n where
  toFun e := ⟨e.1.map π, by
    -- A permutation preserves the fact that an unordered pair is non-diagonal.
    intro hdiag
    exact e.2 ((Sym2.isDiag_map π.injective).1 hdiag)⟩
  invFun e := ⟨e.1.map π.symm, by
    -- The inverse permutation preserves non-diagonality for the same reason.
    intro hdiag
    exact e.2 ((Sym2.isDiag_map π.symm.injective).1 hdiag)⟩
  left_inv e := by
    -- Relabeling by `π` and then by `π.symm` returns the original edge.
    apply Subtype.ext
    calc
      Sym2.map π.symm (Sym2.map π e.1) = Sym2.map (fun x : Fin n => x) e.1 := by
        have hm :
            Sym2.map π.symm (Sym2.map π e.1) =
              Sym2.map (fun x : Fin n => π.symm (π x)) e.1 := by
          simp [Sym2.map_map]
        exact hm.trans (by simp)
      _ = e.1 := by
        simpa using
          congrArg (fun f : Sym2 (Fin n) → Sym2 (Fin n) => f e.1)
            (Sym2.map_id' (α := Fin n))
  right_inv e := by
    -- The same calculation works in the opposite order.
    apply Subtype.ext
    calc
      Sym2.map π (Sym2.map π.symm e.1) = Sym2.map (fun x : Fin n => x) e.1 := by
        have hm :
            Sym2.map π (Sym2.map π.symm e.1) =
              Sym2.map (fun x : Fin n => π (π.symm x)) e.1 := by
          simp [Sym2.map_map]
        exact hm.trans (by simp)
      _ = e.1 := by
        simpa using
          congrArg (fun f : Sym2 (Fin n) → Sym2 (Fin n) => f e.1)
            (Sym2.map_id' (α := Fin n))

/-- Helper for Example 3.21: relabeling the vertices relabels every consecutive edge of the
associated Hamiltonian path. -/
theorem path_edge_of_index_relabel {n : ℕ} (π ρ : Equiv.Perm (Fin n)) (k : Fin (n - 1)) :
    path_edge_of_index (ρ.trans π) k = relabel_edge π (path_edge_of_index ρ k) := by
  -- This is the concrete bridge from a relabeled vertex order to the induced edge coordinate.
  apply Subtype.ext
  simp [path_edge_of_index, relabel_edge, Sym2.map_mk]

/-- Helper for Example 3.21: relabeling vertices preserves Hamiltonian-path edge membership after
transporting the queried edge by the same permutation. -/
theorem is_hamiltonian_path_edge_relabel_iff {n : ℕ} (π ρ : Equiv.Perm (Fin n))
    (e : complete_graph_edges n) :
    is_hamiltonian_path_edge (ρ.trans π) (relabel_edge π e) ↔ is_hamiltonian_path_edge ρ e := by
  -- Membership is witnessed by one consecutive index, and the previous lemma transports that
  -- witness exactly.
  rw [is_hamiltonian_path_edge_iff_exists_index, is_hamiltonian_path_edge_iff_exists_index]
  constructor
  · rintro ⟨k, hk⟩
    use k
    apply (relabel_edge π).injective
    simpa [path_edge_of_index_relabel] using hk
  · rintro ⟨k, hk⟩
    use k
    simpa [path_edge_of_index_relabel] using congrArg (relabel_edge π) hk

/-- Helper for Example 3.21: the Hamiltonian-path incidence vector is equivariant under relabeling
of the vertices. -/
theorem hamiltonian_path_incidence_vector_relabel_apply {n : ℕ} (π ρ : Equiv.Perm (Fin n))
    (e : complete_graph_edges n) :
    hamiltonian_path_incidence_vector (ρ.trans π) (relabel_edge π e) =
      hamiltonian_path_incidence_vector ρ e := by
  by_cases he : is_hamiltonian_path_edge ρ e
  · -- When the edge is present before relabeling, it is present after relabeling as well.
    have hrel : is_hamiltonian_path_edge (ρ.trans π) (relabel_edge π e) :=
      (is_hamiltonian_path_edge_relabel_iff π ρ e).2 he
    have he' : e ∈ hamiltonian_path_edge_finset ρ := by
      simpa [is_hamiltonian_path_edge] using he
    have hrel' : relabel_edge π e ∈ hamiltonian_path_edge_finset (ρ.trans π) := by
      simpa [is_hamiltonian_path_edge] using hrel
    simp [hamiltonian_path_incidence_vector, he', hrel']
  · -- The absent-edge case transports in the same way.
    have hrel : ¬ is_hamiltonian_path_edge (ρ.trans π) (relabel_edge π e) := by
      intro h
      exact he ((is_hamiltonian_path_edge_relabel_iff π ρ e).1 h)
    have he' : e ∉ hamiltonian_path_edge_finset ρ := by
      simpa [is_hamiltonian_path_edge] using he
    have hrel' : relabel_edge π e ∉ hamiltonian_path_edge_finset (ρ.trans π) := by
      simpa [is_hamiltonian_path_edge] using hrel
    simp [hamiltonian_path_incidence_vector, he', hrel']

/-- Helper for Example 3.21: a vertex relabeling that fixes `0` and `1` also fixes the reference
edge `{0,1}`. -/
theorem relabel_reference_edge_of_fixes_zero_one {n : ℕ} (hn : 2 ≤ n) (π : Equiv.Perm (Fin n))
    (h0 : π (⟨0, by omega⟩ : Fin n) = ⟨0, by omega⟩)
    (h1 : π (⟨1, by omega⟩ : Fin n) = ⟨1, by omega⟩) :
    relabel_edge π (reference_edge n hn) = reference_edge n hn := by
  -- Relabeling sends the unordered pair `{0,1}` to `{π 0, π 1}`, so fixing both endpoints fixes
  -- the distinguished reference coordinate itself.
  apply Subtype.ext
  simp [relabel_edge, reference_edge, h0, h1, Sym2.map_mk]

/-- Helper for Example 3.21: every non-reference edge has one of the three endpoint patterns used
in the source proof. -/
theorem nonreference_edge_cases
    (n : ℕ) (hn : 2 ≤ n) (e : complete_graph_edges n) (href : e ≠ reference_edge n hn) :
    (∃ v : Fin n, v ≠ (⟨1, by omega⟩ : Fin n) ∧ e.1 = s((⟨0, by omega⟩ : Fin n), v)) ∨
      (∃ v : Fin n, v ≠ (⟨0, by omega⟩ : Fin n) ∧ e.1 = s((⟨1, by omega⟩ : Fin n), v)) ∨
      ∃ u v : Fin n,
        u ≠ (⟨0, by omega⟩ : Fin n) ∧ u ≠ (⟨1, by omega⟩ : Fin n) ∧
          v ≠ (⟨0, by omega⟩ : Fin n) ∧ v ≠ (⟨1, by omega⟩ : Fin n) ∧ e.1 = s(u, v) := by
  let zero : Fin n := ⟨0, by omega⟩
  let one : Fin n := ⟨1, by omega⟩
  let u := e.1.out.1
  let v := e.1.out.2
  have huv : s(u, v) = e.1 := e.1.out_eq
  -- Split first by whether one endpoint is `0`; if so, the edge is of the `{0, *}` type unless
  -- it is exactly the excluded reference edge.
  by_cases hu0 : u = zero
  · refine Or.inl ?_
    refine ⟨v, ?_, ?_⟩
    · intro hv1
      apply href
      apply Subtype.ext
      simpa [reference_edge, zero, one, hu0, hv1] using huv.symm
    · simpa [zero, hu0] using huv.symm
  · by_cases hv0 : v = zero
    · refine Or.inl ?_
      refine ⟨u, ?_, ?_⟩
      · intro hu1
        apply href
        apply Subtype.ext
        have huv0 : e.1 = s(u, zero) := by
          simpa [hv0, zero] using huv.symm
        have hswap : s(u, zero) = s(zero, one) := by
          simpa [hu1, zero, one] using (Sym2.eq_swap : s(one, zero) = s(zero, one))
        simpa [reference_edge, zero, one] using huv0.trans hswap
      · have huv0 : e.1 = s(u, zero) := by
          simpa [hv0, zero] using huv.symm
        simpa [zero] using huv0.trans (Sym2.eq_swap : s(u, zero) = s(zero, u))
    · -- Once both endpoints avoid `0`, split by whether one endpoint is `1`.
      by_cases hu1 : u = one
      · refine Or.inr <| Or.inl ?_
        refine ⟨v, ?_, ?_⟩
        · exact hv0
        · simpa [one, hu1] using huv.symm
      · by_cases hv1 : v = one
        · refine Or.inr <| Or.inl ?_
          refine ⟨u, ?_, ?_⟩
          · exact hu0
          · have huv1 : e.1 = s(u, one) := by
              simpa [hv1, one] using huv.symm
            simpa [one] using huv1.trans (Sym2.eq_swap : s(u, one) = s(one, u))
        · refine Or.inr <| Or.inr ?_
          exact ⟨u, v, hu0, hu1, hv0, hv1, huv.symm⟩

/-- Helper for Example 3.21: the standard edge `{0, last}` of the cycle
`0, 1, ..., n - 1, 0`. -/
theorem standard_last_edge_not_isDiag {n : ℕ} (hn : 3 ≤ n) :
    ¬ (s((⟨0, by omega⟩ : Fin n), (⟨n - 1, by omega⟩ : Fin n)) : Sym2 (Fin n)).IsDiag := by
  -- The endpoints `0` and `n - 1` are distinct once `n ≥ 3`.
  rw [Sym2.mk_isDiag_iff]
  intro hdiag
  have hval := congrArg Fin.val hdiag
  simp at hval
  omega

/-- Helper for Example 3.21: the standard edge `{0, last}` used in the source tour-cut proof. -/
def standard_last_edge (n : ℕ) (hn : 3 ≤ n) : complete_graph_edges n :=
  ⟨s((⟨0, by omega⟩ : Fin n), (⟨n - 1, by omega⟩ : Fin n)), standard_last_edge_not_isDiag hn⟩

/-- Helper for Example 3.21: the standard edge `{1, 2}` is non-diagonal once `n ≥ 3`. -/
theorem standard_one_two_edge_not_isDiag {n : ℕ} (hn : 3 ≤ n) :
    ¬ (s((⟨1, by omega⟩ : Fin n), (⟨2, by omega⟩ : Fin n)) : Sym2 (Fin n)).IsDiag := by
  -- The explicit vertices `1` and `2` are distinct in the required range.
  rw [Sym2.mk_isDiag_iff]
  intro hdiag
  have hval := congrArg Fin.val hdiag
  norm_num at hval

/-- Helper for Example 3.21: the standard edge `{1, 2}` used for the second cut of the fixed
Hamiltonian tour. -/
def standard_one_two_edge (n : ℕ) (hn : 3 ≤ n) : complete_graph_edges n :=
  ⟨s((⟨1, by omega⟩ : Fin n), (⟨2, by omega⟩ : Fin n)), standard_one_two_edge_not_isDiag hn⟩

/-- Helper for Example 3.21: the standard edge `{2, 3}` is non-diagonal once `n ≥ 4`. -/
theorem standard_two_three_edge_not_isDiag {n : ℕ} (hn : 4 ≤ n) :
    ¬ (s((⟨2, by omega⟩ : Fin n), (⟨3, by omega⟩ : Fin n)) : Sym2 (Fin n)).IsDiag := by
  -- The explicit vertices `2` and `3` are distinct in the required range.
  rw [Sym2.mk_isDiag_iff]
  intro hdiag
  have hval := congrArg Fin.val hdiag
  norm_num at hval

/-- Helper for Example 3.21: the standard edge `{2, 3}` used for edges disjoint from the
reference edge. -/
def standard_two_three_edge (n : ℕ) (hn : 4 ≤ n) : complete_graph_edges n :=
  ⟨s((⟨2, by omega⟩ : Fin n), (⟨3, by omega⟩ : Fin n)), standard_two_three_edge_not_isDiag hn⟩

/-- Helper for Example 3.21: in the identity ordering, the first path edge is the reference edge
`{0, 1}`. -/
theorem path_edge_of_index_refl_zero_eq_reference_edge {n : ℕ} (hn : 2 ≤ n) :
    path_edge_of_index (Equiv.refl (Fin n)) (⟨0, by omega⟩ : Fin (n - 1)) = reference_edge n hn := by
  -- The identity permutation starts with the consecutive vertices `0` and `1`.
  apply Subtype.ext
  simp [path_edge_of_index, reference_edge, path_position_left, path_position_right]

/-- Helper for Example 3.21: every non-wraparound edge of the fixed cycle
`0, 1, ..., n - 1, 0` agrees with the corresponding shifted edge of the identity path. -/
theorem path_edge_of_index_finRotate_eq_path_edge_of_index_refl_succ {n : ℕ}
    (hn : 3 ≤ n) (k : ℕ) (hk : k < n - 2) :
    path_edge_of_index (finRotate n) (⟨k, by omega⟩ : Fin (n - 1)) =
      path_edge_of_index (Equiv.refl (Fin n)) (⟨k + 1, by omega⟩ : Fin (n - 1)) := by
  -- The rotated cycle and the identity path share all interior consecutive edges after shifting
  -- the index by one.
  apply Subtype.ext
  simp [path_edge_of_index, path_position_left, path_position_right]
  left
  constructor
  · -- The left endpoint advances from `k` to `k + 1` without wrapping.
    simp [Fin.add_def]
    have hmod : (k + 1) % n = k + 1 := by
      rw [Nat.mod_eq_of_lt]
      omega
    exact hmod
  · -- The right endpoint advances from `k + 1` to `k + 2`, still before the wraparound.
    simp [Fin.add_def]
    have hmod : (k + 1 + 1) % n = k + 1 + 1 := by
      rw [Nat.mod_eq_of_lt]
      omega
    exact hmod

/-- Helper for Example 3.21: the final edge of the rotated fixed cycle is exactly `{0, last}`. -/
theorem path_edge_of_index_finRotate_last_eq_standard_last_edge {n : ℕ} (hn : 3 ≤ n) :
    path_edge_of_index (finRotate n) (⟨n - 2, by omega⟩ : Fin (n - 1)) =
      standard_last_edge n hn := by
  -- The last consecutive pair of the rotated cycle is the unique wraparound from `last` back to
  -- `0`.
  apply Subtype.ext
  simp [path_edge_of_index, standard_last_edge, path_position_left, path_position_right]
  right
  constructor
  · -- The first endpoint is `last = n - 1`.
    simp [Fin.add_def]
    rw [Nat.mod_eq_of_lt]
    · omega
    · omega
  · -- The second endpoint wraps back to `0`.
    have hsum : n - 2 + 1 + 1 = n := by
      omega
    simpa [Fin.add_def, hsum]

/-- Helper for Example 3.21: rotating the fixed cycle sends `{0, last}` to the reference edge
`{0, 1}`. -/
theorem relabel_standard_last_edge_by_finRotate {n : ℕ} (hn : 3 ≤ n) :
    relabel_edge (finRotate n) (standard_last_edge n hn) = reference_edge n (by omega) := by
  -- The wraparound edge becomes the first edge of the rotated order.
  apply Subtype.ext
  simp [relabel_edge, standard_last_edge, reference_edge, Sym2.map_mk, Fin.add_def]
  right
  constructor
  · -- The endpoint `1` stays fixed modulo `n` because `n ≥ 3`.
    have hmod : 1 % n = 1 := by
      rw [Nat.mod_eq_of_lt]
      omega
    exact hmod
  · -- The endpoint `last + 1` wraps back to `0`.
    have hsum : n - 1 + 1 = n := by
      omega
    simpa [hsum]

/-- Helper for Example 3.21: rotating the reference edge `{0, 1}` yields the standard edge
`{1, 2}`. -/
theorem relabel_reference_edge_by_finRotate {n : ℕ} (hn : 3 ≤ n) :
    relabel_edge (finRotate n) (reference_edge n (by omega)) = standard_one_two_edge n hn := by
  -- One application of `finRotate` advances both endpoints by one without wrapping.
  apply Subtype.ext
  simp [relabel_edge, standard_one_two_edge, reference_edge, Sym2.map_mk, Fin.add_def]
  left
  constructor
  · have hmod : 1 % n = 1 := by
      rw [Nat.mod_eq_of_lt]
      omega
    simpa using hmod
  · have hmod : 2 % n = 2 := by
      rw [Nat.mod_eq_of_lt]
      omega
    simpa using hmod

/-- Helper for Example 3.21: rotating `{1, 2}` once yields `{2, 3}` in the fixed cycle. -/
theorem relabel_standard_one_two_edge_by_finRotate {n : ℕ} (hn : 4 ≤ n) :
    relabel_edge (finRotate n) (standard_one_two_edge n (by omega)) = standard_two_three_edge n hn := by
  -- With `n ≥ 4`, both endpoints stay away from the wraparound and simply advance by one.
  apply Subtype.ext
  simp [relabel_edge, standard_one_two_edge, standard_two_three_edge, Sym2.map_mk, Fin.add_def]
  left
  constructor
  · have hmod : 2 % n = 2 := by
      rw [Nat.mod_eq_of_lt]
      omega
    simpa using hmod
  · have hmod : 3 % n = 3 := by
      rw [Nat.mod_eq_of_lt]
      omega
    simpa using hmod

/-- Helper for Example 3.21: transporting a proved basis-difference identity along a vertex
relabeling transports both incidence vectors and both basis coordinates. -/
theorem transport_incidence_difference
    {n : ℕ} {σ τ : Equiv.Perm (Fin n)} {e₁ e₂ : complete_graph_edges n}
    (π : Equiv.Perm (Fin n))
    (hdiff :
      hamiltonian_path_incidence_vector σ - hamiltonian_path_incidence_vector τ =
        Pi.basisFun ℝ (complete_graph_edges n) e₁ -
          Pi.basisFun ℝ (complete_graph_edges n) e₂) :
    hamiltonian_path_incidence_vector (σ.trans π) -
        hamiltonian_path_incidence_vector (τ.trans π) =
      Pi.basisFun ℝ (complete_graph_edges n) (relabel_edge π e₁) -
        Pi.basisFun ℝ (complete_graph_edges n) (relabel_edge π e₂) := by
  -- Evaluate the known identity on the inverse-relabeled coordinate and rewrite both sides by
  -- equivariance of the incidence vector and of the basis functions.
  ext d
  have hσ :=
    hamiltonian_path_incidence_vector_relabel_apply π σ ((relabel_edge π).symm d)
  have hτ :=
    hamiltonian_path_incidence_vector_relabel_apply π τ ((relabel_edge π).symm d)
  rw [(relabel_edge π).apply_symm_apply] at hσ hτ
  have hb₁ :
      Pi.basisFun ℝ (complete_graph_edges n) e₁ ((relabel_edge π).symm d) =
        Pi.basisFun ℝ (complete_graph_edges n) (relabel_edge π e₁) d := by
    by_cases h : relabel_edge π e₁ = d
    · have h' : e₁ = (relabel_edge π).symm d := by
        have h'' := congrArg (fun x => (relabel_edge π).symm x) h
        simpa using h''
      simp [Pi.basisFun_apply, h, h']
    · have h' : e₁ ≠ (relabel_edge π).symm d := by
        intro h'
        apply h
        simpa [h'] using congrArg (relabel_edge π) h'
      simp [Pi.basisFun_apply, h, h']
  have hb₂ :
      Pi.basisFun ℝ (complete_graph_edges n) e₂ ((relabel_edge π).symm d) =
        Pi.basisFun ℝ (complete_graph_edges n) (relabel_edge π e₂) d := by
    by_cases h : relabel_edge π e₂ = d
    · have h' : e₂ = (relabel_edge π).symm d := by
        have h'' := congrArg (fun x => (relabel_edge π).symm x) h
        simpa using h''
      simp [Pi.basisFun_apply, h, h']
    · have h' : e₂ ≠ (relabel_edge π).symm d := by
        intro h'
        apply h
        simpa [h'] using congrArg (relabel_edge π) h'
      simp [Pi.basisFun_apply, h, h']
  have hcoord :=
    congrArg (fun f : complete_graph_edges n → ℝ ↦ f ((relabel_edge π).symm d)) hdiff
  calc
    hamiltonian_path_incidence_vector (σ.trans π) d -
        hamiltonian_path_incidence_vector (τ.trans π) d
      = hamiltonian_path_incidence_vector σ ((relabel_edge π).symm d) -
          hamiltonian_path_incidence_vector τ ((relabel_edge π).symm d) := by
            rw [hσ, hτ]
    _ = Pi.basisFun ℝ (complete_graph_edges n) e₁ ((relabel_edge π).symm d) -
          Pi.basisFun ℝ (complete_graph_edges n) e₂ ((relabel_edge π).symm d) := by
            simpa [Pi.sub_apply] using hcoord
    _ = Pi.basisFun ℝ (complete_graph_edges n) (relabel_edge π e₁) d -
          Pi.basisFun ℝ (complete_graph_edges n) (relabel_edge π e₂) d := by
            rw [hb₁, hb₂]

/-- Helper for Example 3.21: two Hamiltonian-path vertices coming from one common Hamiltonian tour
can realize the required basis difference against the reference edge. -/
theorem reference_edge_difference_vertex_witness
    (n : ℕ) (hn : 2 ≤ n) (e : complete_graph_edges n) :
    ∃ σ τ : Equiv.Perm (Fin n),
      hamiltonian_path_incidence_vector σ - hamiltonian_path_incidence_vector τ =
        Pi.basisFun ℝ (complete_graph_edges n) e -
          Pi.basisFun ℝ (complete_graph_edges n) (reference_edge n hn) := by
  -- Route correction: isolate the missing common-tour construction before any affine-span
  -- argument, so the remaining lower-bound proof is purely linear-algebraic.
  by_cases href : e = reference_edge n hn
  · -- If the target edge already is the reference edge, one path vertex used twice gives zero.
    refine ⟨Equiv.refl (Fin n), Equiv.refl (Fin n), ?_⟩
    simp [href]
  · -- TODO: first prove the base fixed-cycle incidence identity
    -- `finRotate - refl = e_{0,last} - e_{0,1}` using the new path-edge rewrite lemmas above.
    -- Then transport that identity, via the relabeling lemmas above, to the `{1, 2}` and `{2, 3}`
    -- standard witnesses before applying `nonreference_edge_cases`.
    have hcases := nonreference_edge_cases n hn e href
    sorry

/-- Helper for Example 3.21: every standard basis difference against the reference edge lies in the
direction of the affine span of the Hamiltonian-path polytope. -/
theorem reference_edge_difference_mem_hamiltonian_path_direction
    (n : ℕ) (hn : 2 ≤ n) (e : complete_graph_edges n) :
    Pi.basisFun ℝ (complete_graph_edges n) e -
        Pi.basisFun ℝ (complete_graph_edges n) (reference_edge n hn) ∈
      (affineSpan ℝ (hamiltonian_path_polytope n)).direction := by
  rcases reference_edge_difference_vertex_witness n hn e with ⟨σ, τ, hdiff⟩
  have hσ_mem : hamiltonian_path_incidence_vector σ ∈ hamiltonian_path_polytope n := by
    -- Each permutation-induced path vector is one generator of the defining convex hull.
    rw [hamiltonian_path_polytope_eq_convexHull]
    exact subset_convexHull ℝ _ (Set.mem_range_self σ)
  have hτ_mem : hamiltonian_path_incidence_vector τ ∈ hamiltonian_path_polytope n := by
    -- The second witness vector belongs to the same generating family.
    rw [hamiltonian_path_polytope_eq_convexHull]
    exact subset_convexHull ℝ _ (Set.mem_range_self τ)
  have hσ_aff :
      hamiltonian_path_incidence_vector σ ∈ affineSpan ℝ (hamiltonian_path_polytope n) := by
    -- Passing from the polytope to its affine span is immediate.
    exact subset_affineSpan ℝ _ hσ_mem
  have hτ_aff :
      hamiltonian_path_incidence_vector τ ∈ affineSpan ℝ (hamiltonian_path_polytope n) := by
    -- The same affine-span inclusion applies to the second vertex.
    exact subset_affineSpan ℝ _ hτ_mem
  have hvsub :
      hamiltonian_path_incidence_vector σ - hamiltonian_path_incidence_vector τ ∈
        (affineSpan ℝ (hamiltonian_path_polytope n)).direction := by
    -- Differences of two affine-span points lie in the direction subspace.
    simpa using AffineSubspace.vsub_mem_direction hσ_aff hτ_aff
  simpa [hdiff] using hvsub

/-- Helper for Example 3.21: once the basis differences are in the direction, the whole
coordinate-sum kernel is in the direction by the standard spanning argument. -/
theorem sumCoords_ker_le_hamiltonian_path_direction
    (n : ℕ) (hn : 2 ≤ n) :
    LinearMap.ker (Pi.basisFun ℝ (complete_graph_edges n)).sumCoords ≤
      (affineSpan ℝ (hamiltonian_path_polytope n)).direction := by
  -- Rewrite the zero-sum hyperplane as the span of the reference-edge basis differences.
  rw [sum_zero_submodule_eq_span_reference_differences
    (ι := complete_graph_edges n) (i₀ := reference_edge n hn)]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨e, rfl⟩
  -- Each generator belongs to the direction by the affine-span difference lemma above.
  exact reference_edge_difference_mem_hamiltonian_path_direction n hn e

/-- Example 3.21. The Hamiltonian-path polytope of the complete graph on `n` vertices has
dimension `\binom{n}{2} - 1`. -/
theorem hamiltonian_path_polytope_finrank_direction_affineSpan (n : ℕ) :
    Module.finrank ℝ (affineSpan ℝ (hamiltonian_path_polytope n)).direction =
      Nat.choose n 2 - 1 := by
  by_cases hn : 2 ≤ n
  · have hdirection :
        (affineSpan ℝ (hamiltonian_path_polytope n)).direction =
          LinearMap.ker (Pi.basisFun ℝ (complete_graph_edges n)).sumCoords := by
      -- The upper hyperplane containment and the lower spanning argument meet exactly.
      exact le_antisymm
        (hamiltonian_path_polytope_direction_le_sumCoords_ker n)
        (sumCoords_ker_le_hamiltonian_path_direction n hn)
    haveI : Nonempty (complete_graph_edges n) := ⟨reference_edge n hn⟩
    -- After identifying the direction with the zero-sum hyperplane, compute its finrank.
    rw [hdirection, coordinate_sum_ker_finrank (ι := complete_graph_edges n)]
    rw [card_complete_graph_edges]
  · interval_cases n
    · have hcard : Fintype.card (complete_graph_edges 0) = 0 := by
        rw [card_complete_graph_edges]
        simp
      haveI : IsEmpty (complete_graph_edges 0) := Fintype.card_eq_zero_iff.mp hcard
      have hdirection :
          (affineSpan ℝ (hamiltonian_path_polytope 0)).direction = ⊥ := by
        refine (Submodule.eq_bot_iff _).2 ?_
        intro x hx
        -- With no edge coordinates, every vector in the ambient space is zero.
        have hx0 : x = 0 := Subsingleton.elim _ _
        simp [hx0]
      rw [hdirection, finrank_bot]
      simp
    · have hcard : Fintype.card (complete_graph_edges 1) = 0 := by
        rw [card_complete_graph_edges]
        simp
      haveI : IsEmpty (complete_graph_edges 1) := Fintype.card_eq_zero_iff.mp hcard
      have hdirection :
          (affineSpan ℝ (hamiltonian_path_polytope 1)).direction = ⊥ := by
        refine (Submodule.eq_bot_iff _).2 ?_
        intro x hx
        -- Again the ambient function space is subsingleton because there are no edges.
        have hx0 : x = 0 := Subsingleton.elim _ _
        simp [hx0]
      rw [hdirection, finrank_bot]
      simp

end
