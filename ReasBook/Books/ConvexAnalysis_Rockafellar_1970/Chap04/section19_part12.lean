/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Xinyi Guo, Siyuan Shao, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section19_part11

open scoped BigOperators
open scoped Pointwise
open Topology

section Chap19
section Section19


/-- Helper for Theorem 19.6: `weightedSumSetWithRecession` is exactly the finite Minkowski
sum of the branch sets `if λᵢ = 0 then 0⁺Cᵢ else λᵢ • Cᵢ`. -/
lemma helperForTheorem_19_6_weightedSumSetWithRecession_eq_finsetSumIf
    {n m : ℕ} {C : Fin m → Set (Fin n → ℝ)} {lam : Fin m → ℝ} :
    weightedSumSetWithRecession (n := n) (m := m) (C := C) (lam := lam) =
      ∑ i, (if lam i = 0 then Set.recessionCone (C i) else lam i • C i) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine (Set.mem_finset_sum (t := (Finset.univ : Finset (Fin m)))
      (f := fun i => if lam i = 0 then Set.recessionCone (C i) else lam i • C i)
      (a := ∑ i, y i)).2 ?_
    refine ⟨y, ?_, rfl⟩
    intro i hi
    exact hy i
  · intro hx
    rcases (Set.mem_finset_sum (t := (Finset.univ : Finset (Fin m)))
      (f := fun i => if lam i = 0 then Set.recessionCone (C i) else lam i • C i)
      (a := x)).1 hx with ⟨y, hy, hsum⟩
    refine ⟨y, ?_, ?_⟩
    · intro i
      have hiuniv : i ∈ (Finset.univ : Finset (Fin m)) := by
        simp
      exact hy (i := i) hiuniv
    simpa using hsum.symm

/-- Helper for Theorem 19.6: for each index `i`, the branch set
`if λᵢ = 0 then 0⁺Cᵢ else λᵢ • Cᵢ` is polyhedral. -/
lemma helperForTheorem_19_6_polyhedral_component_if_zero_or_scaled
    {n m : ℕ} {C : Fin m → Set (Fin n → ℝ)}
    (h_nonempty : ∀ i, (C i).Nonempty)
    (h_polyhedral : ∀ i, IsPolyhedralConvexSet n (C i))
    (lam : Fin m → ℝ) :
    ∀ i, IsPolyhedralConvexSet n
      (if lam i = 0 then Set.recessionCone (C i) else lam i • C i) := by
  intro i
  have hrepr :=
    polyhedralConvexSet_smul_recessionCone_and_representation
      (n := n) (C := C i) (h_nonempty i) (h_polyhedral i)
  by_cases hzero : lam i = 0
  · simpa [hzero] using hrepr.2.1
  · simpa [hzero] using (hrepr.1 (lam i))

/-- Helper for Theorem 19.6: finite Minkowski sums of polyhedral convex sets are polyhedral. -/
lemma helperForTheorem_19_6_polyhedral_finset_sum
    {n m : ℕ} {S : Fin m → Set (Fin n → ℝ)}
    (hS_poly : ∀ i, IsPolyhedralConvexSet n (S i)) :
    IsPolyhedralConvexSet n (∑ i, S i) := by
  classical
  have hsum_poly :
      ∀ t : Finset (Fin m), IsPolyhedralConvexSet n (Finset.sum t S) := by
    intro t
    refine Finset.induction_on t ?_ ?_
    · simpa using (helperForTheorem_19_1_zero_set_polyhedral (m := n))
    · intro a t ha ht
      have ha_poly : IsPolyhedralConvexSet n (S a) := hS_poly a
      have hadd_poly : IsPolyhedralConvexSet n (S a + Finset.sum t S) :=
        polyhedral_convexSet_add n (S a) (Finset.sum t S) ha_poly ht
      simpa [Finset.sum_insert ha] using hadd_poly
  simpa using hsum_poly (Finset.univ : Finset (Fin m))

/-- Helper for Theorem 19.6: polyhedral family members are closed and convex. -/
lemma helperForTheorem_19_6_closed_convex_of_polyhedral_family
    {n m : ℕ} {C : Fin m → Set (Fin n → ℝ)}
    (h_polyhedral : ∀ i, IsPolyhedralConvexSet n (C i)) :
    (∀ i, IsClosed (C i)) ∧ (∀ i, Convex ℝ (C i)) := by
  refine ⟨?_, ?_⟩
  · intro i
    exact
      (helperForTheorem_19_1_polyhedral_imp_closed_finiteFaces
        (n := n) (C := C i) (h_polyhedral i)).1
  · intro i
    exact helperForTheorem_19_1_polyhedral_isConvex (n := n) (C := C i) (h_polyhedral i)

/-- Helper for Theorem 19.6: if each `closure (K i)` is polyhedral, then
`closure (∑ i, K i) = ∑ i, closure (K i)`. -/
lemma helperForTheorem_19_6_closure_sum_liftedCones_eq_sum_closure_liftedCones_polyhedral
    {n m : ℕ} {K : Fin m → Set (Fin (n + 1) → ℝ)}
    (hK_poly : ∀ i, IsPolyhedralConvexSet (n + 1) (closure (K i))) :
    closure (∑ i, K i) = ∑ i, closure (K i) := by
  have hsum_poly :
      IsPolyhedralConvexSet (n + 1) (∑ i, closure (K i)) :=
    helperForTheorem_19_6_polyhedral_finset_sum
      (n := n + 1) (m := m) (S := fun i => closure (K i)) hK_poly
  have hsum_closed : IsClosed (∑ i, closure (K i)) :=
    (helperForTheorem_19_1_polyhedral_imp_closed_finiteFaces
      (n := n + 1) (C := ∑ i, closure (K i)) hsum_poly).1
  have hsubset_left : closure (∑ i, K i) ⊆ ∑ i, closure (K i) := by
    refine closure_minimal ?_ hsum_closed
    intro x hx
    rcases
      (Set.mem_finset_sum (t := (Finset.univ : Finset (Fin m)))
        (f := K) (a := x)).1 hx with ⟨y, hy, hsum⟩
    refine (Set.mem_finset_sum (t := (Finset.univ : Finset (Fin m)))
      (f := fun i => closure (K i)) (a := x)).2 ?_
    refine ⟨y, ?_, hsum⟩
    intro i hi
    exact subset_closure (hy (i := i) hi)
  have hsubset_right : (∑ i, closure (K i)) ⊆ closure (∑ i, K i) := by
    classical
    have haux :
        ∀ t : Finset (Fin m),
          Finset.sum t (fun i => closure (K i)) ⊆ closure (Finset.sum t K) := by
      intro t
      refine Finset.induction_on t ?_ ?_
      · intro x hx
        simpa using hx
      · intro a t ha hrec x hx
        rcases (Set.mem_add).1 (by simpa [Finset.sum_insert ha] using hx) with ⟨u, hu, v, hv, rfl⟩
        have hv' : v ∈ closure (Finset.sum t K) := hrec hv
        have hsubset_add :
            closure (K a) + closure (Finset.sum t K) ⊆ closure (K a + Finset.sum t K) := by
          simpa using
            (vadd_set_closure_subset (K := K a) (L := Finset.sum t K))
        have huv : u + v ∈ closure (K a) + closure (Finset.sum t K) :=
          (Set.mem_add).2 ⟨u, hu, v, hv', rfl⟩
        have huvc : u + v ∈ closure (K a + Finset.sum t K) := hsubset_add huv
        simpa [Finset.sum_insert ha] using huvc
    simpa using haux (Finset.univ : Finset (Fin m))
  exact Set.Subset.antisymm hsubset_left hsubset_right

/-- Helper for Theorem 19.6: the empty set in `ℝ^n` is polyhedral. -/
lemma helperForTheorem_19_6_polyhedral_empty_set
    {n : ℕ} :
    IsPolyhedralConvexSet n (∅ : Set (Fin n → ℝ)) := by
  classical
  let ι : Type := PUnit
  let b : ι → Fin n → ℝ := fun _ => 0
  let β : ι → ℝ := fun _ => -1
  refine ⟨ι, inferInstance, b, β, ?_⟩
  ext x
  constructor
  · intro hx
    exact False.elim (Set.notMem_empty x hx)
  · intro hx
    have hx' : x ∈ closedHalfSpaceLE n (b PUnit.unit) (β PUnit.unit) := by
      exact Set.mem_iInter.1 hx PUnit.unit
    have hfalse : (0 : ℝ) ≤ -1 := by
      simpa [closedHalfSpaceLE, b, β] using hx'
    linarith

/-- Helper for Theorem 19.6: when the index set is `Fin 0`, the closed convex hull of
the union is polyhedral. -/
lemma helperForTheorem_19_6_polyhedral_emptyClosureConvexHull_fin0
    {n : ℕ} {C : Fin 0 → Set (Fin n → ℝ)} :
    IsPolyhedralConvexSet n (closure (convexHull ℝ (⋃ i : Fin 0, C i))) := by
  have hempty : (⋃ i : Fin 0, C i) = (∅ : Set (Fin n → ℝ)) := by
    ext x
    simp
  have hclosure_empty :
      closure (convexHull ℝ (⋃ i : Fin 0, C i)) = (∅ : Set (Fin n → ℝ)) := by
    simp
  simpa [hclosure_empty] using
    (helperForTheorem_19_6_polyhedral_empty_set (n := n))

/-- Helper for Theorem 19.6: transporting nonemptiness from `Fin n → ℝ` to
`EuclideanSpace ℝ (Fin n)` via `EuclideanSpace.equiv.symm`. -/
lemma helperForTheorem_19_6_nonempty_transport_toEuclidean
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (hC_nonempty : C.Nonempty) :
    (((EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm) '' C).Nonempty := by
  rcases hC_nonempty with ⟨x, hx⟩
  exact ⟨(EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm x, ⟨x, hx, rfl⟩⟩

/-- Helper for Theorem 19.6: transporting closedness from `Fin n → ℝ` to
`EuclideanSpace ℝ (Fin n)` via `EuclideanSpace.equiv.symm`. -/
lemma helperForTheorem_19_6_closed_transport_toEuclidean
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (hC_closed : IsClosed C) :
    IsClosed (((EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm) '' C) := by
  simpa using
    (((EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm.toHomeomorph).isClosed_image).2
      hC_closed

/-- Helper for Theorem 19.6: transporting convexity from `Fin n → ℝ` to
`EuclideanSpace ℝ (Fin n)` via `EuclideanSpace.equiv.symm`. -/
lemma helperForTheorem_19_6_convex_transport_toEuclidean
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (hC_convex : Convex ℝ C) :
    Convex ℝ (((EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm) '' C) := by
  simpa using
    hC_convex.linear_image ((EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm.toLinearMap)

/-- Helper for Theorem 19.6: explicit coordinate identities between the `Fin` model
and `EuclideanSpace` via `EuclideanSpace.equiv`. -/
lemma helperForTheorem_19_6_finEuclidean_firstTail_bridge
    {n : ℕ} :
    let eNp1 : (Fin (n + 1) → ℝ) → EuclideanSpace ℝ (Fin (n + 1)) :=
      (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin (n + 1))).symm
    let coordsE : EuclideanSpace ℝ (Fin (n + 1)) → (Fin (n + 1) → ℝ) :=
      EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin (n + 1))
    let firstE : EuclideanSpace ℝ (Fin (n + 1)) → ℝ :=
      fun v => coordsE v 0
    let tailE : EuclideanSpace ℝ (Fin (n + 1)) → (Fin n → ℝ) :=
      fun v i => coordsE v (Fin.succ i)
    (∀ v, firstE (eNp1 v) = v 0) ∧
      (∀ v, tailE (eNp1 v) = fun i => v (Fin.succ i)) := by
  intro eNp1 coordsE firstE tailE
  constructor
  · intro v
    simp [firstE, coordsE, eNp1]
  · intro v
    funext i
    simp [tailE, coordsE, eNp1]

/-- Helper for Theorem 19.6: the lifted slice `{v | v₀ = 1, tail v ∈ C}` is nonempty
whenever `C` is nonempty. -/
lemma helperForTheorem_19_6_nonempty_liftedSlice
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (hC_nonempty : C.Nonempty) :
    ({v : Fin (n + 1) → ℝ | v 0 = 1 ∧ (fun j : Fin n => v (Fin.succ j)) ∈ C}).Nonempty := by
  rcases hC_nonempty with ⟨x, hx⟩
  refine ⟨Fin.cases (1 : ℝ) x, ?_⟩
  constructor
  · simp
  · simpa using hx

/-- Helper for Theorem 19.6: polyhedrality of a base set `C` implies polyhedrality of the
lifted slice `{v | v₀ = 1, tail v ∈ C}`. -/
lemma helperForTheorem_19_6_polyhedral_liftedSlice
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (hC_polyhedral : IsPolyhedralConvexSet n C) :
    IsPolyhedralConvexSet (n + 1)
      {v : Fin (n + 1) → ℝ | v 0 = 1 ∧ (fun j : Fin n => v (Fin.succ j)) ∈ C} := by
  rcases (isPolyhedralConvexSet_iff_exists_finite_halfspaces n C).1 hC_polyhedral with
    ⟨k, b, β, hCeq⟩
  let aEq : Fin 1 → Fin (n + 1) → ℝ :=
    fun _ => Fin.cases (1 : ℝ) (fun _ : Fin n => 0)
  let αEq : Fin 1 → ℝ := fun _ => 1
  let bIneq : Fin k → Fin (n + 1) → ℝ := fun r => Fin.cases (0 : ℝ) (b r)
  let βIneq : Fin k → ℝ := β
  have hpoly_system :
      IsPolyhedralConvexSet (n + 1)
        {v : Fin (n + 1) → ℝ |
          (∀ t, v ⬝ᵥ aEq t = αEq t) ∧
            (∀ r, v ⬝ᵥ bIneq r ≤ βIneq r)} := by
    simpa [aEq, αEq, bIneq, βIneq] using
      (polyhedralConvexSet_solutionSet_linearEq_and_inequalities
        (n + 1) 1 k aEq αEq bIneq βIneq)
  have htarget_eq :
      {v : Fin (n + 1) → ℝ | v 0 = 1 ∧ (fun j : Fin n => v (Fin.succ j)) ∈ C} =
        {v : Fin (n + 1) → ℝ |
          (∀ t, v ⬝ᵥ aEq t = αEq t) ∧
            (∀ r, v ⬝ᵥ bIneq r ≤ βIneq r)} := by
    ext v
    simp [hCeq, aEq, αEq, bIneq, βIneq, dotProduct, Fin.sum_univ_succ, closedHalfSpaceLE]
  simpa [htarget_eq] using hpoly_system

/-- Helper for Theorem 19.6: every point-generator belongs to its mixed convex hull. -/
lemma helperForTheorem_19_6_points_subset_mixedConvexHull
    {d : ℕ} {S₀ S₁ : Set (Fin d → ℝ)} :
    S₀ ⊆ mixedConvexHull (n := d) S₀ S₁ := by
  intro x hx
  refine (Set.mem_sInter).2 ?_
  intro C hC
  have hCprop :
      Convex ℝ C ∧ S₀ ⊆ C ∧
        (∀ ⦃dir⦄, dir ∈ S₁ → ∀ ⦃y⦄, y ∈ C → ∀ t : ℝ, 0 ≤ t → y + t • dir ∈ C) := by
    simpa [mixedConvexHull] using hC
  exact hCprop.2.1 hx

/-- Helper for Theorem 19.6: every direction-generator is a recession direction of the mixed
convex hull generated by the same data. -/
lemma helperForTheorem_19_6_directions_subset_recessionCone_mixedConvexHull
    {d : ℕ} {S₀ S₁ : Set (Fin d → ℝ)} :
    S₁ ⊆ Set.recessionCone (mixedConvexHull (n := d) S₀ S₁) := by
  intro dir hdir x hx t ht
  refine (Set.mem_sInter).2 ?_
  intro C hC
  have hCprop :
      Convex ℝ C ∧ S₀ ⊆ C ∧
        (∀ ⦃e⦄, e ∈ S₁ → ∀ ⦃y⦄, y ∈ C → ∀ s : ℝ, 0 ≤ s → y + s • e ∈ C) := by
    simpa [mixedConvexHull] using hC
  have hxC : x ∈ C := (Set.mem_sInter).1 hx C hC
  exact hCprop.2.2 hdir hxC t ht

/-- Helper for Theorem 19.6: every recession direction of a nonempty set lies in the
closure of the convex cone generated by that set. -/
lemma helperForTheorem_19_6_recessionDirection_mem_closure_convexConeHull_of_nonempty
    {d : ℕ} {C : Set (Fin d → ℝ)}
    (hC_nonempty : C.Nonempty)
    {dir : Fin d → ℝ}
    (hdir : dir ∈ Set.recessionCone C) :
    dir ∈ closure ((ConvexCone.hull ℝ C : Set (Fin d → ℝ))) := by
  rcases hC_nonempty with ⟨x0, hx0⟩
  have hlim_coeff :
      Filter.Tendsto (fun n : ℕ => ((n : ℝ)⁻¹ : ℝ)) Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hlim_smul :
      Filter.Tendsto (fun n : ℕ => ((n : ℝ)⁻¹ : ℝ) • x0) Filter.atTop (𝓝 ((0 : ℝ) • x0)) :=
    hlim_coeff.smul_const x0
  have hlim :
      Filter.Tendsto (fun n : ℕ => dir + ((n : ℝ)⁻¹ : ℝ) • x0)
        Filter.atTop (𝓝 dir) := by
    have hlim_const : Filter.Tendsto (fun _ : ℕ => dir) Filter.atTop (𝓝 dir) :=
      tendsto_const_nhds
    have hlim_add := hlim_const.add hlim_smul
    simpa [zero_smul] using hlim_add
  have hmem_event :
      ∀ᶠ n : ℕ in Filter.atTop,
        dir + ((n : ℝ)⁻¹ : ℝ) • x0 ∈ (ConvexCone.hull ℝ C : Set (Fin d → ℝ)) := by
    refine Filter.eventually_atTop.2 ?_
    refine ⟨1, ?_⟩
    intro n hn
    have hn_nat_pos : 0 < n := Nat.succ_le_iff.mp hn
    have hn_real_pos : 0 < (n : ℝ) := by
      exact_mod_cast hn_nat_pos
    have hn_real_nonneg : 0 ≤ (n : ℝ) := le_of_lt hn_real_pos
    have hxn : x0 + (n : ℝ) • dir ∈ C := hdir hx0 hn_real_nonneg
    have hxn_hull : x0 + (n : ℝ) • dir ∈ (ConvexCone.hull ℝ C : Set (Fin d → ℝ)) :=
      ConvexCone.subset_hull hxn
    have h_inv_pos : 0 < ((n : ℝ)⁻¹ : ℝ) := inv_pos.mpr hn_real_pos
    have hsmul_mem :
        ((n : ℝ)⁻¹ : ℝ) • (x0 + (n : ℝ) • dir) ∈
          (ConvexCone.hull ℝ C : Set (Fin d → ℝ)) :=
      (ConvexCone.hull ℝ C).smul_mem h_inv_pos hxn_hull
    have hn_real_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_real_pos
    have hrewrite :
        ((n : ℝ)⁻¹ : ℝ) • (x0 + (n : ℝ) • dir) =
          dir + ((n : ℝ)⁻¹ : ℝ) • x0 := by
      calc
        ((n : ℝ)⁻¹ : ℝ) • (x0 + (n : ℝ) • dir)
            = ((n : ℝ)⁻¹ : ℝ) • x0 +
                (((n : ℝ)⁻¹ : ℝ) * (n : ℝ)) • dir := by
                  simp [smul_add, smul_smul]
        _ = ((n : ℝ)⁻¹ : ℝ) • x0 + (1 : ℝ) • dir := by
              simp [hn_real_ne]
        _ = dir + ((n : ℝ)⁻¹ : ℝ) • x0 := by
              simp [add_comm]
    simpa [hrewrite] using hsmul_mem
  exact mem_closure_of_tendsto hlim hmem_event

/-- Helper for Theorem 19.6: closure of the convex cone generated by a finite mixed hull equals
the cone generated by the union of finite point and direction generators. -/
lemma helperForTheorem_19_6_closure_convexConeHull_eq_cone_of_finiteMixedData
    {d : ℕ} {S₀ S₁ : Set (Fin d → ℝ)}
    (hS₀fin : Set.Finite S₀)
    (hS₁fin : Set.Finite S₁)
    (hS₀ne : S₀.Nonempty) :
    closure ((ConvexCone.hull ℝ (mixedConvexHull (n := d) S₀ S₁) : Set (Fin d → ℝ))) =
      cone d (S₀ ∪ S₁) := by
  let M : Set (Fin d → ℝ) := mixedConvexHull (n := d) S₀ S₁
  have hM_nonempty : M.Nonempty := by
    rcases hS₀ne with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    exact helperForTheorem_19_6_points_subset_mixedConvexHull
      (d := d) (S₀ := S₀) (S₁ := S₁) hx
  have hcone_isConvexCone : IsConvexCone d (cone d (S₀ ∪ S₁)) := by
    simpa [cone_eq_convexConeGenerated (n := d) (S₁ := S₀ ∪ S₁)] using
      (isConvexCone_convexConeGenerated (n := d) (S₁ := S₀ ∪ S₁))
  have hcone_convex : Convex ℝ (cone d (S₀ ∪ S₁)) := hcone_isConvexCone.2
  have hcone_add :
      ∀ x ∈ cone d (S₀ ∪ S₁),
        ∀ y ∈ cone d (S₀ ∪ S₁), x + y ∈ cone d (S₀ ∪ S₁) :=
    isConvexCone_add_closed d (cone d (S₀ ∪ S₁)) hcone_isConvexCone
  have hS₀_subset_cone : S₀ ⊆ cone d (S₀ ∪ S₁) := by
    intro x hx
    have hxray_nonneg : x ∈ rayNonneg d (S₀ ∪ S₁) := by
      refine ⟨x, ?_, 1, by norm_num, ?_⟩
      · exact Or.inl hx
      · simp
    have hxray : x ∈ ray d (S₀ ∪ S₁) := (Set.mem_insert_iff).2 (Or.inr hxray_nonneg)
    simpa [cone, conv] using
      (subset_convexHull (𝕜 := ℝ) (s := ray d (S₀ ∪ S₁)) hxray)
  have hS₁_subset_cone : S₁ ⊆ cone d (S₀ ∪ S₁) := by
    intro x hx
    have hxray_nonneg : x ∈ rayNonneg d (S₀ ∪ S₁) := by
      refine ⟨x, ?_, 1, by norm_num, ?_⟩
      · exact Or.inr hx
      · simp
    have hxray : x ∈ ray d (S₀ ∪ S₁) := (Set.mem_insert_iff).2 (Or.inr hxray_nonneg)
    simpa [cone, conv] using
      (subset_convexHull (𝕜 := ℝ) (s := ray d (S₀ ∪ S₁)) hxray)
  have hrecedes :
      ∀ ⦃dir⦄, dir ∈ S₁ → ∀ ⦃x⦄, x ∈ cone d (S₀ ∪ S₁) →
        ∀ t : ℝ, 0 ≤ t → x + t • dir ∈ cone d (S₀ ∪ S₁) := by
    intro dir hdir x hx t ht
    by_cases ht0 : t = 0
    · subst ht0
      simpa using hx
    · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      have htdir : t • dir ∈ cone d (S₀ ∪ S₁) :=
        hcone_isConvexCone.1 dir (hS₁_subset_cone hdir) t htpos
      exact hcone_add x hx (t • dir) htdir
  have hM_subset_cone : M ⊆ cone d (S₀ ∪ S₁) := by
    refine mixedConvexHull_subset_of_convex_of_subset_of_recedes
      (n := d) (S₀ := S₀) (S₁ := S₁)
      (Ccand := cone d (S₀ ∪ S₁)) hcone_convex hS₀_subset_cone hrecedes
  have hcone_closed : IsClosed (cone d (S₀ ∪ S₁)) :=
    helperForTheorem_19_1_isClosed_cone_of_finite_generators
      (m := d) (T := S₀ ∪ S₁) (hS₀fin.union hS₁fin)
  have hsmul_mem_cone :
      ∀ (r : ℝ), 0 < r → ∀ x ∈ cone d (S₀ ∪ S₁), r • x ∈ cone d (S₀ ∪ S₁) := by
    intro r hr x hx
    exact hcone_isConvexCone.1 x hx r hr
  have hadd_mem_cone :
      ∀ x ∈ cone d (S₀ ∪ S₁), ∀ y ∈ cone d (S₀ ∪ S₁), x + y ∈ cone d (S₀ ∪ S₁) :=
    hcone_add
  let Ccone : ConvexCone ℝ (Fin d → ℝ) :=
    ConvexCone.mk (cone d (S₀ ∪ S₁)) hsmul_mem_cone hadd_mem_cone
  have hHullM_subset_cone :
      (ConvexCone.hull ℝ M : Set (Fin d → ℝ)) ⊆ cone d (S₀ ∪ S₁) := by
    have hHullM_subset_Ccone :
        (ConvexCone.hull ℝ M : Set (Fin d → ℝ)) ⊆ (Ccone : Set (Fin d → ℝ)) :=
      ConvexCone.hull_min (s := M) (C := Ccone) hM_subset_cone
    simpa [Ccone] using hHullM_subset_Ccone
  have hsubset_left :
      closure ((ConvexCone.hull ℝ M : Set (Fin d → ℝ))) ⊆ cone d (S₀ ∪ S₁) := by
    exact closure_minimal hHullM_subset_cone hcone_closed
  have hS₀_subset_closureHull :
      S₀ ⊆ closure ((ConvexCone.hull ℝ M : Set (Fin d → ℝ))) := by
    intro x hx
    have hxM : x ∈ M :=
      helperForTheorem_19_6_points_subset_mixedConvexHull
        (d := d) (S₀ := S₀) (S₁ := S₁) hx
    exact subset_closure (ConvexCone.subset_hull hxM)
  have hS₁_subset_closureHull :
      S₁ ⊆ closure ((ConvexCone.hull ℝ M : Set (Fin d → ℝ))) := by
    intro dir hdir
    have hdir_rec : dir ∈ Set.recessionCone M :=
      helperForTheorem_19_6_directions_subset_recessionCone_mixedConvexHull
        (d := d) (S₀ := S₀) (S₁ := S₁) hdir
    exact helperForTheorem_19_6_recessionDirection_mem_closure_convexConeHull_of_nonempty
      (d := d) (C := M) hM_nonempty hdir_rec
  have hUnion_subset_closureHull :
      S₀ ∪ S₁ ⊆ closure ((ConvexCone.hull ℝ M : Set (Fin d → ℝ))) := by
    intro x hx
    rcases hx with hx0 | hx1
    · exact hS₀_subset_closureHull hx0
    · exact hS₁_subset_closureHull hx1
  let Ccl : ConvexCone ℝ (Fin d → ℝ) := (ConvexCone.hull ℝ M).closure
  have hHullUnion_subset_closure :
      (ConvexCone.hull ℝ (S₀ ∪ S₁) : Set (Fin d → ℝ)) ⊆
        closure ((ConvexCone.hull ℝ M : Set (Fin d → ℝ))) := by
    have hHullUnion_subset_Ccl :
        (ConvexCone.hull ℝ (S₀ ∪ S₁) : Set (Fin d → ℝ)) ⊆ (Ccl : Set (Fin d → ℝ)) :=
      ConvexCone.hull_min (s := S₀ ∪ S₁) (C := Ccl) hUnion_subset_closureHull
    simpa [Ccl] using hHullUnion_subset_Ccl
  have hzero_mem_closureHullM :
      (0 : Fin d → ℝ) ∈ closure ((ConvexCone.hull ℝ M : Set (Fin d → ℝ))) := by
    rcases hM_nonempty with ⟨x, hxM⟩
    have hxHull : x ∈ (ConvexCone.hull ℝ M : Set (Fin d → ℝ)) := ConvexCone.subset_hull hxM
    have hlim_coeff0 :
        Filter.Tendsto (fun n : ℕ => ((n : ℝ)⁻¹ : ℝ)) Filter.atTop (𝓝 (0 : ℝ)) := by
      simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hlim0 :
        Filter.Tendsto (fun n : ℕ => ((n : ℝ)⁻¹ : ℝ) • x) Filter.atTop (𝓝 (0 : Fin d → ℝ)) := by
      have hsmul := hlim_coeff0.smul_const x
      simpa [zero_smul] using hsmul
    have hmem_event0 :
        ∀ᶠ n : ℕ in Filter.atTop, ((n : ℝ)⁻¹ : ℝ) • x ∈ (ConvexCone.hull ℝ M : Set (Fin d → ℝ)) := by
      refine Filter.eventually_atTop.2 ?_
      refine ⟨1, ?_⟩
      intro n hn
      have hn_nat_pos : 0 < n := Nat.succ_le_iff.mp hn
      have hn_real_pos : 0 < (n : ℝ) := by
        exact_mod_cast hn_nat_pos
      have h_inv_pos : 0 < ((n : ℝ)⁻¹ : ℝ) := inv_pos.mpr hn_real_pos
      exact (ConvexCone.hull ℝ M).smul_mem h_inv_pos hxHull
    exact mem_closure_of_tendsto hlim0 hmem_event0
  have hsubset_right :
      cone d (S₀ ∪ S₁) ⊆ closure ((ConvexCone.hull ℝ M : Set (Fin d → ℝ))) := by
    intro x hx
    have hx' : x ∈ convexConeGenerated d (S₀ ∪ S₁) := by
      simpa [cone_eq_convexConeGenerated (n := d) (S₁ := S₀ ∪ S₁)] using hx
    have hx'' : x = 0 ∨ x ∈ (ConvexCone.hull ℝ (S₀ ∪ S₁) : Set (Fin d → ℝ)) := by
      simpa [convexConeGenerated, Set.mem_insert_iff] using hx'
    rcases hx'' with rfl | hxHull
    · exact hzero_mem_closureHullM
    · exact hHullUnion_subset_closure hxHull
  have hEq : closure ((ConvexCone.hull ℝ M : Set (Fin d → ℝ))) = cone d (S₀ ∪ S₁) :=
    Set.Subset.antisymm hsubset_left hsubset_right
  simpa [M] using hEq

/-- Helper for Theorem 19.6: closure of the convex cone generated by a nonempty polyhedral set
is polyhedral. -/
lemma helperForTheorem_19_6_polyhedral_closure_convexConeHull_of_polyhedral
    {d : ℕ} {S : Set (Fin d → ℝ)}
    (hS_nonempty : S.Nonempty)
    (hS_polyhedral : IsPolyhedralConvexSet d S) :
    IsPolyhedralConvexSet d (closure ((ConvexCone.hull ℝ S : Set (Fin d → ℝ)))) := by
  have hS_conv : Convex ℝ S :=
    helperForTheorem_19_1_polyhedral_isConvex (n := d) (C := S) hS_polyhedral
  have hTFAE :
      [IsPolyhedralConvexSet d S,
        (IsClosed S ∧ {C' : Set (Fin d → ℝ) | IsFace (𝕜 := ℝ) S C'}.Finite),
        IsFinitelyGeneratedConvexSet d S].TFAE :=
    polyhedral_closed_finiteFaces_finitelyGenerated_equiv (n := d) (C := S) hS_conv
  have hS_fg : IsFinitelyGeneratedConvexSet d S :=
    (hTFAE.out 0 2).1 hS_polyhedral
  rcases hS_fg with ⟨S₀, S₁, hS₀fin, hS₁fin, hSeq⟩
  have hMixed_nonempty : (mixedConvexHull (n := d) S₀ S₁).Nonempty := by
    rcases hS_nonempty with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    simpa [hSeq] using hx
  have hS₀ne : S₀.Nonempty :=
    helperForTheorem_19_5_pointsNonempty_of_nonempty_mixedConvexHull
      (n := d) (S₀ := S₀) (S₁ := S₁) hMixed_nonempty
  have hclosure_eq :
      closure ((ConvexCone.hull ℝ S : Set (Fin d → ℝ))) = cone d (S₀ ∪ S₁) := by
    calc
      closure ((ConvexCone.hull ℝ S : Set (Fin d → ℝ))) =
          closure ((ConvexCone.hull ℝ (mixedConvexHull (n := d) S₀ S₁) : Set (Fin d → ℝ))) := by
            simp [hSeq]
      _ = cone d (S₀ ∪ S₁) :=
        helperForTheorem_19_6_closure_convexConeHull_eq_cone_of_finiteMixedData
          (d := d) (S₀ := S₀) (S₁ := S₁) hS₀fin hS₁fin hS₀ne
  have hcone_poly : IsPolyhedralConvexSet d (cone d (S₀ ∪ S₁)) :=
    helperForTheorem_19_1_cone_polyhedral_of_finite_generators
      (m := d) (T := S₀ ∪ S₁) (hS₀fin.union hS₁fin)
  simpa [hclosure_eq] using hcone_poly

/-- Helper for Theorem 19.6: transporting `convexHull` of a finite union through the
Euclidean coordinate equivalence. -/
lemma helperForTheorem_19_6_convexHull_iUnion_image_linearEquiv
    {n m : ℕ} {C : Fin (Nat.succ m) → Set (Fin n → ℝ)} :
    let eN : (Fin n → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
      (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm
    let CE : Fin (Nat.succ m) → Set (EuclideanSpace ℝ (Fin n)) :=
      fun i => eN '' C i
    eN '' (convexHull ℝ (⋃ i, C i)) = convexHull ℝ (⋃ i, CE i) := by
  intro eN CE
  calc
    eN '' (convexHull ℝ (⋃ i, C i)) = convexHull ℝ (eN '' (⋃ i, C i)) := by
      simpa using (LinearMap.image_convexHull (f := eN.toLinearMap) (s := ⋃ i, C i))
    _ = convexHull ℝ (⋃ i, CE i) := by
      congr 1
      simpa [CE] using (Set.image_iUnion (f := eN) (s := fun i => C i))

/-- Helper for Theorem 19.6: additive equivalences commute with finite Minkowski sums. -/
lemma helperForTheorem_19_6_image_finsetSum_addEquiv
    {α β ι : Type*}
    [AddCommMonoid α] [AddCommMonoid β] [Fintype ι]
    (e : α ≃+ β) (A : ι → Set α) :
    e '' (∑ i, A i) = ∑ i, (e '' A i) := by
  classical
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases (Set.mem_finset_sum (t := (Finset.univ : Finset ι)) (f := A) (a := x)).1 hx with
      ⟨z, hzmem, hzsum⟩
    refine
      (Set.mem_finset_sum (t := (Finset.univ : Finset ι)) (f := fun i => e '' A i) (a := e x)).2 ?_
    refine ⟨fun i => e (z i), ?_, ?_⟩
    · intro i hi
      exact ⟨z i, hzmem (i := i) hi, rfl⟩
    · simpa using congrArg e hzsum
  · intro hy
    rcases (Set.mem_finset_sum (t := (Finset.univ : Finset ι)) (f := fun i => e '' A i)
      (a := y)).1 hy with ⟨z, hzmem, hzsum⟩
    have hzpre : ∀ i, ∃ x, x ∈ A i ∧ e x = z i := by
      intro i
      rcases hzmem (i := i) (by simp) with ⟨x, hxA, hxz⟩
      exact ⟨x, hxA, hxz⟩
    choose x hxA hxz using hzpre
    have hxsum_mem : (∑ i, x i) ∈ ∑ i, A i := by
      refine (Set.mem_finset_sum (t := (Finset.univ : Finset ι)) (f := A) (a := ∑ i, x i)).2 ?_
      refine ⟨x, ?_, rfl⟩
      intro i hi
      exact hxA i
    refine ⟨∑ i, x i, hxsum_mem, ?_⟩
    calc
      e (∑ i, x i) = ∑ i, e (x i) := by simp
      _ = ∑ i, z i := by simp [hxz]
      _ = y := hzsum

/-- Helper for Theorem 19.6: additive equivalences commute with finite Minkowski sums under
preimage. -/
lemma helperForTheorem_19_6_preimage_finsetSum_addEquiv
    {α β ι : Type*}
    [AddCommMonoid α] [AddCommMonoid β] [Fintype ι]
    (e : α ≃+ β) (A : ι → Set β) :
    e ⁻¹' (∑ i, A i) = ∑ i, (e ⁻¹' A i) := by
  classical
  have hpreimage_eq_image :
      e ⁻¹' (∑ i, A i) = e.symm '' (∑ i, A i) := by
    ext x
    constructor
    · intro hx
      exact ⟨e x, hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  have hpreimage_eq_image_each :
      (fun i => e ⁻¹' A i) = (fun i => e.symm '' A i) := by
    funext i
    ext x
    constructor
    · intro hx
      exact ⟨e x, hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  calc
    e ⁻¹' (∑ i, A i) = e.symm '' (∑ i, A i) := hpreimage_eq_image
    _ = ∑ i, e.symm '' A i := by
      simpa using
        (helperForTheorem_19_6_image_finsetSum_addEquiv (e := e.symm) (A := A))
    _ = ∑ i, e ⁻¹' A i := by
      simp [hpreimage_eq_image_each]

/-- Helper for Theorem 19.6: the weighted branch union in the `tail` coordinate transports
through the Euclidean coordinate linear equivalence. -/
lemma helperForTheorem_19_6_image_weightedUnion_linearEquiv
    {n m : ℕ} {C : Fin (Nat.succ m) → Set (Fin n → ℝ)}
    (eN : (Fin n → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (lam : Fin (Nat.succ m) → ℝ) :
    eN ''
        (∑ i, (if lam i = 0 then Set.recessionCone (C i) else lam i • (C i))) =
      ∑ i,
        (if lam i = 0 then Set.recessionCone (eN '' C i) else lam i • (eN '' (C i))) := by
  have hbranch :
      ∀ i,
        eN '' (if lam i = 0 then Set.recessionCone (C i) else lam i • (C i)) =
          (if lam i = 0 then Set.recessionCone (eN '' C i) else lam i • (eN '' (C i))) := by
    intro i
    by_cases h0 : lam i = 0
    · simpa [h0] using
        (recessionCone_image_linearEquiv (e := eN) (C := C i)).symm
    · simp [h0]
  calc
    eN '' (∑ i, (if lam i = 0 then Set.recessionCone (C i) else lam i • (C i))) =
        ∑ i, eN '' (if lam i = 0 then Set.recessionCone (C i) else lam i • (C i)) := by
          simpa using
            (helperForTheorem_19_6_image_finsetSum_addEquiv
              (e := eN.toAddEquiv)
              (A := fun i => if lam i = 0 then Set.recessionCone (C i) else lam i • (C i)))
    _ = ∑ i,
          (if lam i = 0 then Set.recessionCone (eN '' C i) else lam i • (eN '' (C i))) := by
          simp [hbranch]

/-- Helper for Theorem 19.6: transporting the weighted finite union formula back through a linear
equivalence using preimage. -/
lemma helperForTheorem_19_6_preimage_weightedUnion_linearEquiv
    {n m : ℕ} {C : Fin (Nat.succ m) → Set (Fin n → ℝ)}
    (eN : (Fin n → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (lam : Fin (Nat.succ m) → ℝ) :
    eN ⁻¹'
        (∑ i,
          (if lam i = 0 then Set.recessionCone (eN '' C i) else lam i • (eN '' (C i)))) =
      ∑ i, (if lam i = 0 then Set.recessionCone (C i) else lam i • (C i)) := by
  have himage :=
    helperForTheorem_19_6_image_weightedUnion_linearEquiv
      (n := n) (m := m) (C := C) (eN := eN) (lam := lam)
  calc
    eN ⁻¹'
        (∑ i,
          (if lam i = 0 then Set.recessionCone (eN '' C i) else lam i • (eN '' (C i)))) =
      eN ⁻¹' (eN '' (∑ i, (if lam i = 0 then Set.recessionCone (C i) else lam i • (C i)))) := by
        simp [himage]
    _ = ∑ i, (if lam i = 0 then Set.recessionCone (C i) else lam i • (C i)) :=
      Set.preimage_image_eq _ eN.injective

/-- Helper for Theorem 19.6: linear equivalences transport convex-cone hulls through set image. -/
lemma helperForTheorem_19_6_convexConeHull_image_linearEquiv
    {α β : Type*}
    [AddCommMonoid α] [Module ℝ α]
    [AddCommMonoid β] [Module ℝ β]
    (e : α ≃ₗ[ℝ] β) (s : Set α) :
    e '' (ConvexCone.hull ℝ s : Set α) = (ConvexCone.hull ℝ (e '' s) : Set β) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hs_to : s ⊆ (ConvexCone.hull ℝ (e '' s)).comap e.toLinearMap := by
      intro x hx
      exact ConvexCone.subset_hull ⟨x, hx, rfl⟩
    have hhull_to :
        ConvexCone.hull ℝ s ≤ (ConvexCone.hull ℝ (e '' s)).comap e.toLinearMap :=
      ConvexCone.hull_min hs_to
    exact hhull_to hx
  · intro hy
    have himage_subset :
        e '' s ⊆ ((ConvexCone.hull ℝ s).map e.toLinearMap : Set β) := by
      rintro y ⟨x, hx, rfl⟩
      exact ⟨x, ConvexCone.subset_hull hx, rfl⟩
    have hhull_image :
        ConvexCone.hull ℝ (e '' s) ≤ (ConvexCone.hull ℝ s).map e.toLinearMap :=
      ConvexCone.hull_min himage_subset
    exact hhull_image hy

/-- Helper for Theorem 19.6: after casting `Fin.natAdd 1 i` from `Fin (1+n)` to `Fin (n+1)`,
it coincides with `Fin.succ i`. -/
lemma helperForTheorem_19_6_cast_natAdd_one_eq_succ
    {n : ℕ} (i : Fin n) :
    (Fin.cast (Nat.add_comm 1 n) (Fin.natAdd 1 i) : Fin (n + 1)) =
      Fin.succ i := by
  apply Fin.ext
  simp [Fin.natAdd, Fin.succ, Nat.add_comm]

/-- Helper for Theorem 19.6: the tail-coordinate function written with casted `Fin.natAdd 1`
agrees with the usual `Fin.succ` tail function. -/
lemma helperForTheorem_19_6_tail_cast_natAdd_eq_tail_succ
    {n : ℕ} (v : Fin (n + 1) → ℝ) :
    (fun i : Fin n =>
      v (Fin.cast (Nat.add_comm 1 n) (Fin.natAdd 1 i))) =
      (fun i : Fin n => v (Fin.succ i)) := by
  funext i
  rw [helperForTheorem_19_6_cast_natAdd_one_eq_succ]


end Section19
end Chap19
