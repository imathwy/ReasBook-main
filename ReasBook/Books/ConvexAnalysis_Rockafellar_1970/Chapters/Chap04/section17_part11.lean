/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yunfei Zhang, Yunxi Duan, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap04.section17_part8
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap04.section17_part10

open scoped BigOperators Pointwise
open Topology

section Chap04
section Section17

/-- A feasible cone prevents a nonpositive representation of the vertical vector. -/
lemma exists_pos_coeff_repr_vertical_of_feasible {n : Nat}
    {Sstar : Set ((Fin n → Real) × Real)} {x0 : Fin n → Real}
    (hx0 : x0 ∈ intersectionOfHalfspaces (n := n) Sstar)
    (v : Fin (n + 1) → (Fin n → Real) × Real) (a : Fin (n + 1) → Real)
    (hv : ∀ i, v i ∈ Sstar)
    (hEq : verticalVector n = ∑ i, a i • v i) :
    ∃ j, 0 < a j := by
  classical
  by_contra hpos
  have hle : ∀ i, a i ≤ 0 := by
    intro i
    by_contra hi
    exact hpos ⟨i, lt_of_not_ge hi⟩
  have hneg :
      -(verticalVector n) = ∑ i, (-a i) • v i := by
    calc
      -(verticalVector n) = -(∑ i, a i • v i) := by simp [hEq]
      _ = ∑ i, -(a i • v i) := by
        simp [Finset.sum_neg_distrib]
      _ = ∑ i, (-a i) • v i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simp
  have hlam : ∀ i, 0 ≤ -a i := by
    intro i
    exact neg_nonneg.mpr (hle i)
  have hineq :
      x0 ⬝ᵥ (∑ i, (-a i) • (v i).1) ≤ ∑ i, (-a i) * (v i).2 :=
    conicSum_snd_nonneg_of_mem_intersectionOfHalfspaces (n := n) (Sstar := Sstar)
      (x0 := x0) hx0 v (fun i => -a i) hv hlam
  have hfst : (∑ i, (-a i) • (v i).1) = 0 := by
    have hfst' := congrArg Prod.fst hneg
    simpa [fst_sum, verticalVector] using hfst'
  have hsnd : ∑ i, (-a i) * (v i).2 = -1 := by
    have hsnd' := congrArg Prod.snd hneg
    have hsnd'' : (-1 : Real) = ∑ i, (-a i) * (v i).2 := by
      simpa [snd_sum, verticalVector, mul_comm, mul_left_comm, mul_assoc] using hsnd'
    exact hsnd''.symm
  have hcontra : (0 : Real) ≤ -1 := by
    calc
      (0 : Real) = x0 ⬝ᵥ (∑ i, (-a i) • (v i).1) := by
        rw [hfst]
        simp
      _ ≤ ∑ i, (-a i) * (v i).2 := hineq
      _ = -1 := hsnd
  linarith

/-- Express the vertical vector using a linearly independent `(n + 1)`-tuple. -/
lemma verticalVector_eq_sum_smul_of_linIndep {n : Nat}
    (v : Fin (n + 1) → (Fin n → Real) × Real) (hv : LinearIndependent ℝ v) :
    ∃ a : Fin (n + 1) → Real, verticalVector n = ∑ i, a i • v i := by
  classical
  have hfin_fun : Module.finrank Real (Fin (n + 1) → Real) = n + 1 := by
    calc
      Module.finrank Real (Fin (n + 1) → Real) = Fintype.card (Fin (n + 1)) := by
        exact (Module.finrank_fintype_fun_eq_card (R := Real) (η := Fin (n + 1)))
      _ = n + 1 := by
        simp [Fintype.card_fin]
  have hfin : Module.finrank Real ((Fin n → Real) × Real) = n + 1 := by
    calc
      Module.finrank Real ((Fin n → Real) × Real) =
          Module.finrank Real (Fin (n + 1) → Real) := by
            exact (LinearEquiv.finrank_eq (prodLinearEquiv_append_coord (n := n)))
      _ = n + 1 := hfin_fun
  have hcard : Fintype.card (Fin (n + 1)) = Module.finrank Real ((Fin n → Real) × Real) := by
    calc
      Fintype.card (Fin (n + 1)) = n + 1 := Fintype.card_fin (n + 1)
      _ = Module.finrank Real ((Fin n → Real) × Real) := by symm; exact hfin
  let b : Module.Basis (Fin (n + 1)) Real ((Fin n → Real) × Real) :=
    basisOfLinearIndependentOfCardEqFinrank hv hcard
  refine ⟨fun i => (b.repr (verticalVector n)) i, ?_⟩
  have hsum := (Module.Basis.sum_repr b (verticalVector n))
  simpa [b, coe_basisOfLinearIndependentOfCardEqFinrank] using hsum.symm

/-- Shift a linearly independent conic sum along the vertical vector to zero a coefficient. -/
lemma reduce_linIndep_Sstar_rep_by_vertical_shift {n : Nat}
    {Sstar : Set ((Fin n → Real) × Real)} {x0 : Fin n → Real}
    (hx0 : x0 ∈ intersectionOfHalfspaces (n := n) Sstar)
    (v : Fin (n + 1) → (Fin n → Real) × Real) (hlin : LinearIndependent ℝ v)
    (hvS : ∀ i, v i ∈ Sstar) (c : Fin (n + 1) → Real) (hc : ∀ i, 0 ≤ c i) :
    ∃ (δ : Real), ∃ (c' : Fin (n + 1) → Real), ∃ j,
      0 ≤ δ ∧ (∀ i, 0 ≤ c' i) ∧ c' j = 0 ∧
        (∑ i, c i • v i) = δ • verticalVector n + ∑ i, c' i • v i := by
  classical
  rcases verticalVector_eq_sum_smul_of_linIndep (n := n) v hlin with ⟨a, hVert⟩
  rcases
      exists_pos_coeff_repr_vertical_of_feasible (n := n) (Sstar := Sstar) (x0 := x0) hx0 v a
        hvS hVert with ⟨j0, hj0⟩
  let s : Finset (Fin (n + 1)) := Finset.univ.filter fun i => 0 < a i
  have hs : s.Nonempty := by
    refine ⟨j0, ?_⟩
    simp [s, hj0]
  rcases Finset.exists_min_image s (fun i => c i / a i) hs with ⟨j, hjmem, hjmin⟩
  have hjpos : 0 < a j := by
    have hjmem' : j ∈ Finset.univ ∧ 0 < a j := by
      simpa [s] using hjmem
    exact hjmem'.2
  let δ : Real := c j / a j
  let c' : Fin (n + 1) → Real := fun i => c i - δ * a i
  have hδ : 0 ≤ δ := by
    exact div_nonneg (hc j) (le_of_lt hjpos)
  have hc' : ∀ i, 0 ≤ c' i := by
    intro i
    by_cases hi : 0 < a i
    ·
      have his : i ∈ s := by
        simp [s, hi]
      have hmin : δ ≤ c i / a i := by
        simpa [δ] using hjmin i his
      have hmul : δ * a i ≤ (c i / a i) * a i :=
        mul_le_mul_of_nonneg_right hmin (le_of_lt hi)
      have hdiv : (c i / a i) * a i = c i := by
        have hne : a i ≠ 0 := ne_of_gt hi
        field_simp [hne]
      have hmul' : δ * a i ≤ c i := by
        simpa [hdiv] using hmul
      exact sub_nonneg.mpr hmul'
    ·
      have hnonpos : a i ≤ 0 := le_of_not_gt hi
      have hmul : δ * a i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hδ hnonpos
      linarith [hc i, hmul]
  have hzero : c' j = 0 := by
    have hne : a j ≠ 0 := ne_of_gt hjpos
    have hzero' : c j - (c j / a j) * a j = (0 : Real) := by
      field_simp [hne]
      ring
    simpa [c', δ] using hzero'
  have hdelta_vert : δ • verticalVector n = ∑ i, (δ * a i) • v i := by
    calc
      δ • verticalVector n = δ • (∑ i, a i • v i) := by simp [hVert]
      _ = ∑ i, δ • (a i • v i) := by
        simpa using
          (Finset.smul_sum (r := δ) (s := (Finset.univ : Finset (Fin (n + 1))))
            (f := fun i => a i • v i))
      _ = ∑ i, (δ * a i) • v i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simp [smul_smul, mul_comm]
  have hsum :
      (∑ i, c i • v i) = δ • verticalVector n + ∑ i, c' i • v i := by
    calc
      ∑ i, c i • v i =
          ∑ i, (δ * a i + (c i - δ * a i)) • v i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hci : δ * a i + (c i - δ * a i) = c i := by ring
            rw [hci]
      _ = ∑ i, (δ * a i) • v i + ∑ i, (c i - δ * a i) • v i := by
            calc
              ∑ i, (δ * a i + (c i - δ * a i)) • v i =
                  ∑ i, ((δ * a i) • v i + (c i - δ * a i) • v i) := by
                    refine Finset.sum_congr rfl ?_
                    intro i hi
                    simpa using
                      (add_smul (δ * a i) (c i - δ * a i) (v i))
              _ = ∑ i, (δ * a i) • v i + ∑ i, (c i - δ * a i) • v i := by
                    simp [Finset.sum_add_distrib]
      _ = δ • verticalVector n + ∑ i, c' i • v i := by
            simp [hdelta_vert.symm, c']
  exact ⟨δ, c', j, hδ, hc', hzero, hsum⟩

/-- Drop a zero coefficient from a `Fin (n + 1)` sum via `succAbove`. -/
lemma sum_smul_succAbove_eq_of_zero {n : Nat}
    (v : Fin (n + 1) → (Fin n → Real) × Real) (c : Fin (n + 1) → Real)
    (j : Fin (n + 1)) (hj : c j = 0) :
    (∑ i, c i • v i) = ∑ i, c (j.succAbove i) • v (j.succAbove i) := by
  simpa [hj] using (Fin.sum_univ_succAbove (f := fun i => c i • v i) j)

/-- If one coefficient is zero, reindex the conic sum over `Fin n` by skipping that index. -/
lemma drop_zero_coeff_conicSum {n : Nat} {Sstar : Set ((Fin n → Real) × Real)}
    (v : Fin (n + 1) → (Fin n → Real) × Real) (c : Fin (n + 1) → Real)
    (j : Fin (n + 1)) (hj : c j = 0) (hv : ∀ i, v i ∈ Sstar) (hc : ∀ i, 0 ≤ c i) :
    ∃ (p : Fin n → (Fin n → Real) × Real) (lam : Fin n → Real),
      (∀ i, p i ∈ Sstar) ∧ (∀ i, 0 ≤ lam i) ∧
        (∑ i, c i • v i) = ∑ i, lam i • p i := by
  refine ⟨fun i => v (j.succAbove i), fun i => c (j.succAbove i), ?_, ?_, ?_⟩
  · intro i
    simpa using hv (j.succAbove i)
  · intro i
    exact hc (j.succAbove i)
  · simpa using (sum_smul_succAbove_eq_of_zero (n := n) v c j hj)

theorem mem_coneK_imp_exists_conicCombination_le {n : Nat}
    (Sstar : Set ((Fin n → Real) × Real)) (xStar : Fin n → Real) (muStar : Real)
    (hC_ne : intersectionOfHalfspaces (n := n) Sstar ≠ (∅ : Set (Fin n → Real))) :
    (xStar, muStar) ∈ coneK (n := n) Sstar →
      ∃ m : Nat, m ≤ n ∧
        ∃ (p : Fin m → (Fin n → Real) × Real) (lam0 : Real) (lam : Fin m → Real),
          (∀ i, p i ∈ Sstar) ∧ 0 ≤ lam0 ∧ (∀ i, 0 ≤ lam i) ∧
            (xStar, muStar) = lam0 • verticalVector n + ∑ i, lam i • p i := by
  intro hmem
  have hC_nonempty :
      (intersectionOfHalfspaces (n := n) Sstar).Nonempty := by
    exact Set.nonempty_iff_ne_empty.mpr hC_ne
  rcases hC_nonempty with ⟨x0, hx0⟩
  rcases
      mem_coneK_imp_exists_linIndep_nonnegLinearCombination_adjoinVertical_le (n := n)
        (Sstar := Sstar) (xStar := xStar) (muStar := muStar) hmem with
    ⟨k, hk, v, c, hv, hc, hEq, hlin⟩
  by_cases hk' : k ≤ n
  ·
    rcases
        split_adjoinVertical_conicCombination (n := n) (Sstar := Sstar) (v := v) (c := c) hv hc with
      ⟨m, hm, p, lam0, lam, hp, hlam0, hlam, hEq'⟩
    refine ⟨m, le_trans hm hk', p, lam0, lam, hp, hlam0, hlam, ?_⟩
    calc
      (xStar, muStar) = ∑ i, c i • v i := hEq
      _ = lam0 • verticalVector n + ∑ i, lam i • p i := hEq'
  ·
    have hk_lt : n < k := lt_of_not_ge hk'
    have hk_ge : n + 1 ≤ k := Nat.succ_le_iff.mpr hk_lt
    have hk_eq : k = n + 1 := le_antisymm hk hk_ge
    subst hk_eq
    classical
    by_cases hvert : ∃ j, v j = verticalVector n
    ·
      rcases hvert with ⟨j, hvj⟩
      refine ⟨n, le_rfl, (fun i => v (j.succAbove i)), c j,
        (fun i => c (j.succAbove i)), ?_, ?_, ?_, ?_⟩
      ·
        intro i
        have hmem := hv (j.succAbove i)
        have hne : v (j.succAbove i) ≠ verticalVector n := by
          intro hEqv
          have hidx : j.succAbove i = j := by
            exact (hlin.injective (by simpa [hvj] using hEqv))
          exact (Fin.succAbove_ne j i) hidx
        have hmem' :
            v (j.succAbove i) = verticalVector n ∨ v (j.succAbove i) ∈ Sstar := by
          simpa [adjoinVertical, Set.union_comm] using hmem
        rcases hmem' with hmemV | hmemS
        · exact (hne hmemV).elim
        · exact hmemS
      · exact hc j
      · intro i
        exact hc (j.succAbove i)
      ·
        calc
          (xStar, muStar) = ∑ i, c i • v i := hEq
          _ = c j • v j + ∑ i, c (j.succAbove i) • v (j.succAbove i) := by
                simpa using (Fin.sum_univ_succAbove (f := fun i => c i • v i) j)
          _ = c j • verticalVector n + ∑ i, c (j.succAbove i) • v (j.succAbove i) := by
                simp [hvj]
    ·
      -- TODO: use feasibility via `hx0` to reduce to at most `n` generators from `Sstar`.
      -- This is the "bottoms of simplices" argument for the remaining hard case.
      have hvS : ∀ i, v i ∈ Sstar := by
        intro i
        have hmem := hv i
        have hmem' : v i = verticalVector n ∨ v i ∈ Sstar := by
          simpa [adjoinVertical, Set.union_comm] using hmem
        rcases hmem' with hmemV | hmemS
        · exact (hvert ⟨i, hmemV⟩).elim
        · exact hmemS
      rcases
          reduce_linIndep_Sstar_rep_by_vertical_shift (n := n) (Sstar := Sstar) (x0 := x0) hx0 v
            hlin hvS c hc with
        ⟨δ, c', j, hδ, hc', hzero, hshift⟩
      rcases drop_zero_coeff_conicSum (n := n) (Sstar := Sstar) v c' j hzero hvS hc' with
        ⟨p', lam', hp', hlam', hsum⟩
      refine ⟨n, le_rfl, p', δ, lam', hp', hδ, hlam', ?_⟩
      calc
        (xStar, muStar) = ∑ i, c i • v i := hEq
        _ = δ • verticalVector n + ∑ i, c' i • v i := hshift
        _ = δ • verticalVector n + ∑ i, lam' i • p' i := by simp [hsum]

/-- Full dimensionality and a nonzero normal force the intersection of half-spaces to be nonempty. -/
lemma intersectionOfHalfspaces_ne_empty_of_full_dim {n : Nat}
    (Sstar : Set ((Fin n → Real) × Real))
    (hC_dim :
      Module.finrank Real
          (affineSpan Real (intersectionOfHalfspaces (n := n) Sstar)).direction = n)
    (r : HalfspaceRep n) :
    intersectionOfHalfspaces (n := n) Sstar ≠ (∅ : Set (Fin n → Real)) := by
  classical
  let C : Set (Fin n → Real) := intersectionOfHalfspaces (n := n) Sstar
  have hC_dim' :
      Module.finrank Real (affineSpan Real C).direction = n := by
    simpa [C] using hC_dim
  intro hC_empty
  have hspan : affineSpan Real C = ⊥ := (affineSpan_eq_bot (k := Real) (s := C)).2 hC_empty
  have hfin : Module.finrank Real (affineSpan Real C).direction = 0 := by
    simp [hspan]
  have hn0 : n = 0 := by
    have : (0 : Nat) = n := by
      simpa [hfin] using hC_dim'
    exact this.symm
  subst hn0
  have hxzero : r.xStar = 0 := by
    funext i
    exact (Fin.elim0 i)
  exact r.hxStar hxzero

/-- Containment in a half-space gives membership in the closure of `coneK`. -/
lemma halfspace_contains_intersectionOfHalfspaces_imp_mem_closure_coneK {n : Nat}
    (Sstar : Set ((Fin n → Real) × Real))
    (hC_ne : intersectionOfHalfspaces (n := n) Sstar ≠ (∅ : Set (Fin n → Real)))
    (r : HalfspaceRep n) :
    r.set ⊇ intersectionOfHalfspaces (n := n) Sstar →
      (r.xStar, r.muStar) ∈ closure (coneK (n := n) Sstar) := by
  classical
  let C : Set (Fin n → Real) := intersectionOfHalfspaces (n := n) Sstar
  intro hsup
  have hforall : ∀ x ∈ C, x ⬝ᵥ r.xStar ≤ r.muStar :=
    (halfspaceRep_set_superset_iff_forall_dot_le (C := C) (r := r)).1 hsup
  have hforall' : ∀ x ∈ C, dotProduct x r.xStar ≤ r.muStar := by
    intro x hx
    have hx' := hforall x hx
    simpa [dotProduct_comm, dotProduct_comm_bridge_for_supportFunction] using hx'
  have hle : supportFunctionEReal C r.xStar ≤ (r.muStar : EReal) :=
    (section13_supportFunctionEReal_le_coe_iff (C := C) (y := r.xStar) (μ := r.muStar)).2
      hforall'
  have hmem_epi :
      (r.xStar, r.muStar) ∈
        epigraph (S := (Set.univ : Set (Fin n → Real))) (supportFunctionEReal C) :=
    (mem_epigraph_univ_iff (f := supportFunctionEReal C)).2 hle
  have hcl :
      epigraph (S := (Set.univ : Set (Fin n → Real))) (supportFunctionEReal C) =
        closure (coneK (n := n) Sstar) := by
    rcases
        (by
            simpa [C] using
              (epigraph_supportFunction_eq_epigraph_convexFunctionClosure_eq_closure_epigraph_eq_closure_coneK
                (n := n) Sstar hC_ne)) with
      ⟨h1, h2, h3⟩
    exact h1.trans (h2.trans h3)
  simpa [hcl] using hmem_epi

/-- Full-dimensionality of `C` forces a point in the interior. -/
lemma exists_mem_interior_intersectionOfHalfspaces_of_full_dim {n : Nat}
    (Sstar : Set ((Fin n → Real) × Real))
    (hC_ne : intersectionOfHalfspaces (n := n) Sstar ≠ (∅ : Set (Fin n → Real)))
    (hC_dim :
      Module.finrank Real
          (affineSpan Real (intersectionOfHalfspaces (n := n) Sstar)).direction = n) :
    ∃ x, x ∈ interior (intersectionOfHalfspaces (n := n) Sstar) := by
  classical
  let C : Set (Fin n → Real) := intersectionOfHalfspaces (n := n) Sstar
  have hCconv : Convex ℝ C := convex_intersectionOfHalfspaces (n := n) Sstar
  have hC_nonempty : C.Nonempty := Set.nonempty_iff_ne_empty.mpr hC_ne
  have hfin : Module.finrank Real (Fin n → Real) = n := by
    calc
      Module.finrank Real (Fin n → Real) = Fintype.card (Fin n) := by
        exact (Module.finrank_fintype_fun_eq_card (R := Real) (η := Fin n))
      _ = n := by simp
  have hdir_top : (affineSpan Real C).direction = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    simpa [C, hfin] using hC_dim
  have hspan_nonempty : (affineSpan Real C : Set (Fin n → Real)).Nonempty := by
    rcases hC_nonempty with ⟨x, hx⟩
    exact ⟨x, (subset_affineSpan Real C) hx⟩
  have hspan_top : affineSpan Real C = ⊤ := by
    exact
      (AffineSubspace.direction_eq_top_iff_of_nonempty (s := affineSpan Real C) hspan_nonempty).1
        hdir_top
  have hinterior : (interior C).Nonempty := by
    exact (Convex.interior_nonempty_iff_affineSpan_eq_top (s := C) hCconv).2 hspan_top
  rcases hinterior with ⟨x, hx⟩
  exact ⟨x, hx⟩

/-- Interior points of a closed halfspace satisfy the strict inequality. -/
lemma mem_interior_halfspace_le_imp_dot_lt {n : Nat} {v : Fin n → Real} {μ : Real}
    {x : Fin n → Real} (hv : v ≠ 0)
    (hx : x ∈ interior {y : Fin n → Real | y ⬝ᵥ v ≤ μ}) :
    x ⬝ᵥ v < μ := by
  classical
  let f : (Fin n → Real) →ₗ[Real] Real :=
    { toFun := fun y => dotProduct y v
      map_add' := by intro y z; simp
      map_smul' := by intro a y; simp [smul_eq_mul] }
  have hsurj : Function.Surjective f := by
    classical
    obtain ⟨i, hvi⟩ : ∃ i, v i ≠ 0 := by
      by_contra h
      have hv0 : v = 0 := by
        funext j
        by_contra hvj
        exact h ⟨j, hvj⟩
      exact hv hv0
    intro t
    refine ⟨Pi.single i (t / v i), ?_⟩
    have hdot : dotProduct v (Pi.single i (t / v i)) = v i * (t / v i) := by
      simp [dotProduct_single]
    have hdot' : dotProduct (Pi.single i (t / v i)) v = v i * (t / v i) := by
      simp [dotProduct_comm, hdot]
    have hmul : v i * (t / v i) = t := by
      field_simp [hvi]
    simpa [f, hmul] using hdot'
  have hcont : Continuous f := LinearMap.continuous_of_finiteDimensional f
  have hopen : IsOpenMap f :=
    (LinearMap.isOpenMap_of_finiteDimensional (f := f) hsurj)
  have hpre :
      f ⁻¹' interior (Set.Iic μ) = interior (f ⁻¹' Set.Iic μ) :=
    (IsOpenMap.preimage_interior_eq_interior_preimage (f := f) hopen hcont (Set.Iic μ))
  have hx' : x ∈ f ⁻¹' interior (Set.Iic μ) := by
    have hx'' : x ∈ interior (f ⁻¹' Set.Iic μ) := by
      simpa [f, Set.preimage, Set.Iic] using hx
    simpa [hpre.symm] using hx''
  have hx'' : f x ∈ interior (Set.Iic μ) := by
    simpa [Set.preimage] using hx'
  have hx''' : f x ∈ Set.Iio μ := by
    simpa [interior_Iic] using hx''
  simpa [Set.Iio, f] using hx'''

/-- Interior points give strict inequalities for defining halfspaces. -/
lemma strict_dot_lt_of_mem_interior_intersectionOfHalfspaces {n : Nat}
    (Sstar : Set ((Fin n → Real) × Real))
    (hC_ne : intersectionOfHalfspaces (n := n) Sstar ≠ (∅ : Set (Fin n → Real)))
    {xbar : Fin n → Real}
    (hxbar : xbar ∈ interior (intersectionOfHalfspaces (n := n) Sstar))
    (hSstar0 : (0 : (Fin n → Real) × Real) ∉ Sstar) :
    ∀ p ∈ Sstar, dotProduct xbar p.1 < p.2 := by
  classical
  intro p hp
  by_cases hzero : p.1 = 0
  ·
    rcases (Set.nonempty_iff_ne_empty.mpr hC_ne) with ⟨x0, hx0⟩
    have hx0' : ∀ q ∈ Sstar, x0 ⬝ᵥ q.1 ≤ q.2 := by
      simpa [intersectionOfHalfspaces] using hx0
    have hle : (0 : Real) ≤ p.2 := by
      have := hx0' p hp
      simpa [hzero] using this
    have hpne : p ≠ 0 := by
      intro h0
      exact hSstar0 (by simpa [h0] using hp)
    have hp2ne : p.2 ≠ 0 := by
      intro hmu
      apply hpne
      ext <;> simp [hzero, hmu]
    have hpos : 0 < p.2 := lt_of_le_of_ne hle (by simpa [eq_comm] using hp2ne)
    simpa [hzero] using hpos
  ·
    let C : Set (Fin n → Real) := intersectionOfHalfspaces (n := n) Sstar
    have hsubset : C ⊆ {x : Fin n → Real | x ⬝ᵥ p.1 ≤ p.2} := by
      intro x hx
      have hx' : ∀ q ∈ Sstar, x ⬝ᵥ q.1 ≤ q.2 := by
        simpa [C, intersectionOfHalfspaces] using hx
      exact hx' p hp
    have hxbar' : xbar ∈ interior {x : Fin n → Real | x ⬝ᵥ p.1 ≤ p.2} :=
      (interior_mono hsubset) hxbar
    exact
      mem_interior_halfspace_le_imp_dot_lt (v := p.1) (μ := p.2) hzero hxbar'

/-- An interior point excludes the origin from `conv (adjoinVertical Sstar)`. -/
lemma zero_not_mem_conv_adjoinVertical_of_interior {n : Nat}
    (Sstar : Set ((Fin n → Real) × Real))
    (hC_ne : intersectionOfHalfspaces (n := n) Sstar ≠ (∅ : Set (Fin n → Real)))
    (hSstar0 : (0 : (Fin n → Real) × Real) ∉ Sstar)
    (hxbar : ∃ xbar, xbar ∈ interior (intersectionOfHalfspaces (n := n) Sstar)) :
    (0 : (Fin n → Real) × Real) ∉ convexHull ℝ (adjoinVertical (n := n) Sstar) := by
  classical
  rcases hxbar with ⟨xbar, hxbar⟩
  let D : Set ((Fin n → Real) × Real) := adjoinVertical (n := n) Sstar
  let U : Set ((Fin n → Real) × Real) := {q | dotProduct xbar q.1 - q.2 < 0}
  have hsubset : D ⊆ U := by
    intro q hq
    have hq' : q = verticalVector n ∨ q ∈ Sstar := by
      simpa [D, adjoinVertical, Set.mem_union, Set.mem_singleton_iff] using hq
    rcases hq' with hqV | hqS
    ·
      simp [U, hqV, verticalVector]
    ·
      have hstrict :
          dotProduct xbar q.1 < q.2 :=
        strict_dot_lt_of_mem_interior_intersectionOfHalfspaces (n := n) (Sstar := Sstar) hC_ne
          hxbar hSstar0 q hqS
      have : dotProduct xbar q.1 - q.2 < 0 := by linarith
      simpa [U] using this
  have hlin :
      IsLinearMap Real (fun q : (Fin n → Real) × Real => dotProduct xbar q.1 - q.2) := by
    refine ⟨?_, ?_⟩
    · intro q r
      simp [sub_eq_add_neg]
      ring
    · intro a q
      simp [smul_eq_mul, sub_eq_add_neg, mul_add]
  have hconvU : Convex Real U := by
    simpa [U] using (convex_halfSpace_lt (f := fun q : (Fin n → Real) × Real =>
      dotProduct xbar q.1 - q.2) hlin 0)
  have hconv : convexHull ℝ D ⊆ U := by
    simpa [D] using (convexHull_min hsubset hconvU)
  intro hmem
  have hmem' : (0 : (Fin n → Real) × Real) ∈ U := hconv hmem
  simp [U] at hmem'

/-- Linear equivalences commute with `convexHull`. -/
lemma convexHull_image_linearEquiv {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (e : E ≃ₗ[ℝ] F) (D : Set E) :
    e '' (convexHull ℝ D) = convexHull ℝ (e '' D) := by
  simpa using (LinearMap.image_convexHull (f := e.toLinearMap) (s := D))

/-- Linear equivalences commute with `ConvexCone.hull` on the level of sets. -/
lemma convexCone_hull_image_linearEquiv {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (e : E ≃ₗ[ℝ] F) (D : Set E) :
    e '' (ConvexCone.hull ℝ D : Set E) = (ConvexCone.hull ℝ (e '' D) : Set F) := by
  classical
  apply Set.Subset.antisymm
  ·
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hsubset :
        D ⊆
          (ConvexCone.comap e.toLinearMap (ConvexCone.hull ℝ (e '' D)) : Set E) := by
      intro d hd
      have hd' :
          e d ∈ (ConvexCone.hull ℝ (e '' D) : Set F) := by
        exact (ConvexCone.subset_hull (R := ℝ) (s := e '' D)) ⟨d, hd, rfl⟩
      simpa using hd'
    have hx' :
        x ∈
          (ConvexCone.comap e.toLinearMap (ConvexCone.hull ℝ (e '' D)) : Set E) :=
      (ConvexCone.hull_min (s := D)
          (C := ConvexCone.comap e.toLinearMap (ConvexCone.hull ℝ (e '' D))) hsubset) hx
    have hx'' :
        e x ∈ (ConvexCone.hull ℝ (e '' D) : Set F) := by
      simpa using
        (ConvexCone.mem_comap (f := e.toLinearMap) (C := ConvexCone.hull ℝ (e '' D))
            (x := x)).1 hx'
    exact hx''
  ·
    intro y hy
    have hy' :
        e.symm y ∈ (ConvexCone.hull ℝ D : Set E) := by
      have hsubset :
          (e '' D) ⊆
            (ConvexCone.comap e.symm.toLinearMap (ConvexCone.hull ℝ D) : Set F) := by
        intro d hd
        rcases hd with ⟨x, hx, rfl⟩
        have hx' : x ∈ (ConvexCone.hull ℝ D : Set E) :=
          (ConvexCone.subset_hull (R := ℝ) (s := D)) hx
        simpa using hx'
      have hy'' :
          y ∈
            (ConvexCone.comap e.symm.toLinearMap (ConvexCone.hull ℝ D) : Set F) :=
        (ConvexCone.hull_min (s := e '' D)
            (C := ConvexCone.comap e.symm.toLinearMap (ConvexCone.hull ℝ D)) hsubset) hy
      simpa using
        (ConvexCone.mem_comap (f := e.symm.toLinearMap) (C := ConvexCone.hull ℝ D)
            (x := y)).1 hy''
    exact ⟨e.symm y, hy', by simp⟩

/-- Taking the cone hull after `convexHull` does not change the cone. -/
lemma convexCone_hull_convexHull_eq {E : Type*}
    [AddCommGroup E] [Module ℝ E] (D : Set E) :
    (ConvexCone.hull ℝ (convexHull ℝ D) : Set E) = (ConvexCone.hull ℝ D : Set E) := by
  classical
  apply Set.Subset.antisymm
  ·
    have hsubset : convexHull ℝ D ⊆ (ConvexCone.hull ℝ D : Set E) := by
      refine convexHull_min (ConvexCone.subset_hull (R := ℝ) (s := D)) ?_
      exact (ConvexCone.hull ℝ D).convex
    intro x hx
    exact
      (ConvexCone.hull_min (s := convexHull ℝ D) (C := ConvexCone.hull ℝ D) hsubset) hx
  ·
    have hsubset :
        D ⊆ (ConvexCone.hull ℝ (convexHull ℝ D) : Set E) := by
      intro x hx
      have hx' : x ∈ convexHull ℝ D :=
        (subset_convexHull (𝕜 := ℝ) (s := D)) hx
      exact (ConvexCone.subset_hull (R := ℝ) (s := convexHull ℝ D)) hx'
    intro x hx
    exact
      (ConvexCone.hull_min (s := D)
          (C := ConvexCone.hull ℝ (convexHull ℝ D)) hsubset) hx

/-- The `prodLinearEquiv_append_coord` image of `coneK` is a generated cone. -/
lemma image_coneK_eq_convexConeGenerated {n : Nat}
    (Sstar : Set ((Fin n → Real) × Real)) :
    let e : ((Fin n → Real) × Real) ≃ₗ[ℝ] (Fin (n + 1) → Real) :=
      prodLinearEquiv_append_coord (n := n)
    let T : Set (Fin (n + 1) → Real) := e '' adjoinVertical (n := n) Sstar
    e '' (coneK (n := n) Sstar) = convexConeGenerated (n + 1) (convexHull ℝ T) := by
  classical
  intro e T
  have himage :
      e '' (coneK (n := n) Sstar) =
        Set.insert (0 : Fin (n + 1) → Real)
          (e '' (ConvexCone.hull Real (adjoinVertical (n := n) Sstar) :
            Set ((Fin n → Real) × Real))) := by
    simpa [coneK] using
      (Set.image_insert_eq (f := e) (a := (0 : (Fin n → Real) × Real))
        (s :=
          (ConvexCone.hull Real (adjoinVertical (n := n) Sstar) :
            Set ((Fin n → Real) × Real))))
  have hcone :
      e '' (ConvexCone.hull Real (adjoinVertical (n := n) Sstar) :
        Set ((Fin n → Real) × Real)) =
        (ConvexCone.hull Real T : Set (Fin (n + 1) → Real)) := by
    simpa [T] using
      (convexCone_hull_image_linearEquiv (e := e) (D := adjoinVertical (n := n) Sstar))
  have hcone' :
      (ConvexCone.hull Real T : Set (Fin (n + 1) → Real)) =
        (ConvexCone.hull Real (convexHull ℝ T) : Set (Fin (n + 1) → Real)) := by
    simpa using (convexCone_hull_convexHull_eq (D := T)).symm
  calc
    e '' (coneK (n := n) Sstar) =
        Set.insert (0 : Fin (n + 1) → Real)
          (ConvexCone.hull Real T : Set (Fin (n + 1) → Real)) := by
        simpa [hcone] using himage
    _ =
        Set.insert (0 : Fin (n + 1) → Real)
          (ConvexCone.hull Real (convexHull ℝ T) : Set (Fin (n + 1) → Real)) := by
        simp [hcone']
    _ = convexConeGenerated (n + 1) (convexHull ℝ T) := by
        simp [convexConeGenerated]

/-- Full-dimensionality and compactness of `Sstar` make `coneK` closed. -/
lemma isClosed_coneK_of_closed_bounded_full_dim {n : Nat}
    (Sstar : Set ((Fin n → Real) × Real)) (hSstar_ne : Sstar.Nonempty)
    (hSstar_closed : IsClosed Sstar) (hSstar_bdd : Bornology.IsBounded Sstar)
    (hSstar0 : (0 : (Fin n → Real) × Real) ∉ Sstar)
    (hC_ne : intersectionOfHalfspaces (n := n) Sstar ≠ (∅ : Set (Fin n → Real)))
    (hC_dim :
      Module.finrank Real
          (affineSpan Real (intersectionOfHalfspaces (n := n) Sstar)).direction = n) :
    IsClosed (coneK (n := n) Sstar) := by
  classical
  let e : ((Fin n → Real) × Real) ≃ₗ[ℝ] (Fin (n + 1) → Real) :=
    prodLinearEquiv_append_coord (n := n)
  let eCL : ((Fin n → Real) × Real) ≃L[ℝ] (Fin (n + 1) → Real) :=
    e.toContinuousLinearEquiv
  let D : Set ((Fin n → Real) × Real) := adjoinVertical (n := n) Sstar
  let T : Set (Fin (n + 1) → Real) := eCL '' D
  let C : Set (Fin (n + 1) → Real) := convexHull ℝ T
  have hD_closed : IsClosed D := by
    have hvert_closed :
        IsClosed ({verticalVector n} : Set ((Fin n → Real) × Real)) := isClosed_singleton
    simpa [D, adjoinVertical] using hSstar_closed.union hvert_closed
  have hD_bdd : Bornology.IsBounded D := by
    have hvert_bdd :
        Bornology.IsBounded ({verticalVector n} : Set ((Fin n → Real) × Real)) := by
      simp [Bornology.isBounded_singleton]
    have hunion : Bornology.IsBounded (Sstar ∪ {verticalVector n}) :=
      (Bornology.isBounded_union).2 ⟨hSstar_bdd, hvert_bdd⟩
    simpa [D, adjoinVertical] using hunion
  have hT_closed : IsClosed T := by
    have himage :
        eCL '' D = eCL.symm ⁻¹' D := by
      simpa using (ContinuousLinearEquiv.image_eq_preimage_symm (e := eCL) (s := D))
    have hpre : IsClosed (eCL.symm ⁻¹' D) := hD_closed.preimage eCL.symm.continuous
    have hclosed' : IsClosed (eCL '' D) := by
      simpa [himage] using hpre
    simpa [T] using hclosed'
  have hT_bdd : Bornology.IsBounded T := by
    simpa [T] using (eCL.lipschitz.isBounded_image hD_bdd)
  have hT_ne : T.Nonempty := by
    rcases hSstar_ne with ⟨p, hp⟩
    refine ⟨eCL p, ?_⟩
    exact ⟨p, by simp [D, adjoinVertical, hp], rfl⟩
  have hCne : C.Nonempty := by
    rcases hT_ne with ⟨t, ht⟩
    exact ⟨t, (subset_convexHull (𝕜 := Real) (s := T)) ht⟩
  have hC_conv : Convex Real C := by
    simpa [C] using (convex_convexHull (𝕜 := Real) (s := T))
  have hC_closed_bdd : IsClosed C ∧ Bornology.IsBounded C := by
    simpa [C, conv] using
      (isClosed_and_isBounded_conv_of_isClosed_and_isBounded (n := n + 1) (S := T) hT_closed
        hT_bdd)
  have hC_closed : IsClosed C := hC_closed_bdd.1
  have hC_bdd : Bornology.IsBounded C := hC_closed_bdd.2
  have hxbar :
      ∃ xbar, xbar ∈ interior (intersectionOfHalfspaces (n := n) Sstar) :=
    exists_mem_interior_intersectionOfHalfspaces_of_full_dim (n := n) (Sstar := Sstar) hC_ne
      hC_dim
  have hzero_not :
      (0 : (Fin n → Real) × Real) ∉ convexHull ℝ D := by
    simpa [D] using
      zero_not_mem_conv_adjoinVertical_of_interior (n := n) (Sstar := Sstar) hC_ne hSstar0 hxbar
  have hzero_not_T : (0 : Fin (n + 1) → Real) ∉ convexHull ℝ T := by
    intro h0
    have himage :
        e '' convexHull ℝ D = convexHull ℝ T := by
      simpa [T] using (convexHull_image_linearEquiv (e := eCL.toLinearEquiv) (D := D))
    have h0' : (0 : Fin (n + 1) → Real) ∈ e '' convexHull ℝ D := by
      simpa [himage] using h0
    rcases h0' with ⟨x, hx, hx0⟩
    have hx0' : x = 0 := by
      apply e.injective
      simpa using hx0
    have : (0 : (Fin n → Real) × Real) ∈ convexHull ℝ D := by
      simpa [hx0'] using hx
    exact hzero_not this
  have hC0 : (0 : Fin (n + 1) → Real) ∉ C := by
    simpa [C, conv] using hzero_not_T
  have hclosedK :
      IsClosed (convexConeGenerated (n + 1) C) :=
    closed_convexConeGenerated_of_bounded (n := n + 1) (C := C) hCne hC_closed hC_bdd hC_conv hC0
  have himage :
      e '' (coneK (n := n) Sstar) = convexConeGenerated (n + 1) C := by
    simpa [C, T, D] using
      (image_coneK_eq_convexConeGenerated (n := n) (Sstar := Sstar))
  have hpreimage :
      coneK (n := n) Sstar = (fun x => e x) ⁻¹' convexConeGenerated (n + 1) C := by
    ext x
    constructor
    · intro hx
      have hx' : e x ∈ e '' coneK (n := n) Sstar := ⟨x, hx, rfl⟩
      have hx'' : e x ∈ convexConeGenerated (n + 1) C := by
        simpa [himage] using hx'
      simpa using hx''
    · intro hx
      have hx' : e x ∈ convexConeGenerated (n + 1) C := by
        simpa using hx
      have hx'' : e x ∈ e '' coneK (n := n) Sstar := by
        simpa [himage] using hx'
      rcases hx'' with ⟨y, hy, hyeq⟩
      have hy' : y = x := e.injective hyeq
      simpa [hy'] using hy
  have hclosed_pre :
      IsClosed ((fun x => e x) ⁻¹' convexConeGenerated (n + 1) C) :=
    hclosedK.preimage eCL.continuous
  simpa [hpreimage] using hclosed_pre

/-- Theorem 17.2.11 (Dual Carath\'eodory for half-spaces (Theorem 17.3 / 2.10)), LaTeX label
`thm:dual_caratheodory`.

Let `S* ⊆ ℝ^{n+1}` be nonempty, closed, and bounded, and let
`C := intersectionOfHalfspaces S*` as in Definition 17.2.5 (`def:C`). Suppose `C` is
`n`-dimensional (i.e. `finrank (affineSpan ℝ C).direction = n`).

Fix `(x*, μ*) ∈ ℝ^{n+1}` with `x* ≠ 0` and consider the half-space
`H = {x ∈ ℝⁿ | ⟪x, x*⟫ ≤ μ*}`. Then `H ⊇ C` if and only if there exist
`(xᵢ*, μᵢ*) ∈ S*` and coefficients `λᵢ ≥ 0` for `i = 1, …, m`, with `m ≤ n`, such that

`∑ i, λᵢ • xᵢ* = x*` and `∑ i, λᵢ * μᵢ* ≤ μ*`. -/
theorem halfspaceRep_set_superset_intersectionOfHalfspaces_iff_exists_dual_caratheodory
    {n : Nat} (Sstar : Set ((Fin n → Real) × Real)) (hSstar_ne : Sstar.Nonempty)
    (hSstar_closed : IsClosed Sstar) (hSstar_bdd : Bornology.IsBounded Sstar)
    (hSstar0 : (0 : (Fin n → Real) × Real) ∉ Sstar)
    (hC_dim :
      Module.finrank Real
          (affineSpan Real (intersectionOfHalfspaces (n := n) Sstar)).direction = n)
    (r : HalfspaceRep n) :
    r.set ⊇ intersectionOfHalfspaces (n := n) Sstar ↔
      ∃ m : Nat, m ≤ n ∧
        ∃ (p : Fin m → (Fin n → Real) × Real) (lam : Fin m → Real),
          (∀ i, p i ∈ Sstar) ∧ (∀ i, 0 ≤ lam i) ∧
            (∑ i, lam i • (p i).1 = r.xStar) ∧ (∑ i, lam i * (p i).2 ≤ r.muStar) := by
  classical
  let C : Set (Fin n → Real) := intersectionOfHalfspaces (n := n) Sstar
  have hC_ne : C ≠ (∅ : Set (Fin n → Real)) :=
    intersectionOfHalfspaces_ne_empty_of_full_dim (n := n) (Sstar := Sstar) hC_dim r
  constructor
  · intro hsup
    have hmem_closure :
        (r.xStar, r.muStar) ∈ closure (coneK (n := n) Sstar) :=
      halfspace_contains_intersectionOfHalfspaces_imp_mem_closure_coneK (n := n)
        (Sstar := Sstar) hC_ne r hsup
    have hclosedK : IsClosed (coneK (n := n) Sstar) :=
      isClosed_coneK_of_closed_bounded_full_dim (n := n) (Sstar := Sstar) hSstar_ne
        hSstar_closed hSstar_bdd hSstar0 hC_ne hC_dim
    have hmemK : (r.xStar, r.muStar) ∈ coneK (n := n) Sstar := by
      simpa [hclosedK.closure_eq] using hmem_closure
    rcases
        mem_coneK_imp_exists_conicCombination_le (n := n) (Sstar := Sstar) (xStar := r.xStar)
          (muStar := r.muStar) hC_ne hmemK with
      ⟨m, hm, p, lam0, lam, hp, hlam0, hlam, hEq⟩
    have hcomp :
        r.xStar = ∑ i, lam i • (p i).1 ∧ r.muStar ≥ ∑ i, lam i * (p i).2 :=
      conicCombination_components (n := n) (xStar := r.xStar) (muStar := r.muStar) (p := p)
        (lam0 := lam0) (lam := lam) hlam0 hEq
    rcases hcomp with ⟨hx, hmu⟩
    refine ⟨m, hm, p, lam, hp, hlam, ?_, ?_⟩
    · exact hx.symm
    · linarith [hmu]
  · rintro ⟨m, hm, p, lam, hp, hlam, hx, hmu⟩
    have hforall : ∀ x ∈ C, x ⬝ᵥ r.xStar ≤ r.muStar := by
      intro x hxC
      have hineq :
          x ⬝ᵥ (∑ i, lam i • (p i).1) ≤ ∑ i, lam i * (p i).2 :=
        conicSum_snd_nonneg_of_mem_intersectionOfHalfspaces (n := n) (Sstar := Sstar)
          (x0 := x) hxC p lam hp hlam
      have hineq' : x ⬝ᵥ r.xStar ≤ ∑ i, lam i * (p i).2 := by
        simpa [hx] using hineq
      exact le_trans hineq' hmu
    exact (halfspaceRep_set_superset_iff_forall_dot_le (C := C) (r := r)).2 hforall

/-- Theorem 17.3. Let `S* ⊆ ℝ^{n+1}` be nonempty, closed, and bounded, and let

`C = {x ∈ ℝⁿ | ∀ (x*, μ*) ∈ S*, ⟪x, x*⟫ ≤ μ*}`.

Assume the convex set `C` is `n`-dimensional (here: `finrank (affineSpan ℝ C).direction = n`).
Fix a half-space `H = {x ∈ ℝⁿ | ⟪x, x*⟫ ≤ μ*}` with `x* ≠ 0` (represented as `r : HalfspaceRep n`).

Then `H ⊇ C` if and only if there exist points `(xᵢ*, μᵢ*) ∈ S*` and coefficients `λᵢ ≥ 0`,
`i = 1, …, m`, with `m ≤ n`, such that `∑ i, λᵢ • xᵢ* = x*` and `∑ i, λᵢ * μᵢ* ≤ μ*`. -/
theorem dualCaratheodory_halfspace_contains_intersectionOfHalfspaces_iff
    {n : Nat} (Sstar : Set ((Fin n → Real) × Real)) (hSstar_ne : Sstar.Nonempty)
    (hSstar_closed : IsClosed Sstar) (hSstar_bdd : Bornology.IsBounded Sstar)
    (hSstar0 : (0 : (Fin n → Real) × Real) ∉ Sstar)
    (hC_dim :
      Module.finrank Real
          (affineSpan Real (intersectionOfHalfspaces (n := n) Sstar)).direction = n)
    (r : HalfspaceRep n) :
    r.set ⊇ intersectionOfHalfspaces (n := n) Sstar ↔
      ∃ m : Nat, m ≤ n ∧
        ∃ (p : Fin m → (Fin n → Real) × Real) (lam : Fin m → Real),
          (∀ i, p i ∈ Sstar) ∧ (∀ i, 0 ≤ lam i) ∧
            (∑ i, lam i • (p i).1 = r.xStar) ∧ (∑ i, lam i * (p i).2 ≤ r.muStar) := by
  simpa using
    (halfspaceRep_set_superset_intersectionOfHalfspaces_iff_exists_dual_caratheodory
        (n := n) (Sstar := Sstar) hSstar_ne hSstar_closed hSstar_bdd hSstar0 hC_dim r)

/-- A conic-combination certificate forces a finite intersection to lie in the target half-space. -/
lemma iInter_halfspaces_subset_halfspaceRep_of_conicCombination {n m : Nat}
    (r : HalfspaceRep n) (p : Fin m → (Fin n → Real) × Real) (lam : Fin m → Real)
    (hlam : ∀ i, 0 ≤ lam i)
    (hx : (∑ i, lam i • (p i).1) = r.xStar)
    (hmu : (∑ i, lam i * (p i).2) ≤ r.muStar) :
    (⋂ i : Fin m, {x : Fin n → Real | x ⬝ᵥ (p i).1 ≤ (p i).2}) ⊆ r.set := by
  classical
  intro x hxmem
  have hx' : ∀ i, x ⬝ᵥ (p i).1 ≤ (p i).2 := by
    have hx'' : ∀ i, x ∈ {x : Fin n → Real | x ⬝ᵥ (p i).1 ≤ (p i).2} := by
      simpa [Set.mem_iInter] using hxmem
    intro i
    simpa using hx'' i
  have hle_i : ∀ i, lam i * (x ⬝ᵥ (p i).1) ≤ lam i * (p i).2 := by
    intro i
    exact mul_le_mul_of_nonneg_left (hx' i) (hlam i)
  have hsum :
      ∑ i, lam i * (x ⬝ᵥ (p i).1) ≤ ∑ i, lam i * (p i).2 := by
    refine Finset.sum_le_sum ?_
    intro i hi
    exact hle_i i
  have hdot :
      x ⬝ᵥ (∑ i, lam i • (p i).1) = ∑ i, lam i * (x ⬝ᵥ (p i).1) := by
    calc
      x ⬝ᵥ (∑ i, lam i • (p i).1) = ∑ i, x ⬝ᵥ lam i • (p i).1 := by
        simpa using
          (dotProduct_sum (u := x) (s := (Finset.univ : Finset (Fin m)))
            (v := fun i => lam i • (p i).1))
      _ = ∑ i, lam i * (x ⬝ᵥ (p i).1) := by
        simp [dotProduct_smul, smul_eq_mul]
  have hineq :
      x ⬝ᵥ (∑ i, lam i • (p i).1) ≤ ∑ i, lam i * (p i).2 := by
    simpa [hdot] using hsum
  have hineq' : x ⬝ᵥ r.xStar ≤ ∑ i, lam i * (p i).2 := by
    simpa [hx] using hineq
  have hineq'' : x ⬝ᵥ r.xStar ≤ r.muStar := le_trans hineq' hmu
  simpa [HalfspaceRep.set] using hineq''

/-- Pad a finite family of half-spaces without changing the intersection inclusion. -/
lemma exists_fin_n_family_padding_iInter_subset {n m : Nat} {α β : Type}
    (hm : m ≤ n) (p : Fin m → α) (a0 : α)
    (P : α → Prop) (H : α → Set β) (R : Set β)
    (hp : ∀ i, P (p i)) (ha0 : P a0)
    (hsubset : (⋂ i : Fin m, H (p i)) ⊆ R) :
    ∃ q : Fin n → α, (∀ i, P (q i)) ∧ (⋂ i : Fin n, H (q i)) ⊆ R := by
  classical
  let q : Fin n → α := fun i =>
    if h : (i.1 < m) then p ⟨i.1, h⟩ else a0
  have hqP : ∀ i, P (q i) := by
    intro i
    by_cases h : (i.1 < m)
    ·
      have := hp ⟨i.1, h⟩
      simpa [q, h] using this
    ·
      simpa [q, h] using ha0
  refine ⟨q, hqP, ?_⟩
  intro x hx
  have hx' : ∀ i : Fin n, x ∈ H (q i) := by
    simpa [Set.mem_iInter] using hx
  have hx_m : x ∈ ⋂ i : Fin m, H (p i) := by
    refine Set.mem_iInter.mpr ?_
    intro j
    have hxj : x ∈ H (q (Fin.castLE hm j)) := hx' (Fin.castLE hm j)
    have hqcast : q (Fin.castLE hm j) = p j := by
      simp [q]
    simpa [hqcast] using hxj
  exact hsubset hx_m

/-- The full intersection of half-spaces is contained in any finite sub-intersection. -/
lemma intersectionOfHalfspaces_subset_iInter_of_mem {n : Nat}
    (Sstar : Set ((Fin n → Real) × Real)) (p : Fin n → (Fin n → Real) × Real)
    (hp : ∀ i, p i ∈ Sstar) :
    intersectionOfHalfspaces (n := n) Sstar ⊆
      (⋂ i : Fin n, {x : Fin n → Real | x ⬝ᵥ (p i).1 ≤ (p i).2}) := by
  intro x hx
  have hx' : ∀ q ∈ Sstar, x ⬝ᵥ q.1 ≤ q.2 := by
    simpa [intersectionOfHalfspaces] using hx
  refine Set.mem_iInter.mpr ?_
  intro i
  have hineq := hx' (p i) (hp i)
  simpa using hineq

/-- Corollary 17.2.12 (Equivalent intersection formulation), LaTeX label `cor:intersection_form`.

In the setting of Theorem 17.2.11 (`thm:dual_caratheodory`), the condition
`intersectionOfHalfspaces S* ⊆ H` is equivalent to the existence of `n` (not necessarily
distinct) half-spaces

`Hᵢ = {x ∈ ℝⁿ | ⟪x, xᵢ*⟫ ≤ μᵢ*}` with `(xᵢ*, μᵢ*) ∈ S*`

such that `H₁ ∩ ··· ∩ Hₙ ⊆ H`. -/
theorem halfspaceRep_set_superset_intersectionOfHalfspaces_iff_exists_fin_n_halfspaces_iInter_subset
    {n : Nat} (Sstar : Set ((Fin n → Real) × Real)) (hSstar_ne : Sstar.Nonempty)
    (hSstar_closed : IsClosed Sstar) (hSstar_bdd : Bornology.IsBounded Sstar)
    (hSstar0 : (0 : (Fin n → Real) × Real) ∉ Sstar)
    (hC_dim :
      Module.finrank Real
          (affineSpan Real (intersectionOfHalfspaces (n := n) Sstar)).direction = n)
    (r : HalfspaceRep n) :
    r.set ⊇ intersectionOfHalfspaces (n := n) Sstar ↔
      ∃ p : Fin n → (Fin n → Real) × Real,
        (∀ i, p i ∈ Sstar) ∧
          (⋂ i : Fin n, {x : Fin n → Real | x ⬝ᵥ (p i).1 ≤ (p i).2}) ⊆ r.set := by
  classical
  constructor
  · intro hsup
    rcases hSstar_ne with ⟨p0, hp0⟩
    rcases
        (halfspaceRep_set_superset_intersectionOfHalfspaces_iff_exists_dual_caratheodory
            (n := n) (Sstar := Sstar) ⟨p0, hp0⟩ hSstar_closed hSstar_bdd hSstar0 hC_dim r).1
          hsup with
      ⟨m, hm, p, lam, hp, hlam, hx, hmu⟩
    have hsubset :
        (⋂ i : Fin m, {x : Fin n → Real | x ⬝ᵥ (p i).1 ≤ (p i).2}) ⊆ r.set :=
      iInter_halfspaces_subset_halfspaceRep_of_conicCombination (r := r) (p := p) (lam := lam)
        hlam hx hmu
    rcases
        exists_fin_n_family_padding_iInter_subset (n := n) (m := m) (hm := hm) (p := p) (a0 := p0)
          (P := fun q => q ∈ Sstar)
          (H := fun q => {x : Fin n → Real | x ⬝ᵥ q.1 ≤ q.2}) (R := r.set) hp hp0 hsubset with
      ⟨q, hqmem, hqsubset⟩
    exact ⟨q, hqmem, hqsubset⟩
  · rintro ⟨p, hp, hsubset⟩
    have hsubset' :
        intersectionOfHalfspaces (n := n) Sstar ⊆
          (⋂ i : Fin n, {x : Fin n → Real | x ⬝ᵥ (p i).1 ≤ (p i).2}) :=
      intersectionOfHalfspaces_subset_iInter_of_mem (n := n) (Sstar := Sstar) p hp
    exact Set.Subset.trans hsubset' hsubset

/-- Corollary 17.3.1 (Equivalent intersection formulation), LaTeX label
`cor:intersection_form_page11`.

Assume the hypotheses of Theorem 17.3 (`thm:dual_caratheodory`). Then the condition that the
intersection `intersectionOfHalfspaces S*` is contained in the half-space under consideration
`H = r.set` is equivalent to the existence of `n` (not necessarily distinct) half-spaces
`H i = {x | ⟪x, x i*⟫ ≤ μ i*}` with `(x i*, μ i*) ∈ S*` such that
`⋂ i, H i ⊆ H`. -/
theorem halfspaceRep_set_superset_intersectionOfHalfspaces_iff_exists_fin_n_halfspaces_iInter_subset_page11
    {n : Nat} (Sstar : Set ((Fin n → Real) × Real)) (hSstar_ne : Sstar.Nonempty)
    (hSstar_closed : IsClosed Sstar) (hSstar_bdd : Bornology.IsBounded Sstar)
    (hSstar0 : (0 : (Fin n → Real) × Real) ∉ Sstar)
    (hC_dim :
      Module.finrank Real
          (affineSpan Real (intersectionOfHalfspaces (n := n) Sstar)).direction = n)
    (r : HalfspaceRep n) :
    r.set ⊇ intersectionOfHalfspaces (n := n) Sstar ↔
      ∃ p : Fin n → (Fin n → Real) × Real,
        (∀ i, p i ∈ Sstar) ∧
          (⋂ i : Fin n, {x : Fin n → Real | x ⬝ᵥ (p i).1 ≤ (p i).2}) ⊆ r.set := by
  simpa using
    (halfspaceRep_set_superset_intersectionOfHalfspaces_iff_exists_fin_n_halfspaces_iInter_subset
        (n := n) (Sstar := Sstar) hSstar_ne hSstar_closed hSstar_bdd hSstar0 hC_dim r)

end Section17
end Chap04
