/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yunxi Duan, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section06_part2

noncomputable section
open scoped Pointwise

section Chap02
section Section06

/-- The relative interior of a convex set is convex. -/
lemma convex_euclideanRelativeInterior (n : Nat) (C : Set (EuclideanSpace Real (Fin n)))
    (hC : Convex Real C) : Convex Real (euclideanRelativeInterior n C) := by
  refine (convex_iff_segment_subset).2 ?_
  intro x hx y hy z hz
  rcases hz with ⟨a, b, ha, hb, hab, rfl⟩
  by_cases hb1 : b = 1
  · subst hb1
    have ha0 : a = 0 := by linarith [hab]
    simpa [ha0] using hy
  · have hri_subset : euclideanRelativeInterior n C ⊆ C :=
      (euclideanRelativeInterior_subset_closure n C).1
    have hC_subset : C ⊆ closure C :=
      (euclideanRelativeInterior_subset_closure n C).2
    have hy_closure : y ∈ closure C := hC_subset (hri_subset hy)
    have hb_le : b ≤ 1 := by linarith [ha, hab]
    have hb_lt : b < 1 := lt_of_le_of_ne hb_le hb1
    have ha_eq : a = 1 - b := by linarith [hab]
    have hcomb :
        (1 - b) • x + b • y ∈ euclideanRelativeInterior n C :=
      euclideanRelativeInterior_convex_combination_mem n C hC x y hx hy_closure b hb hb_lt
    simpa [ha_eq] using hcomb

/-- The affine span of the closure equals the affine span of the set. -/
lemma affineSpan_closure_eq (n : Nat) (C : Set (EuclideanSpace Real (Fin n))) :
    affineSpan Real (closure C) = affineSpan Real C := by
  refine le_antisymm ?_ ?_
  · have hsub : closure C ⊆ (affineSpan Real C : Set (EuclideanSpace Real (Fin n))) := by
      intro x hx
      exact mem_affineSpan_of_mem_closure (n := n) (C := C) hx
    exact (affineSpan_le (k := Real) (s := closure C) (Q := affineSpan Real C)).2 hsub
  · exact affineSpan_mono Real (subset_closure)

/-- The intrinsic interior is contained in the Euclidean relative interior. -/
lemma intrinsicInterior_subset_euclideanRelativeInterior (n : Nat)
    (C : Set (EuclideanSpace Real (Fin n))) :
    intrinsicInterior ℝ C ⊆ euclideanRelativeInterior n C := by
  classical
  intro x hx
  let A : AffineSubspace Real (EuclideanSpace Real (Fin n)) := affineSpan Real C
  let sA : Set A := ((↑) : A → EuclideanSpace Real (Fin n)) ⁻¹' C
  rcases (mem_intrinsicInterior.mp hx) with ⟨y, hy, rfl⟩
  have hyA : (y : EuclideanSpace Real (Fin n)) ∈
      (A : Set (EuclideanSpace Real (Fin n))) := y.property
  have hsA_nhds : sA ∈ nhds y := (mem_interior_iff_mem_nhds.mp hy)
  rcases (Metric.mem_nhds_iff.mp hsA_nhds) with ⟨ε, hε, hball⟩
  have hε0 : 0 < ε / 2 := by linarith
  refine ⟨by simp, ε / 2, hε0, ?_⟩
  intro z hz
  have hclosed :
      (fun z => (y : EuclideanSpace Real (Fin n)) + z) '' ((ε / 2) • euclideanUnitBall n) =
        Metric.closedBall (y : EuclideanSpace Real (Fin n)) (ε / 2) := by
    simpa using
      (translate_smul_unitBall_eq_closedBall n (y : EuclideanSpace Real (Fin n)) (ε / 2) hε0)
  have hz' :
      z ∈ Metric.closedBall (y : EuclideanSpace Real (Fin n)) (ε / 2) ∩
        (A : Set (EuclideanSpace Real (Fin n))) := by
    simpa [hclosed] using hz
  rcases hz' with ⟨hzball, hzA⟩
  have hzball' :
      z ∈ Metric.ball (y : EuclideanSpace Real (Fin n)) ε := by
    have hsubset :
        Metric.closedBall (y : EuclideanSpace Real (Fin n)) (ε / 2) ⊆
          Metric.ball (y : EuclideanSpace Real (Fin n)) ε := by
      exact Metric.closedBall_subset_ball (by linarith)
    exact hsubset hzball
  have hzA' : (⟨z, hzA⟩ : A) ∈ Metric.ball y ε := by
    simpa using hzball'
  have hzC : (⟨z, hzA⟩ : A) ∈ sA := hball hzA'
  simpa [sA] using hzC

/-- The affine span of the intrinsic interior equals the affine span of a nonempty convex set. -/
lemma affineSpan_intrinsicInterior_eq (n : Nat)
    (C : Set (EuclideanSpace Real (Fin n))) (hC : Convex Real C) (hCne : C.Nonempty) :
    affineSpan Real (intrinsicInterior ℝ C) = affineSpan Real C := by
  classical
  let A : AffineSubspace Real (EuclideanSpace Real (Fin n)) := affineSpan Real C
  let sA : Set A := ((↑) : A → EuclideanSpace Real (Fin n)) ⁻¹' C
  have hAne :
      (A : Set (EuclideanSpace Real (Fin n))).Nonempty := by
    simpa [A] using (hCne.affineSpan (k := Real))
  haveI : Nonempty A := Set.nonempty_coe_sort.mpr hAne
  have hri_ne : (intrinsicInterior ℝ C).Nonempty :=
    Set.Nonempty.intrinsicInterior hC hCne
  have hinterior_ne : (interior sA).Nonempty := by
    rcases hri_ne with ⟨x, hx⟩
    rcases (mem_intrinsicInterior.mp hx) with ⟨y, hy, rfl⟩
    exact ⟨y, hy⟩
  have hspanA :
      affineSpan Real (interior sA) = (⊤ : AffineSubspace Real A) :=
    (IsOpen.affineSpan_eq_top (isOpen_interior) hinterior_ne)
  have hmap :
      affineSpan Real (intrinsicInterior ℝ C) =
        (affineSpan Real (interior sA)).map A.subtype := by
    have hmap' := (AffineSubspace.map_span (k := Real) (f := A.subtype) (s := interior sA))
    simpa [intrinsicInterior, sA, A, AffineSubspace.coe_subtype] using hmap'.symm
  calc
    affineSpan Real (intrinsicInterior ℝ C)
        = (affineSpan Real (interior sA)).map A.subtype := hmap
    _ = (⊤ : AffineSubspace Real A).map A.subtype := by simp [hspanA]
    _ = A := by
      ext x
      simp

/-- Theorem 6.2: Let `C` be a convex set in `R^n`. Then `cl C` and `ri C` are convex sets
having the same affine hull (hence the same dimension) as `C`. In particular, `ri C ≠ ∅`
if `C ≠ ∅`. -/
theorem euclideanRelativeInterior_closure_convex_affineSpan (n : Nat)
    (C : Set (EuclideanSpace Real (Fin n))) (hC : Convex Real C) :
    Convex Real (closure C) ∧
      Convex Real (euclideanRelativeInterior n C) ∧
      affineSpan Real (closure C) = affineSpan Real C ∧
      affineSpan Real (euclideanRelativeInterior n C) = affineSpan Real C ∧
      (C.Nonempty → (euclideanRelativeInterior n C).Nonempty) := by
  have hconv_closure : Convex Real (closure C) := convex_closure_of_convex n C hC
  have hconv_ri : Convex Real (euclideanRelativeInterior n C) :=
    convex_euclideanRelativeInterior n C hC
  have haff_closure : affineSpan Real (closure C) = affineSpan Real C :=
    affineSpan_closure_eq n C
  have hri_subset : intrinsicInterior ℝ C ⊆ euclideanRelativeInterior n C :=
    intrinsicInterior_subset_euclideanRelativeInterior n C
  have haff_ri : affineSpan Real (euclideanRelativeInterior n C) = affineSpan Real C := by
    by_cases hCne : C.Nonempty
    · have haff_intr :
        affineSpan Real (intrinsicInterior ℝ C) = affineSpan Real C :=
        affineSpan_intrinsicInterior_eq n C hC hCne
      have hmono :
          affineSpan Real (intrinsicInterior ℝ C) ≤
            affineSpan Real (euclideanRelativeInterior n C) :=
        affineSpan_mono Real hri_subset
      have hC_le : affineSpan Real C ≤ affineSpan Real (euclideanRelativeInterior n C) := by
        simpa [haff_intr] using hmono
      have hri_subset_C : euclideanRelativeInterior n C ⊆ C :=
        (euclideanRelativeInterior_subset_closure n C).1
      have hri_le : affineSpan Real (euclideanRelativeInterior n C) ≤ affineSpan Real C :=
        affineSpan_mono Real hri_subset_C
      exact le_antisymm hri_le hC_le
    · have hCempty : C = ∅ := by
        simpa [Set.not_nonempty_iff_eq_empty] using hCne
      have hri_empty : euclideanRelativeInterior n C = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have : x ∈ C := (euclideanRelativeInterior_subset_closure n C).1 hx
        simp [hCempty] at this
      have hri_empty' : euclideanRelativeInterior n ∅ = ∅ := by
        simpa [hCempty] using hri_empty
      simp [hCempty, hri_empty']
  have hri_nonempty : C.Nonempty → (euclideanRelativeInterior n C).Nonempty := by
    intro hCne
    exact
      (Set.Nonempty.intrinsicInterior hC hCne).mono
        (intrinsicInterior_subset_euclideanRelativeInterior n C)
  exact ⟨hconv_closure, hconv_ri, haff_closure, haff_ri, hri_nonempty⟩

/-- For a nonempty convex set, `cl C` is contained in `cl (ri C)`. -/
lemma euclidean_closure_subset_closure_relativeInterior_of_nonempty (n : Nat)
    (C : Set (EuclideanSpace Real (Fin n))) (hC : Convex Real C) (hCne : C.Nonempty) :
    closure C ⊆ closure (euclideanRelativeInterior n C) := by
  intro y hy
  have hri_nonempty : (euclideanRelativeInterior n C).Nonempty :=
    (euclideanRelativeInterior_closure_convex_affineSpan n C hC).2.2.2.2 hCne
  rcases hri_nonempty with ⟨x, hx⟩
  refine
    (Metric.mem_closure_iff (α := EuclideanSpace Real (Fin n))
        (a := y) (s := euclideanRelativeInterior n C)).2 ?_
  intro ε hε
  set t : Real := dist (α := EuclideanSpace Real (Fin n)) x y /
    (dist (α := EuclideanSpace Real (Fin n)) x y + ε)
  have hdist : 0 ≤ dist x y := dist_nonneg
  have hden : 0 < dist x y + ε := by
    linarith [hdist, hε]
  have ht0 : 0 ≤ t := by
    exact div_nonneg hdist (le_of_lt hden)
  have ht1 : t < 1 := by
    have hnum : dist x y < dist x y + ε := by linarith [hε]
    have h := (div_lt_one hden).2 hnum
    simpa [t] using h
  have hz_mem :
      (1 - t) • x + t • y ∈ euclideanRelativeInterior n C :=
    euclideanRelativeInterior_convex_combination_mem n C hC x y hx hy t ht0 ht1
  have hdist :
      dist ((1 - t) • x + t • y) y = ‖1 - t‖ * dist x y := by
    simpa [AffineMap.lineMap_apply_module] using (dist_lineMap_right x y t)
  have h1t_nonneg : 0 ≤ 1 - t := sub_nonneg.mpr (le_of_lt ht1)
  have h1t_eq : 1 - t = ε / (dist x y + ε) := by
    have hden' : dist x y + ε ≠ 0 := by linarith [hdist, hε]
    calc
      1 - t = (dist x y + ε - dist x y) / (dist x y + ε) := by
        simpa [t] using (one_sub_div (a := dist x y) (b := dist x y + ε) hden')
      _ = ε / (dist x y + ε) := by simp
  have hratio_lt : dist x y / (dist x y + ε) < 1 := by
    simpa [t] using ht1
  have hdist_lt : dist ((1 - t) • x + t • y) y < ε := by
    have hεpos : 0 < ε := hε
    have h1t_norm : ‖1 - t‖ = 1 - t := by
      simpa using (Real.norm_of_nonneg h1t_nonneg)
    calc
      dist ((1 - t) • x + t • y) y
          = ‖1 - t‖ * dist x y := hdist
      _ = (1 - t) * dist x y := by simp [h1t_norm]
      _ = (ε / (dist x y + ε)) * dist x y := by simp [h1t_eq]
      _ = ε * (dist x y / (dist x y + ε)) := by
          simp [div_eq_mul_inv, mul_comm, mul_left_comm]
      _ < ε := by
          have h := (mul_lt_mul_of_pos_left hratio_lt hεpos)
          simpa using h
  have hdist_lt' : dist y ((1 - t) • x + t • y) < ε := by
    simpa [dist_comm] using hdist_lt
  exact ⟨(1 - t) • x + t • y, hz_mem, hdist_lt'⟩

/-- The relative interior is monotone with respect to closure. -/
lemma euclideanRelativeInterior_subset_relativeInterior_closure (n : Nat)
    (C : Set (EuclideanSpace Real (Fin n))) :
    euclideanRelativeInterior n C ⊆ euclideanRelativeInterior n (closure C) := by
  intro x hx
  rcases hx with ⟨hx_aff, ε, hε, hxsub⟩
  refine ⟨?_, ε, hε, ?_⟩
  · simpa [affineSpan_closure_eq n C] using hx_aff
  · intro y hy
    have hy' :
        y ∈ ((fun y => x + y) '' (ε • euclideanUnitBall n)) ∩
          (affineSpan Real C : Set (EuclideanSpace Real (Fin n))) := by
      simpa [affineSpan_closure_eq n C] using hy
    exact subset_closure (hxsub hy')

/-- For a nonempty convex set, `ri (cl C)` is contained in `ri C`. -/
lemma euclideanRelativeInterior_closure_subset_relativeInterior (n : Nat)
    (C : Set (EuclideanSpace Real (Fin n))) (hC : Convex Real C) (hCne : C.Nonempty) :
    euclideanRelativeInterior n (closure C) ⊆ euclideanRelativeInterior n C := by
  classical
  intro z hz
  have hri_nonempty : (euclideanRelativeInterior n C).Nonempty :=
    (euclideanRelativeInterior_closure_convex_affineSpan n C hC).2.2.2.2 hCne
  rcases hri_nonempty with ⟨x, hx⟩
  by_cases hxz : z = x
  · simpa [hxz] using hx
  have hx_ri : x ∈ euclideanRelativeInterior n C := hx
  rcases hx_ri with ⟨hx_aff, -, -, -⟩
  rcases hz with ⟨hz_aff, ε, hε, hzsub⟩
  set δ : Real := ε / (‖z - x‖ + ε)
  set μ : Real := 1 + δ
  set y : EuclideanSpace Real (Fin n) := AffineMap.lineMap x z μ
  have hδpos : 0 < δ := by
    have hdist : 0 ≤ ‖(z - x : EuclideanSpace Real (Fin n))‖ := by
      simp
    have hden : 0 < ‖z - x‖ + ε := by linarith [hdist, hε]
    exact div_pos hε hden
  have hμpos : 0 < μ := by linarith [hδpos]
  have hμne : μ ≠ 0 := ne_of_gt hμpos
  have hx_aff' : x ∈ affineSpan Real (closure C) := by
    simpa [affineSpan_closure_eq n C] using hx_aff
  have hy_aff : y ∈ affineSpan Real (closure C) := by
    have h :=
      AffineMap.lineMap_mem (Q := affineSpan Real (closure C))
        (p₀ := x) (p₁ := z) μ hx_aff' hz_aff
    simpa [y] using h
  have hy_vsub : y - z = δ • (z - x) := by
    have hy_vsub' : y - z = (1 - μ) • (x - z) := by
      simpa [y, vsub_eq_sub] using
        (AffineMap.lineMap_vsub_right (p₀ := x) (p₁ := z) (c := μ))
    have h1μ : 1 - μ = -δ := by
      simp [μ]
    have hsub : x - z = -(z - x) := by
      simp
    calc
      y - z = (1 - μ) • (x - z) := hy_vsub'
      _ = (-δ) • (x - z) := by simp [h1μ]
      _ = -(δ • (x - z)) := by
            simp
      _ = δ • (z - x) := by
            have hsmul : δ • (-(z - x)) = -(δ • (z - x)) := by
              simpa using (smul_neg δ (z - x))
            calc
              -(δ • (x - z)) = -(δ • (-(z - x))) := by rw [hsub]
              _ = -(-(δ • (z - x))) := by rw [hsmul]
              _ = δ • (z - x) := by simp
  have hnorm : ‖y - z‖ ≤ ε := by
    have hratio_lt : ‖z - x‖ / (‖z - x‖ + ε) < 1 := by
      have hdist : 0 ≤ ‖(z - x : EuclideanSpace Real (Fin n))‖ := by
        simp
      have hden : 0 < ‖z - x‖ + ε := by linarith [hdist, hε]
      have hnum : ‖z - x‖ < ‖z - x‖ + ε := by linarith [hε]
      have h := (div_lt_one hden).2 hnum
      simpa using h
    have hratio_le : ‖z - x‖ / (‖z - x‖ + ε) ≤ 1 := le_of_lt hratio_lt
    have hεnonneg : 0 ≤ ε := le_of_lt hε
    have hδnonneg : 0 ≤ δ := le_of_lt hδpos
    have hnorm_smul : ‖δ • (z - x)‖ = δ * ‖z - x‖ := by
      simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hδnonneg]
    have hcalc : δ * ‖z - x‖ = ε * (‖z - x‖ / (‖z - x‖ + ε)) := by
      simp [δ, div_eq_mul_inv, mul_comm, mul_left_comm]
    calc
      ‖y - z‖ = ‖δ • (z - x)‖ := by simp [hy_vsub]
      _ = δ * ‖z - x‖ := hnorm_smul
      _ = ε * (‖z - x‖ / (‖z - x‖ + ε)) := hcalc
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hratio_le hεnonneg
      _ = ε := by simp
  have hy_ball :
      y ∈ (fun t => z + t) '' (ε • euclideanUnitBall n) := by
    refine ⟨y - z, ?_, ?_⟩
    · exact mem_smul_unitBall_of_norm_le hε hnorm
    · simp [sub_eq_add_neg, add_comm]
  have hy_closure : y ∈ closure C := by
    have hy_in :
        y ∈ ((fun t => z + t) '' (ε • euclideanUnitBall n)) ∩
          (affineSpan Real (closure C) : Set (EuclideanSpace Real (Fin n))) := by
      exact ⟨hy_ball, hy_aff⟩
    exact hzsub hy_in
  have hz_lineMap : AffineMap.lineMap x y μ⁻¹ = z := by
    simp [y, hμne]
  have hz_eq : (1 - μ⁻¹) • x + μ⁻¹ • y = z := by
    simpa [AffineMap.lineMap_apply_module] using hz_lineMap
  have ht0 : 0 ≤ μ⁻¹ := by
    exact inv_nonneg.mpr (le_of_lt hμpos)
  have ht1 : μ⁻¹ < 1 := by
    have hμ1 : 1 < μ := by linarith [hδpos]
    exact inv_lt_one_of_one_lt₀ hμ1
  have hz_mem :
      (1 - μ⁻¹) • x + μ⁻¹ • y ∈ euclideanRelativeInterior n C :=
    euclideanRelativeInterior_convex_combination_mem n C hC x y hx hy_closure μ⁻¹ ht0 ht1
  simpa [hz_eq] using hz_mem

/-- Theorem 6.3: For any convex set `C` in `R^n`,
`cl (ri C) = cl C` and `ri (cl C) = ri C`. -/
theorem euclidean_closure_relativeInterior_eq_and_relativeInterior_closure_eq (n : Nat)
    (C : Set (EuclideanSpace Real (Fin n))) (hC : Convex Real C) :
    closure (euclideanRelativeInterior n C) = closure C ∧
      euclideanRelativeInterior n (closure C) = euclideanRelativeInterior n C := by
  by_cases hCne : C.Nonempty
  · have hcl_subset :
        closure (euclideanRelativeInterior n C) ⊆ closure C :=
      closure_mono (euclideanRelativeInterior_subset_closure n C).1
    have hcl_superset :
        closure C ⊆ closure (euclideanRelativeInterior n C) :=
      euclidean_closure_subset_closure_relativeInterior_of_nonempty n C hC hCne
    have hcl_eq : closure (euclideanRelativeInterior n C) = closure C :=
      le_antisymm hcl_subset hcl_superset
    have hri_subset :
        euclideanRelativeInterior n C ⊆ euclideanRelativeInterior n (closure C) :=
      euclideanRelativeInterior_subset_relativeInterior_closure n C
    have hri_superset :
        euclideanRelativeInterior n (closure C) ⊆ euclideanRelativeInterior n C :=
      euclideanRelativeInterior_closure_subset_relativeInterior n C hC hCne
    have hri_eq : euclideanRelativeInterior n (closure C) = euclideanRelativeInterior n C :=
      le_antisymm hri_superset hri_subset
    exact ⟨hcl_eq, hri_eq⟩
  · have hCempty : C = ∅ := by
      simpa [Set.not_nonempty_iff_eq_empty] using hCne
    have hri_empty : euclideanRelativeInterior n C = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hxC : x ∈ C := (euclideanRelativeInterior_subset_closure n C).1 hx
      simp [hCempty] at hxC
    have hri_empty' : euclideanRelativeInterior n ∅ = ∅ := by
      simpa [hCempty] using hri_empty
    have hri_closure_empty : euclideanRelativeInterior n (closure C) = ∅ := by
      simpa [hCempty] using hri_empty'
    have hcl_eq : closure (euclideanRelativeInterior n C) = closure C := by
      simp [hCempty, hri_empty']
    have hri_eq : euclideanRelativeInterior n (closure C) = euclideanRelativeInterior n C := by
      simp [hCempty, hri_empty']
    exact ⟨hcl_eq, hri_eq⟩

/-- Closure equality for convex sets yields equality of relative interiors. -/
lemma euclideanRelativeInterior_eq_of_closure_eq (n : Nat)
    (C1 C2 : Set (EuclideanSpace Real (Fin n))) (hC1 : Convex Real C1)
    (hC2 : Convex Real C2) :
    closure C1 = closure C2 →
      euclideanRelativeInterior n C1 = euclideanRelativeInterior n C2 := by
  intro hcl
  have hri1 :
      euclideanRelativeInterior n (closure C1) = euclideanRelativeInterior n C1 :=
    (euclidean_closure_relativeInterior_eq_and_relativeInterior_closure_eq n C1 hC1).2
  have hri2 :
      euclideanRelativeInterior n (closure C2) = euclideanRelativeInterior n C2 :=
    (euclidean_closure_relativeInterior_eq_and_relativeInterior_closure_eq n C2 hC2).2
  calc
    euclideanRelativeInterior n C1
        = euclideanRelativeInterior n (closure C1) := by
          simpa using hri1.symm
    _ = euclideanRelativeInterior n (closure C2) := by simp [hcl]
    _ = euclideanRelativeInterior n C2 := hri2

/-- Relative interior equality for convex sets yields equality of closures. -/
lemma euclidean_closure_eq_of_relativeInterior_eq (n : Nat)
    (C1 C2 : Set (EuclideanSpace Real (Fin n))) (hC1 : Convex Real C1)
    (hC2 : Convex Real C2) :
    euclideanRelativeInterior n C1 = euclideanRelativeInterior n C2 →
      closure C1 = closure C2 := by
  intro hri
  have hcl1 : closure (euclideanRelativeInterior n C1) = closure C1 :=
    (euclidean_closure_relativeInterior_eq_and_relativeInterior_closure_eq n C1 hC1).1
  have hcl2 : closure (euclideanRelativeInterior n C2) = closure C2 :=
    (euclidean_closure_relativeInterior_eq_and_relativeInterior_closure_eq n C2 hC2).1
  calc
    closure C1 = closure (euclideanRelativeInterior n C1) := by
      simpa using hcl1.symm
    _ = closure (euclideanRelativeInterior n C2) := by simp [hri]
    _ = closure C2 := hcl2

/-- Closure equality yields a relative interior and closure sandwich. -/
lemma euclidean_between_of_closure_eq (n : Nat)
    (C1 C2 : Set (EuclideanSpace Real (Fin n))) (hC1 : Convex Real C1)
    (hC2 : Convex Real C2) :
    closure C1 = closure C2 →
      (euclideanRelativeInterior n C1 ⊆ C2 ∧ C2 ⊆ closure C1) := by
  intro hcl
  have hri_eq :
      euclideanRelativeInterior n C1 = euclideanRelativeInterior n C2 :=
    euclideanRelativeInterior_eq_of_closure_eq n C1 C2 hC1 hC2 hcl
  have hri_sub : euclideanRelativeInterior n C2 ⊆ C2 :=
    (euclideanRelativeInterior_subset_closure n C2).1
  have hC2_sub : C2 ⊆ closure C2 :=
    (euclideanRelativeInterior_subset_closure n C2).2
  refine ⟨?_, ?_⟩
  · intro x hx
    have hx' : x ∈ euclideanRelativeInterior n C2 := by
      simpa [hri_eq] using hx
    exact hri_sub hx'
  · intro x hx
    have hx' : x ∈ closure C2 := hC2_sub hx
    simpa [hcl] using hx'

/-- A relative interior and closure sandwich yields equality of closures. -/
lemma euclidean_closure_eq_of_between (n : Nat)
    (C1 C2 : Set (EuclideanSpace Real (Fin n))) (hC1 : Convex Real C1) :
    (euclideanRelativeInterior n C1 ⊆ C2 ∧ C2 ⊆ closure C1) →
      closure C1 = closure C2 := by
  intro hbetween
  rcases hbetween with ⟨hri_sub, hC2_sub⟩
  have hcl1 : closure (euclideanRelativeInterior n C1) = closure C1 :=
    (euclidean_closure_relativeInterior_eq_and_relativeInterior_closure_eq n C1 hC1).1
  have hcl_le : closure C1 ⊆ closure C2 := by
    have hri_cl : closure (euclideanRelativeInterior n C1) ⊆ closure C2 :=
      closure_mono hri_sub
    simpa [hcl1] using hri_cl
  have hcl_ge : closure C2 ⊆ closure C1 := by
    have hcl : closure C2 ⊆ closure (closure C1) :=
      closure_mono hC2_sub
    simpa [closure_closure] using hcl
  exact le_antisymm hcl_le hcl_ge

/-- Corollary 6.3.1: Let `C1` and `C2` be convex sets in `R^n`. Then
`cl C1 = cl C2` if and only if `ri C1 = ri C2`. These conditions are equivalent to
`ri C1 ⊆ C2 ⊆ cl C1`. -/
theorem euclidean_closure_eq_iff_relativeInterior_eq_and_between (n : Nat)
    (C1 C2 : Set (EuclideanSpace Real (Fin n))) (hC1 : Convex Real C1)
    (hC2 : Convex Real C2) :
    (closure C1 = closure C2 ↔ euclideanRelativeInterior n C1 = euclideanRelativeInterior n C2) ∧
      (closure C1 = closure C2 ↔
        (euclideanRelativeInterior n C1 ⊆ C2 ∧ C2 ⊆ closure C1)) := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · exact euclideanRelativeInterior_eq_of_closure_eq n C1 C2 hC1 hC2
    · exact euclidean_closure_eq_of_relativeInterior_eq n C1 C2 hC1 hC2
  · refine ⟨?_, ?_⟩
    · exact euclidean_between_of_closure_eq n C1 C2 hC1 hC2
    · exact euclidean_closure_eq_of_between n C1 C2 hC1

/-- Corollary 6.3.2. If `C` is a convex set in `R^n`, then every open set which meets `cl C`
also meets `ri C`. -/
theorem euclidean_open_meets_closure_meets_relativeInterior (n : Nat)
    (C U : Set (EuclideanSpace Real (Fin n))) (hC : Convex Real C)
    (hU : IsOpen U) :
    (U ∩ closure C).Nonempty → (U ∩ euclideanRelativeInterior n C).Nonempty := by
  intro hmeet
  rcases hmeet with ⟨x, hxU, hxcl⟩
  have hcl : closure (euclideanRelativeInterior n C) = closure C :=
    (euclidean_closure_relativeInterior_eq_and_relativeInterior_closure_eq n C hC).1
  have hmeet' : (closure (euclideanRelativeInterior n C) ∩ U).Nonempty := by
    have hxcl' : x ∈ closure (euclideanRelativeInterior n C) := by
      simpa [hcl] using hxcl
    exact ⟨x, hxcl', hxU⟩
  have hmeet'' : (euclideanRelativeInterior n C ∩ U).Nonempty :=
    (closure_inter_open_nonempty_iff (s := euclideanRelativeInterior n C) (t := U) hU).1 hmeet'
  rcases hmeet'' with ⟨y, hyri, hyU⟩
  exact ⟨y, hyU, hyri⟩

/-- A subset of the relative boundary has affine span contained in the ambient affine span. -/
lemma affineSpan_le_of_subset_relativeBoundary (n : Nat)
    (C1 C2 : Set (EuclideanSpace Real (Fin n)))
    (hC1sub : C1 ⊆ euclideanRelativeBoundary n C2) :
    affineSpan Real C1 ≤ affineSpan Real C2 := by
  have hsubset : C1 ⊆ closure C2 := by
    intro x hx
    exact (hC1sub hx).1
  have hspan : affineSpan Real C1 ≤ affineSpan Real (closure C2) :=
    affineSpan_mono Real hsubset
  simpa [affineSpan_closure_eq n C2] using hspan

/-- Equal direction finrank and nonempty inclusion forces equality of affine spans. -/
lemma affineSpan_eq_of_nonempty_of_finrank_eq (n : Nat)
    (C1 C2 : Set (EuclideanSpace Real (Fin n))) (hC1ne : C1.Nonempty)
    (hspan : affineSpan Real C1 ≤ affineSpan Real C2)
    (hfin :
      Module.finrank Real (affineSpan Real C1).direction =
        Module.finrank Real (affineSpan Real C2).direction) :
    affineSpan Real C1 = affineSpan Real C2 := by
  have hdir_le :
      (affineSpan Real C1).direction ≤ (affineSpan Real C2).direction :=
    AffineSubspace.direction_le hspan
  have hdir_eq :
      (affineSpan Real C1).direction = (affineSpan Real C2).direction :=
    Submodule.eq_of_le_of_finrank_eq hdir_le (by simpa using hfin)
  have hnonempty :
      (affineSpan Real C1 : Set (EuclideanSpace Real (Fin n))).Nonempty := by
    simpa using (hC1ne.affineSpan (k := Real))
  exact
    AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdir_eq hnonempty hspan

/-- A relative interior point cannot lie in the closure of a disjoint relative interior. -/
lemma ri_point_not_mem_closure_ri_of_disjoint (n : Nat)
    {C1 C2 : Set (EuclideanSpace Real (Fin n))} {x : EuclideanSpace Real (Fin n)}
    (hx : x ∈ euclideanRelativeInterior n C1)
    (hspan : affineSpan Real C1 = affineSpan Real C2)
    (hdisj : Disjoint C1 (euclideanRelativeInterior n C2)) :
    x ∉ closure (euclideanRelativeInterior n C2) := by
  intro hxcl
  rcases hx with ⟨-, ε, hε, hxsub⟩
  rcases (Metric.mem_closure_iff.mp hxcl) (ε / 2) (by linarith [hε]) with
    ⟨y, hyri, hydist⟩
  have hy_aff : y ∈ affineSpan Real C2 := hyri.1
  have hy_aff' : y ∈ affineSpan Real C1 := by
    simpa [hspan] using hy_aff
  have hnorm : ‖y - x‖ ≤ ε := by
    have hlt : ‖y - x‖ < ε / 2 := by
      simpa [dist_eq_norm, norm_sub_rev] using hydist
    have hle : ε / 2 ≤ ε := by linarith [hε]
    exact le_of_lt (lt_of_lt_of_le hlt hle)
  have hy_ball : y ∈ (fun z => x + z) '' (ε • euclideanUnitBall n) := by
    refine ⟨y - x, ?_, by simp⟩
    exact mem_smul_unitBall_of_norm_le hε hnorm
  have hyC1 : y ∈ C1 := hxsub ⟨hy_ball, hy_aff'⟩
  have hcontra : False := (Set.disjoint_left.1 hdisj) hyC1 hyri
  exact hcontra.elim

/-- Corollary 6.3.3. If `C1` is a non-empty convex subset of the relative boundary of a
non-empty convex set `C2` in `R^n`, then `dim C1 < dim C2`. -/
theorem euclidean_dim_lt_of_convex_subset_relativeBoundary (n : Nat)
    (C1 C2 : Set (EuclideanSpace Real (Fin n))) (hC1 : Convex Real C1)
    (hC2 : Convex Real C2) (hC1ne : C1.Nonempty) (hC2ne : C2.Nonempty)
    (hC1sub : C1 ⊆ euclideanRelativeBoundary n C2) :
    Module.finrank Real (affineSpan Real C1).direction <
      Module.finrank Real (affineSpan Real C2).direction := by
  have hspan_le : affineSpan Real C1 ≤ affineSpan Real C2 :=
    affineSpan_le_of_subset_relativeBoundary n C1 C2 hC1sub
  have hdir_le :
      (affineSpan Real C1).direction ≤ (affineSpan Real C2).direction :=
    AffineSubspace.direction_le hspan_le
  have hfin_le :
      Module.finrank Real (affineSpan Real C1).direction ≤
        Module.finrank Real (affineSpan Real C2).direction :=
    Submodule.finrank_mono hdir_le
  have hriC1ne : (euclideanRelativeInterior n C1).Nonempty :=
    (euclideanRelativeInterior_closure_convex_affineSpan n C1 hC1).2.2.2.2 hC1ne
  by_contra hnotlt
  have hfin_eq :
      Module.finrank Real (affineSpan Real C1).direction =
        Module.finrank Real (affineSpan Real C2).direction :=
    le_antisymm hfin_le (le_of_not_gt hnotlt)
  have hspan_eq :
      affineSpan Real C1 = affineSpan Real C2 :=
    affineSpan_eq_of_nonempty_of_finrank_eq n C1 C2 hC1ne hspan_le hfin_eq
  rcases hriC1ne with ⟨x, hx⟩
  have hxC1 : x ∈ C1 :=
    (euclideanRelativeInterior_subset_closure n C1).1 hx
  have hxclC2 : x ∈ closure C2 := (hC1sub hxC1).1
  have hxclriC2 :
      x ∈ closure (euclideanRelativeInterior n C2) :=
    (euclidean_closure_subset_closure_relativeInterior_of_nonempty n C2 hC2 hC2ne)
      hxclC2
  have hdisj : Disjoint C1 (euclideanRelativeInterior n C2) := by
    refine Set.disjoint_left.2 ?_
    intro y hyC1 hyriC2
    have hy := hC1sub hyC1
    exact hy.2 hyriC2
  have hxnot :
      x ∉ closure (euclideanRelativeInterior n C2) :=
    ri_point_not_mem_closure_ri_of_disjoint n hx hspan_eq hdisj
  exact hxnot hxclriC2

/-- A relative interior point allows extending any segment past it inside `C`. -/
lemma euclideanRelativeInterior_exists_extension_point (n : Nat)
    (C : Set (EuclideanSpace Real (Fin n))) {z : EuclideanSpace Real (Fin n)}
    (hz : z ∈ euclideanRelativeInterior n C) :
    ∀ x ∈ C, ∃ μ > (1 : Real), (1 - μ) • x + μ • z ∈ C := by
  intro x hxC
  rcases hz with ⟨hz_aff, ε, hε, hzsub⟩
  set δ : Real := ε / (‖z - x‖ + ε)
  set μ : Real := 1 + δ
  set y : EuclideanSpace Real (Fin n) := AffineMap.lineMap x z μ
  have hdist : 0 ≤ ‖(z - x : EuclideanSpace Real (Fin n))‖ := by
    simp
  have hden : 0 < ‖z - x‖ + ε := by
    linarith [hdist, hε]
  have hδpos : 0 < δ := by
    exact div_pos hε hden
  have hμ1 : 1 < μ := by linarith [hδpos]
  have hx_aff : x ∈ affineSpan Real C :=
    (subset_affineSpan (k := Real) (s := C)) hxC
  have hy_aff : y ∈ affineSpan Real C := by
    have h :=
      AffineMap.lineMap_mem (Q := affineSpan Real C)
        (p₀ := x) (p₁ := z) μ hx_aff hz_aff
    simpa [y] using h
  have hy_vsub : y - z = δ • (z - x) := by
    have hy_vsub' : y - z = (1 - μ) • (x - z) := by
      simpa [y, vsub_eq_sub] using
        (AffineMap.lineMap_vsub_right (p₀ := x) (p₁ := z) (c := μ))
    have h1μ : 1 - μ = -δ := by
      simp [μ]
    have hsub : x - z = -(z - x) := by
      simp
    calc
      y - z = (1 - μ) • (x - z) := hy_vsub'
      _ = (-δ) • (x - z) := by simp [h1μ]
      _ = -(δ • (x - z)) := by simp
      _ = δ • (z - x) := by
        have hsmul : δ • (-(z - x)) = -(δ • (z - x)) := by
          simpa using (smul_neg δ (z - x))
        calc
          -(δ • (x - z)) = -(δ • (-(z - x))) := by rw [hsub]
          _ = -(-(δ • (z - x))) := by rw [hsmul]
          _ = δ • (z - x) := by simp
  have hnorm : ‖y - z‖ ≤ ε := by
    have hratio_lt : ‖z - x‖ / (‖z - x‖ + ε) < 1 := by
      have hnum : ‖z - x‖ < ‖z - x‖ + ε := by linarith [hε]
      have h := (div_lt_one hden).2 hnum
      simpa using h
    have hratio_le : ‖z - x‖ / (‖z - x‖ + ε) ≤ 1 := le_of_lt hratio_lt
    have hεnonneg : 0 ≤ ε := le_of_lt hε
    have hδnonneg : 0 ≤ δ := le_of_lt hδpos
    have hnorm_smul : ‖δ • (z - x)‖ = δ * ‖z - x‖ := by
      simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hδnonneg]
    have hcalc : δ * ‖z - x‖ = ε * (‖z - x‖ / (‖z - x‖ + ε)) := by
      simp [δ, div_eq_mul_inv, mul_comm, mul_left_comm]
    calc
      ‖y - z‖ = ‖δ • (z - x)‖ := by simp [hy_vsub]
      _ = δ * ‖z - x‖ := hnorm_smul
      _ = ε * (‖z - x‖ / (‖z - x‖ + ε)) := hcalc
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hratio_le hεnonneg
      _ = ε := by simp
  have hy_ball :
      y ∈ (fun t => z + t) '' (ε • euclideanUnitBall n) := by
    refine ⟨y - z, ?_, ?_⟩
    · exact mem_smul_unitBall_of_norm_le hε hnorm
    · simp [sub_eq_add_neg, add_comm]
  have hyC : y ∈ C := by
    have hy_in :
        y ∈ ((fun t => z + t) '' (ε • euclideanUnitBall n)) ∩
          (affineSpan Real C : Set (EuclideanSpace Real (Fin n))) := by
      exact ⟨hy_ball, hy_aff⟩
    exact hzsub hy_in
  refine ⟨μ, hμ1, ?_⟩
  simpa [y, AffineMap.lineMap_apply_module] using hyC

/-- Theorem 6.4: Let `C` be a non-empty convex set in `R^n`. Then `z ∈ ri C` if and only if,
for every `x ∈ C`, there exists `μ > 1` such that `(1 - μ) x + μ z` belongs to `C`. -/
theorem euclideanRelativeInterior_iff_forall_exists_affine_combination_mem (n : Nat)
    (C : Set (EuclideanSpace Real (Fin n))) (hC : Convex Real C) (hCne : C.Nonempty)
    (z : EuclideanSpace Real (Fin n)) :
    z ∈ euclideanRelativeInterior n C ↔
      ∀ x ∈ C, ∃ μ > (1 : Real), (1 - μ) • x + μ • z ∈ C := by
  constructor
  · intro hz
    exact euclideanRelativeInterior_exists_extension_point n C hz
  · intro h
    have hri_nonempty : (euclideanRelativeInterior n C).Nonempty :=
      (euclideanRelativeInterior_closure_convex_affineSpan n C hC).2.2.2.2 hCne
    rcases hri_nonempty with ⟨x, hx⟩
    have hxC : x ∈ C := (euclideanRelativeInterior_subset_closure n C).1 hx
    rcases h x hxC with ⟨μ, hμ, hyC⟩
    set y : EuclideanSpace Real (Fin n) := AffineMap.lineMap x z μ
    have hyC' : y ∈ C := by
      simpa [y, AffineMap.lineMap_apply_module] using hyC
    have hy_closure : y ∈ closure C := subset_closure hyC'
    have hμpos : 0 < μ := by linarith [hμ]
    have hμne : μ ≠ 0 := ne_of_gt hμpos
    have hz_lineMap : AffineMap.lineMap x y μ⁻¹ = z := by
      simp [y, hμne]
    have hz_eq : (1 - μ⁻¹) • x + μ⁻¹ • y = z := by
      simpa [AffineMap.lineMap_apply_module] using hz_lineMap
    have ht0 : 0 ≤ μ⁻¹ := inv_nonneg.mpr (le_of_lt hμpos)
    have ht1 : μ⁻¹ < 1 := by
      exact inv_lt_one_of_one_lt₀ hμ
    have hz_mem :
        (1 - μ⁻¹) • x + μ⁻¹ • y ∈ euclideanRelativeInterior n C :=
      euclideanRelativeInterior_convex_combination_mem n C hC x y hx hy_closure μ⁻¹ ht0 ht1
    simpa [hz_eq] using hz_mem

/-- Interior points allow stepping a positive distance in any direction. -/
lemma interior_imp_forall_exists_add_smul_mem (n : Nat)
    (C : Set (EuclideanSpace Real (Fin n))) (z : EuclideanSpace Real (Fin n)) :
    z ∈ interior C →
      ∀ y : EuclideanSpace Real (Fin n), ∃ ε > (0 : Real), z + ε • y ∈ C := by
  intro hz y
  have hz' :
      z ∈ {x | ∃ ε : ℝ, 0 < ε ∧ (fun t => x + t) '' (ε • euclideanUnitBall n) ⊆ C} := by
    have hz' := hz
    rw [euclidean_interior_eq_setOf_exists_thickening] at hz'
    exact hz'
  rcases hz' with ⟨ε, hε, hzsub⟩
  set δ : Real := ε / (‖y‖ + 1)
  have hden : 0 < ‖y‖ + 1 := by linarith [norm_nonneg y]
  have hδpos : 0 < δ := by
    exact div_pos hε hden
  have hδnonneg : 0 ≤ δ := le_of_lt hδpos
  have hnorm : ‖δ • y‖ ≤ ε := by
    have hnorm_le : ‖y‖ ≤ ‖y‖ + 1 := by linarith [norm_nonneg y]
    have hmul : δ * ‖y‖ ≤ δ * (‖y‖ + 1) :=
      mul_le_mul_of_nonneg_left hnorm_le hδnonneg
    have hδmul : δ * (‖y‖ + 1) = ε := by
      have hden_ne : ‖y‖ + 1 ≠ 0 := by linarith [norm_nonneg y]
      calc
        δ * (‖y‖ + 1) = (ε / (‖y‖ + 1)) * (‖y‖ + 1) := by simp [δ]
        _ = ε := by field_simp [hden_ne]
    calc
      ‖δ • y‖ = δ * ‖y‖ := by
        simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hδnonneg]
      _ ≤ δ * (‖y‖ + 1) := hmul
      _ = ε := hδmul
  have hy_ball : δ • y ∈ ε • euclideanUnitBall n :=
    mem_smul_unitBall_of_norm_le hε hnorm
  have hz_mem :
      z + δ • y ∈ (fun t => z + t) '' (ε • euclideanUnitBall n) :=
    ⟨δ • y, hy_ball, rfl⟩
  exact ⟨δ, hδpos, hzsub hz_mem⟩

/-- Stepping in every direction yields the extension property of Theorem 6.4. -/
lemma forall_exists_add_smul_mem_imp_extension (n : Nat)
    (C : Set (EuclideanSpace Real (Fin n))) (z : EuclideanSpace Real (Fin n))
    (h : ∀ y : EuclideanSpace Real (Fin n), ∃ ε > (0 : Real), z + ε • y ∈ C) :
    ∀ x ∈ C, ∃ μ > (1 : Real), (1 - μ) • x + μ • z ∈ C := by
  intro x _
  rcases h (z - x) with ⟨ε, hε, hzC⟩
  refine ⟨1 + ε, by linarith [hε], ?_⟩
  have hcalc :
      (1 - (1 + ε)) • x + (1 + ε) • z = z + ε • (z - x) := by
    have h1 : (1 - (1 + ε) : Real) = -ε := by ring
    calc
      (1 - (1 + ε)) • x + (1 + ε) • z
          = (-ε) • x + (1 + ε) • z := by simp [h1]
      _ = (1 + ε) • z + (-ε) • x := by ac_rfl
      _ = (1 : Real) • z + ε • z + (-ε) • x := by
        simp [add_smul]
      _ = z + ε • z + (-ε) • x := by simp
      _ = z + (ε • z + (-ε) • x) := by ac_rfl
      _ = z + (ε • z - ε • x) := by simp [sub_eq_add_neg]
      _ = z + ε • (z - x) := by
        simp [smul_sub]
  rw [hcalc]
  exact hzC

/-- Stepping in every direction forces the affine span of `C` to be all of `R^n`. -/
lemma affineSpan_eq_univ_of_forall_exists_add_smul_mem (n : Nat)
    (C : Set (EuclideanSpace Real (Fin n))) (z : EuclideanSpace Real (Fin n))
    (h : ∀ y : EuclideanSpace Real (Fin n), ∃ ε > (0 : Real), z + ε • y ∈ C) :
    (affineSpan Real C : Set (EuclideanSpace Real (Fin n))) = Set.univ := by
  ext p; constructor
  · intro _; exact Set.mem_univ p
  · intro _
    rcases h 0 with ⟨ε0, -, hzC⟩
    have hzC' : z ∈ C := by simpa using hzC
    have hz_aff : z ∈ affineSpan Real C :=
      (subset_affineSpan (k := Real) (s := C)) hzC'
    rcases h (p - z) with ⟨ε, hε, hpC⟩
    set w : EuclideanSpace Real (Fin n) := z + ε • (p - z)
    have hwC : w ∈ C := by simpa [w] using hpC
    have hw_aff : w ∈ affineSpan Real C :=
      (subset_affineSpan (k := Real) (s := C)) hwC
    have hεne : ε ≠ 0 := ne_of_gt hε
    have hp_line : AffineMap.lineMap z w ε⁻¹ = p := by
      calc
        AffineMap.lineMap z w ε⁻¹
            = (1 - ε⁻¹) • z + ε⁻¹ • w := by
              simp [AffineMap.lineMap_apply_module]
        _ = (1 - ε⁻¹) • z + (ε⁻¹ • z + (ε⁻¹ * ε) • (p - z)) := by
          simp [w, smul_add, smul_smul]
        _ = z + (ε⁻¹ * ε) • (p - z) := by
          have hz' : (1 - ε⁻¹) • z + ε⁻¹ • z = z := by
            calc
              (1 - ε⁻¹) • z + ε⁻¹ • z
                  = ((1 - ε⁻¹) + ε⁻¹) • z := by
                    simpa using (add_smul (1 - ε⁻¹) ε⁻¹ z).symm
              _ = (1 : Real) • z := by ring_nf
              _ = z := by simp
          calc
            (1 - ε⁻¹) • z + (ε⁻¹ • z + (ε⁻¹ * ε) • (p - z))
                = ((1 - ε⁻¹) • z + ε⁻¹ • z) + (ε⁻¹ * ε) • (p - z) := by
                  simp [add_assoc]
            _ = z + (ε⁻¹ * ε) • (p - z) := by
                  simp [hz']
        _ = z + (p - z) := by
          simp [hεne]
        _ = p := by
          simp [sub_eq_add_neg]
    have hp_aff :
        AffineMap.lineMap z w ε⁻¹ ∈ affineSpan Real C := by
      exact
        AffineMap.lineMap_mem (Q := affineSpan Real C)
          (p₀ := z) (p₁ := w) ε⁻¹ hz_aff hw_aff
    simpa [hp_line] using hp_aff

/-- Corollary 6.4.1: Let `C` be a convex set in `R^n`. Then `z ∈ int C` if and only if, for
every `y ∈ R^n`, there exists `ε > 0` such that `z + ε y ∈ C`. -/
theorem euclidean_interior_iff_forall_exists_add_smul_mem (n : Nat)
    (C : Set (EuclideanSpace Real (Fin n))) (hC : Convex Real C)
    (z : EuclideanSpace Real (Fin n)) :
    z ∈ interior C ↔
      ∀ y : EuclideanSpace Real (Fin n), ∃ ε > (0 : Real), z + ε • y ∈ C := by
  constructor
  · intro hz
    exact interior_imp_forall_exists_add_smul_mem n C z hz
  · intro h
    have hCne : C.Nonempty := by
      rcases h 0 with ⟨ε, -, hzC⟩
      exact ⟨z, by simpa using hzC⟩
    have hspan :
        (affineSpan Real C : Set (EuclideanSpace Real (Fin n))) = Set.univ :=
      affineSpan_eq_univ_of_forall_exists_add_smul_mem n C z h
    have h_ext :
        ∀ x ∈ C, ∃ μ > (1 : Real), (1 - μ) • x + μ • z ∈ C :=
      forall_exists_add_smul_mem_imp_extension n C z h
    have hzri : z ∈ euclideanRelativeInterior n C :=
      (euclideanRelativeInterior_iff_forall_exists_affine_combination_mem n C hC hCne z).2 h_ext
    have hri_eq :
        euclideanRelativeInterior n C = interior C :=
      euclideanRelativeInterior_eq_interior_of_affineSpan_eq_univ n C hspan
    simpa [hri_eq] using hzri

/-- Points in all closures lie in the closure of the intersection of relative interiors. -/
lemma iInter_closure_subset_closure_iInter_relativeInterior (n : Nat) {I : Type*}
    (C : I → Set (EuclideanSpace Real (Fin n))) (hC : ∀ i, Convex Real (C i))
    (hri : (⋂ i, euclideanRelativeInterior n (C i)).Nonempty) :
    (⋂ i, closure (C i)) ⊆ closure (⋂ i, euclideanRelativeInterior n (C i)) := by
  classical
  intro y hy
  rcases hri with ⟨x, hx⟩
  refine
    (Metric.mem_closure_iff (α := EuclideanSpace Real (Fin n))
        (a := y) (s := ⋂ i, euclideanRelativeInterior n (C i))).2 ?_
  intro ε hε
  set t : Real := dist x y / (dist x y + ε)
  have hdist : 0 ≤ dist x y := dist_nonneg
  have hden : 0 < dist x y + ε := by
    linarith [hdist, hε]
  have ht0 : 0 ≤ t := by
    exact div_nonneg hdist (le_of_lt hden)
  have ht1 : t < 1 := by
    have hnum : dist x y < dist x y + ε := by linarith [hε]
    have h := (div_lt_one hden).2 hnum
    simpa [t] using h
  have hmem :
      (1 - t) • x + t • y ∈ ⋂ i, euclideanRelativeInterior n (C i) := by
    refine Set.mem_iInter.2 ?_
    intro i
    have hx_i : x ∈ euclideanRelativeInterior n (C i) := (Set.mem_iInter.1 hx) i
    have hy_i : y ∈ closure (C i) := (Set.mem_iInter.1 hy) i
    exact
      euclideanRelativeInterior_convex_combination_mem n (C i) (hC i) x y hx_i hy_i t ht0 ht1
  have hdist_eq :
      dist ((1 - t) • x + t • y) y = ‖1 - t‖ * dist x y := by
    simpa [AffineMap.lineMap_apply_module] using (dist_lineMap_right x y t)
  have h1t_nonneg : 0 ≤ 1 - t := sub_nonneg.mpr (le_of_lt ht1)
  have h1t_eq : 1 - t = ε / (dist x y + ε) := by
    have hden' : dist x y + ε ≠ 0 := by linarith [hdist, hε]
    calc
      1 - t = (dist x y + ε - dist x y) / (dist x y + ε) := by
        simpa [t] using (one_sub_div (a := dist x y) (b := dist x y + ε) hden')
      _ = ε / (dist x y + ε) := by simp
  have hratio_lt : dist x y / (dist x y + ε) < 1 := by
    simpa [t] using ht1
  have hdist_lt : dist ((1 - t) • x + t • y) y < ε := by
    have hεpos : 0 < ε := hε
    have h1t_norm : ‖1 - t‖ = 1 - t := by
      simpa using (Real.norm_of_nonneg h1t_nonneg)
    calc
      dist ((1 - t) • x + t • y) y
          = ‖1 - t‖ * dist x y := hdist_eq
      _ = (1 - t) * dist x y := by simp [h1t_norm]
      _ = (ε / (dist x y + ε)) * dist x y := by simp [h1t_eq]
      _ = ε * (dist x y / (dist x y + ε)) := by
          simp [div_eq_mul_inv, mul_comm, mul_left_comm]
      _ < ε := by
          have h := (mul_lt_mul_of_pos_left hratio_lt hεpos)
          simpa using h
  have hdist_lt' : dist y ((1 - t) • x + t • y) < ε := by
    simpa [dist_comm] using hdist_lt
  exact ⟨(1 - t) • x + t • y, hmem, hdist_lt'⟩

set_option maxHeartbeats 400000 in
-- The affine-combination proof is long and needs more heartbeats.
/-- Shrinking the extension parameter preserves membership in a convex set. -/
lemma affine_combination_mem_of_between (n : Nat) (C : Set (EuclideanSpace Real (Fin n)))
    (hC : Convex Real C) {x z : EuclideanSpace Real (Fin n)} (hz : z ∈ C)
    {μ0 μ : Real} (hμ0 : 1 < μ0) (hμ1 : 1 ≤ μ) (hμ : μ ≤ μ0)
    (hμ0mem : (1 - μ0) • x + μ0 • z ∈ C) :
    (1 - μ) • x + μ • z ∈ C := by
  set t : Real := (μ0 - μ) / (μ0 - 1)
  have hden : 0 < μ0 - 1 := by linarith [hμ0]
  have ht0 : 0 ≤ t := by
    have hnum : 0 ≤ μ0 - μ := by linarith [hμ]
    exact div_nonneg hnum (le_of_lt hden)
  have ht1 : t ≤ 1 := by
    have hnum : μ0 - μ ≤ μ0 - 1 := by linarith [hμ1]
    have h := (div_le_one hden).2 hnum
    simpa [t] using h
  have hden' : μ0 - 1 ≠ 0 := by linarith [hμ0]
  have ht : t * (μ0 - 1) = μ0 - μ := by
    calc
      t * (μ0 - 1) = ((μ0 - μ) / (μ0 - 1)) * (μ0 - 1) := by simp [t]
      _ = (μ0 - μ) * (μ0 - 1) / (μ0 - 1) := by
            simpa using (div_mul_eq_mul_div (μ0 - μ) (μ0 - 1) (μ0 - 1))
      _ = (μ0 - 1) * (μ0 - μ) / (μ0 - 1) := by ring
      _ = μ0 - μ := by
            simpa using (mul_div_cancel_left₀ (μ0 - μ) hden')
  have hcoef_z : (1 - t) * μ0 + t = μ := by
    calc
      (1 - t) * μ0 + t = μ0 - t * μ0 + t := by ring
      _ = μ0 - t * (μ0 - 1) := by ring
      _ = μ0 - (μ0 - μ) := by simp [ht]
      _ = μ := by ring
  have hcoef_x : (1 - t) * (1 - μ0) = 1 - μ := by
    calc
      (1 - t) * (1 - μ0) = (1 - μ0) - t * (1 - μ0) := by ring
      _ = 1 - μ0 + t * (μ0 - 1) := by ring
      _ = 1 - μ0 + (μ0 - μ) := by simp [ht]
      _ = 1 - μ := by ring
  have hline :
      (1 - t) • (1 - μ0) • x + (1 - t) • μ0 • z + t • z = (1 - μ) • x + μ • z := by
    have hz :
        (1 - t) • μ0 • z + t • z = ((1 - t) • μ0 + t) • z := by
      calc
        (1 - t) • μ0 • z + t • z = ((1 - t) * μ0) • z + t • z := by
          simp [smul_smul]
        _ = ((1 - t) * μ0 + t) • z := by
          simpa using (add_smul ((1 - t) * μ0) t z).symm
    have hxcoef : (1 - t) • (1 - μ0) • x = (1 - μ) • x := by
      simp [smul_smul, hcoef_x]
    calc
      (1 - t) • (1 - μ0) • x + (1 - t) • μ0 • z + t • z
          = (1 - t) • (1 - μ0) • x + ((1 - t) • μ0 + t) • z := by
            simp [add_assoc, hz]
      _ = (1 - μ) • x + μ • z := by
            simp [hxcoef, hcoef_z]
  have hmem :
      (1 - t) • ((1 - μ0) • x + μ0 • z) + t • z ∈ C := by
    simpa [AffineMap.lineMap_apply_module] using
      (hC.lineMap_mem hμ0mem hz ⟨ht0, ht1⟩)
  simpa [hline] using hmem

/-- A uniform extension parameter exists in a finite intersection of convex sets. -/
lemma exists_mu_gt_one_mem_iInter_of_finite (n : Nat) {I : Type*} [Finite I]
    (C : I → Set (EuclideanSpace Real (Fin n))) (hC : ∀ i, Convex Real (C i))
    {x z : EuclideanSpace Real (Fin n)}
    (hz : z ∈ ⋂ i, euclideanRelativeInterior n (C i)) (hx : x ∈ ⋂ i, C i) :
    ∃ μ > (1 : Real), (1 - μ) • x + μ • z ∈ ⋂ i, C i := by
  classical
  by_cases hI : (Nonempty I)
  · classical
    let _ := Fintype.ofFinite I
    have hz_i : ∀ i, z ∈ euclideanRelativeInterior n (C i) := by
      intro i
      exact (Set.mem_iInter.1 hz) i
    have hx_i : ∀ i, x ∈ C i := by
      intro i
      exact (Set.mem_iInter.1 hx) i
    have hCne : ∀ i, (C i).Nonempty := by
      intro i
      exact ⟨z, (euclideanRelativeInterior_subset_closure n (C i)).1 (hz_i i)⟩
    choose μ hμ_gt hμ_mem using
      (fun i =>
        (euclideanRelativeInterior_iff_forall_exists_affine_combination_mem n (C i) (hC i)
          (hCne i) z).1 (hz_i i) x (hx_i i))
    have hμset_nonempty : (Finset.univ.image μ).Nonempty := by
      rcases hI with ⟨i0⟩
      refine ⟨μ i0, ?_⟩
      exact Finset.mem_image.2 ⟨i0, Finset.mem_univ i0, rfl⟩
    let μmin : Real := Finset.min' (Finset.univ.image μ) hμset_nonempty
    have hμmin_gt : 1 < μmin := by
      have hlt : ∀ y ∈ Finset.univ.image μ, 1 < y := by
        intro y hy
        rcases Finset.mem_image.1 hy with ⟨i, -, rfl⟩
        exact hμ_gt i
      have h :=
        (Finset.lt_min'_iff (s := Finset.univ.image μ) (H := hμset_nonempty) (x := 1)).2 hlt
      simpa [μmin] using h
    have hμmin_le : ∀ i, μmin ≤ μ i := by
      intro i
      have hmem : μ i ∈ Finset.univ.image μ :=
        Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩
      have hmin_le : (Finset.univ.image μ).min' ⟨μ i, hmem⟩ ≤ μ i :=
        Finset.min'_le (s := Finset.univ.image μ) (x := μ i) hmem
      have hproof :
          (⟨μ i, hmem⟩ : (Finset.univ.image μ).Nonempty) = hμset_nonempty :=
        Subsingleton.elim _ _
      simpa [μmin, hproof] using hmin_le
    refine ⟨μmin, hμmin_gt, ?_⟩
    have hmem : ∀ i, (1 - μmin) • x + μmin • z ∈ C i := by
      intro i
      have hzC : z ∈ C i :=
        (euclideanRelativeInterior_subset_closure n (C i)).1 (hz_i i)
      have hμmin_le_i : μmin ≤ μ i := hμmin_le i
      have hμmin_ge : 1 ≤ μmin := le_of_lt hμmin_gt
      exact
        affine_combination_mem_of_between n (C i) (hC i) hzC (hμ_gt i) hμmin_ge
          hμmin_le_i (hμ_mem i)
    exact Set.mem_iInter.2 hmem
  · have hI' : IsEmpty I := not_nonempty_iff.mp hI
    refine ⟨2, by norm_num, ?_⟩
    simp

/-- Theorem 6.5: Let `C i` be convex sets in `R^n` for `i ∈ I`, and let the sets
`ri (C i)` have a common point. Then `cl (⋂ i, C i) = ⋂ i, cl (C i)`. If `I` is finite,
then also `ri (⋂ i, C i) = ⋂ i, ri (C i)`. -/
theorem euclidean_closure_iInter_eq_iInter_closure_of_common_relativeInterior (n : Nat)
    {I : Type*} (C : I → Set (EuclideanSpace Real (Fin n))) (hC : ∀ i, Convex Real (C i))
    (hri : (⋂ i, euclideanRelativeInterior n (C i)).Nonempty) :
    closure (⋂ i, C i) = ⋂ i, closure (C i) := by
  refine le_antisymm ?_ ?_
  · refine Set.subset_iInter ?_
    intro i
    exact closure_mono (Set.iInter_subset (fun i => C i) i)
  · have h1 :
        ⋂ i, closure (C i) ⊆ closure (⋂ i, euclideanRelativeInterior n (C i)) :=
      iInter_closure_subset_closure_iInter_relativeInterior n C hC hri
    have h2 :
        closure (⋂ i, euclideanRelativeInterior n (C i)) ⊆ closure (⋂ i, C i) := by
      refine closure_mono ?_
      refine Set.subset_iInter ?_
      intro i
      intro x hx
      have hx' : x ∈ euclideanRelativeInterior n (C i) := (Set.mem_iInter.1 hx) i
      exact (euclideanRelativeInterior_subset_closure n (C i)).1 hx'
    exact h1.trans h2

/-- Theorem 6.5: If `I` is finite, then `ri (⋂ i, C i) = ⋂ i, ri (C i)` under the same
assumptions as the preceding statement. -/
theorem euclideanRelativeInterior_iInter_eq_iInter_relativeInterior_of_finite (n : Nat)
    {I : Type*} [Finite I] (C : I → Set (EuclideanSpace Real (Fin n)))
    (hC : ∀ i, Convex Real (C i))
    (hri : (⋂ i, euclideanRelativeInterior n (C i)).Nonempty) :
    euclideanRelativeInterior n (⋂ i, C i) = ⋂ i, euclideanRelativeInterior n (C i) := by
  classical
  have hcl_eq :
      closure (⋂ i, C i) = ⋂ i, closure (C i) :=
    euclidean_closure_iInter_eq_iInter_closure_of_common_relativeInterior n C hC hri
  have hcl_eq' :
      closure (⋂ i, C i) = closure (⋂ i, euclideanRelativeInterior n (C i)) := by
    have h1 :
        ⋂ i, closure (C i) ⊆ closure (⋂ i, euclideanRelativeInterior n (C i)) :=
      iInter_closure_subset_closure_iInter_relativeInterior n C hC hri
    have h2 :
        closure (⋂ i, euclideanRelativeInterior n (C i)) ⊆ closure (⋂ i, C i) := by
      refine closure_mono ?_
      refine Set.subset_iInter ?_
      intro i
      intro x hx
      have hx' : x ∈ euclideanRelativeInterior n (C i) := (Set.mem_iInter.1 hx) i
      exact (euclideanRelativeInterior_subset_closure n (C i)).1 hx'
    have hcl_subset : closure (⋂ i, C i) ⊆ closure (⋂ i, euclideanRelativeInterior n (C i)) := by
      simpa [hcl_eq] using h1
    exact le_antisymm (hcl_subset) h2
  have hri_subset :
      euclideanRelativeInterior n (⋂ i, C i) ⊆ ⋂ i, euclideanRelativeInterior n (C i) := by
    have hconv1 : Convex Real (⋂ i, C i) := convex_iInter hC
    have hconv2 :
        Convex Real (⋂ i, euclideanRelativeInterior n (C i)) := by
      refine convex_iInter ?_
      intro i
      exact convex_euclideanRelativeInterior n (C i) (hC i)
    have hiff :=
      (euclidean_closure_eq_iff_relativeInterior_eq_and_between n (⋂ i, C i)
        (⋂ i, euclideanRelativeInterior n (C i)) hconv1 hconv2).1
    have hri_eq :
        euclideanRelativeInterior n (⋂ i, C i) =
          euclideanRelativeInterior n (⋂ i, euclideanRelativeInterior n (C i)) :=
      (hiff.mp hcl_eq')
    have hri_subset' :
        euclideanRelativeInterior n (⋂ i, euclideanRelativeInterior n (C i)) ⊆
          ⋂ i, euclideanRelativeInterior n (C i) :=
      (euclideanRelativeInterior_subset_closure n (⋂ i, euclideanRelativeInterior n (C i))).1
    simpa [hri_eq] using hri_subset'
  have hri_superset :
      ⋂ i, euclideanRelativeInterior n (C i) ⊆ euclideanRelativeInterior n (⋂ i, C i) := by
    intro z hz
    have hCne : (⋂ i, C i).Nonempty := by
      refine ⟨z, ?_⟩
      refine Set.mem_iInter.2 ?_
      intro i
      have hz' : z ∈ euclideanRelativeInterior n (C i) := (Set.mem_iInter.1 hz) i
      exact (euclideanRelativeInterior_subset_closure n (C i)).1 hz'
    have hconv : Convex Real (⋂ i, C i) := convex_iInter hC
    have hiff :=
      (euclideanRelativeInterior_iff_forall_exists_affine_combination_mem n (⋂ i, C i) hconv
        hCne z)
    refine (hiff.mpr ?_)
    intro x hx
    exact exists_mu_gt_one_mem_iInter_of_finite n C hC hz hx
  exact le_antisymm hri_subset hri_superset

/-- The intersection of a `Fin 2`-indexed family is the binary intersection. -/
lemma iInter_fin_two_eq_inter {α : Type*} (D : Fin 2 → Set α) :
    (⋂ i, D i) = D 0 ∩ D 1 := by
  ext x; constructor
  · intro hx
    have hx0 : x ∈ D 0 := (Set.mem_iInter.1 hx) 0
    have hx1 : x ∈ D 1 := (Set.mem_iInter.1 hx) 1
    exact ⟨hx0, hx1⟩
  · rintro ⟨hx0, hx1⟩
    refine Set.mem_iInter.2 ?_
    intro i
    fin_cases i
    · simpa using hx0
    · simpa using hx1

/-- A point of `M ∩ ri C` gives a point in the intersection of the relative interiors. -/
lemma ri_iInter_nonempty_from_hM (n : Nat) (C : Set (EuclideanSpace Real (Fin n)))
    (M : AffineSubspace Real (EuclideanSpace Real (Fin n))) (D : Fin 2 → Set _)
    (hD0 : D 0 = (M : Set (EuclideanSpace Real (Fin n)))) (hD1 : D 1 = C)
    (hM : ((M : Set (EuclideanSpace Real (Fin n))) ∩ euclideanRelativeInterior n C).Nonempty) :
    (⋂ i, euclideanRelativeInterior n (D i)).Nonempty := by
  rcases hM with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  refine Set.mem_iInter.2 ?_
  intro i
  fin_cases i
  · have hxM : x ∈ (M : Set (EuclideanSpace Real (Fin n))) := hx.1
    simpa [hD0, euclideanRelativeInterior_affineSubspace_eq] using hxM
  · have hxC : x ∈ euclideanRelativeInterior n C := hx.2
    simpa [hD1] using hxC

/-- The closure of an affine subspace is itself. -/
lemma closure_affineSubspace_eq (n : Nat)
    (M : AffineSubspace Real (EuclideanSpace Real (Fin n))) :
    closure (M : Set (EuclideanSpace Real (Fin n))) = M := by
  have hclosed : IsClosed (M : Set (EuclideanSpace Real (Fin n))) :=
    affineSubspace_isClosed n M
  simp

/-- Corollary 6.5.1. Let `C` be convex and let `M` be an affine set containing a point of
`ri C`. Then `ri (M ∩ C) = M ∩ ri C` and `cl (M ∩ C) = M ∩ cl C`. -/
theorem euclideanRelativeInterior_inter_affineSubspace_eq_and_closure_eq (n : Nat)
    (C : Set (EuclideanSpace Real (Fin n))) (hC : Convex Real C)
    (M : AffineSubspace Real (EuclideanSpace Real (Fin n)))
    (hM : ((M : Set (EuclideanSpace Real (Fin n))) ∩ euclideanRelativeInterior n C).Nonempty) :
    euclideanRelativeInterior n ((M : Set (EuclideanSpace Real (Fin n))) ∩ C) =
        (M : Set (EuclideanSpace Real (Fin n))) ∩ euclideanRelativeInterior n C ∧
      closure ((M : Set (EuclideanSpace Real (Fin n))) ∩ C) =
        (M : Set (EuclideanSpace Real (Fin n))) ∩ closure C := by
  classical
  let D : Fin 2 → Set (EuclideanSpace Real (Fin n)) := fun i =>
    if i = 0 then (M : Set (EuclideanSpace Real (Fin n))) else C
  have hD0 : D 0 = (M : Set (EuclideanSpace Real (Fin n))) := by
    simp [D]
  have hD1 : D 1 = C := by
    simp [D]
  have hconv : ∀ i, Convex Real (D i) := by
    intro i
    fin_cases i
    · simpa [D] using (AffineSubspace.convex (Q := M))
    · simpa [D] using hC
  have hri : (⋂ i, euclideanRelativeInterior n (D i)).Nonempty :=
    ri_iInter_nonempty_from_hM n C M D hD0 hD1 hM
  have hri_eq :
      euclideanRelativeInterior n (⋂ i, D i) = ⋂ i, euclideanRelativeInterior n (D i) :=
    euclideanRelativeInterior_iInter_eq_iInter_relativeInterior_of_finite n D hconv hri
  have hcl_eq :
      closure (⋂ i, D i) = ⋂ i, closure (D i) :=
    euclidean_closure_iInter_eq_iInter_closure_of_common_relativeInterior n D hconv hri
  have hInter : (⋂ i, D i) = (M : Set (EuclideanSpace Real (Fin n))) ∩ C := by
    simpa [D] using (iInter_fin_two_eq_inter D)
  have hInter_ri :
      (⋂ i, euclideanRelativeInterior n (D i)) =
        (M : Set (EuclideanSpace Real (Fin n))) ∩ euclideanRelativeInterior n C := by
    simpa [D, euclideanRelativeInterior_affineSubspace_eq] using
      (iInter_fin_two_eq_inter (fun i => euclideanRelativeInterior n (D i)))
  have hInter_closure :
      (⋂ i, closure (D i)) =
        (M : Set (EuclideanSpace Real (Fin n))) ∩ closure C := by
    simpa [D, closure_affineSubspace_eq] using
      (iInter_fin_two_eq_inter (fun i => closure (D i)))
  refine ⟨?_, ?_⟩
  · simpa [hInter, hInter_ri] using hri_eq
  · simpa [hInter, hInter_closure] using hcl_eq

end Section06
end Chap02
