/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Changyu Zou, Yunxi Duan, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section18_part4

open scoped Pointwise

set_option maxHeartbeats 400000

section Chap04
section Section18

variable {𝕜 E : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [SMul 𝕜 E]

/-- A strict mixed convex combination lies in the relative interior of its mixed convex hull. -/
lemma mem_euclideanRelativeInterior_mixedConvexHull_range_of_strict_mixedConvexCombination
    {n k m : ℕ} {x : Fin n → ℝ} (p : Fin k → Fin n → ℝ) (d : Fin m → Fin n → ℝ)
    (a : Fin k → ℝ) (b : Fin m → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j)
    (hsum : ∑ i, a i = 1)
    (hx : x = (∑ i, a i • p i) + (∑ j, b j • d j)) :
    x ∈ euclideanRelativeInterior_fin n
      (mixedConvexHull (n := n) (Set.range p) (Set.range d)) := by
  classical
  have hrepr :=
    mixedConvexHull_eq_conv_add_ray_eq_conv_add_cone (n := n)
      (S₀ := Set.range p) (S₁ := Set.range d)
  have hD' :
      mixedConvexHull (n := n) (Set.range p) (Set.range d) =
        conv (Set.range p) + cone n (Set.range d) := by
    exact hrepr.1.trans hrepr.2
  have hD :
      mixedConvexHull (n := n) (Set.range p) (Set.range d) =
        convexHull ℝ (Set.range p) + cone n (Set.range d) := by
    simpa [conv] using hD'
  have hconv1 : Convex ℝ (convexHull ℝ (Set.range p)) := by
    simpa using (convex_convexHull (𝕜 := ℝ) (s := Set.range p))
  have hconv2 : Convex ℝ (cone n (Set.range d)) := by
    simpa [cone, conv] using
      (convex_convexHull (𝕜 := ℝ) (s := ray n (Set.range d)))
  have hri_add :
      euclideanRelativeInterior_fin n (convexHull ℝ (Set.range p) + cone n (Set.range d)) =
        euclideanRelativeInterior_fin n (convexHull ℝ (Set.range p)) +
          euclideanRelativeInterior_fin n (cone n (Set.range d)) := by
    exact
      euclideanRelativeInterior_fin_add_eq_and_closure_add_superset (n := n)
        (C1 := convexHull ℝ (Set.range p)) (C2 := cone n (Set.range d)) hconv1 hconv2
  have hx1 :
      (∑ i, a i • p i) ∈ euclideanRelativeInterior_fin n (convexHull ℝ (Set.range p)) := by
    simpa using
      (mem_euclideanRelativeInterior_convexHull_of_strict_combination (n := n) (k := k)
        (p := p) (a := a) ha hsum)
  have hx2 :
      (∑ j, b j • d j) ∈ euclideanRelativeInterior_fin n (cone n (Set.range d)) := by
    simpa using
      (mem_euclideanRelativeInterior_cone_of_strict_positive_combination (n := n) (m := m)
        (d := d) (b := b) hb)
  have hxadd :
      x ∈ euclideanRelativeInterior_fin n (convexHull ℝ (Set.range p)) +
            euclideanRelativeInterior_fin n (cone n (Set.range d)) := by
    have hx' :
        (∑ i, a i • p i) + (∑ j, b j • d j) ∈
          euclideanRelativeInterior_fin n (convexHull ℝ (Set.range p)) +
            euclideanRelativeInterior_fin n (cone n (Set.range d)) :=
      Set.add_mem_add hx1 hx2
    simpa [hx] using hx'
  have hxri :
      x ∈ euclideanRelativeInterior_fin n (convexHull ℝ (Set.range p) + cone n (Set.range d)) := by
    simpa [hri_add] using hxadd
  simpa [hD] using hxri

/-- Theorem 18.1 in `Fin n → ℝ` using `euclideanRelativeInterior_fin`. -/
lemma subset_of_isFace_of_convex_of_euclideanRelativeInterior_fin_inter {n : ℕ}
    {C C' D : Set (Fin n → ℝ)} (hC' : IsFace (𝕜 := ℝ) C C') (hDC : D ⊆ C)
    (hri : (euclideanRelativeInterior_fin n D ∩ C').Nonempty) :
    D ⊆ C' := by
  classical
  let e := (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ))
  have hC'e_face : IsFace (𝕜 := ℝ) (e.symm '' C) (e.symm '' C') :=
    isFace_image_equiv_fin (n := n) (C := C) (C' := C') hC'
  have hDC' : e.symm '' D ⊆ e.symm '' C := by
    intro x hx
    rcases hx with ⟨x', hx', rfl⟩
    exact ⟨x', hDC hx', rfl⟩
  have hri' : (euclideanRelativeInterior n (e.symm '' D) ∩ e.symm '' C').Nonempty := by
    rcases hri with ⟨z, hz⟩
    rcases hz with ⟨hzri, hzC'⟩
    have hzri' :
        e.symm z ∈ euclideanRelativeInterior n (e.symm '' D) :=
      (mem_euclideanRelativeInterior_fin_iff (n := n) (C := D) (x := z)).1 hzri
    have hzC'' : e.symm z ∈ e.symm '' C' := ⟨z, hzC', rfl⟩
    exact ⟨e.symm z, ⟨hzri', hzC''⟩⟩
  have hsubsetE :
      e.symm '' D ⊆ e.symm '' C' :=
    subset_of_isFace_of_convex_of_euclideanRelativeInterior_inter (n := n)
      (C := e.symm '' C) (C' := e.symm '' C') (D := e.symm '' D) hC'e_face hDC' hri'
  intro x hxD
  have hxE : e.symm x ∈ e.symm '' D := ⟨x, hxD, rfl⟩
  have hxE' : e.symm x ∈ e.symm '' C' := hsubsetE hxE
  rcases hxE' with ⟨y, hyC', hyEq⟩
  have hyEq' : y = x := by
    apply e.symm.injective
    simpa [eq_comm] using hyEq
  simpa [hyEq'] using hyC'

/-- Theorem 18.3. Let `C = conv S`, where `S` is a set of points and directions, and let `C'` be a
non-empty face of `C`. Then `C' = conv S'`, where `S'` consists of the points in `S` which belong
to `C'` and the directions in `S` which are directions of recession of `C'`. -/
theorem face_mixedConvexHull_eq_mixedConvexHull_inter_recessionCone {n : ℕ}
    (S₀ S₁ : Set (Fin n → ℝ)) {C' : Set (Fin n → ℝ)}
    (hC' : IsFace (𝕜 := ℝ) (mixedConvexHull (n := n) S₀ S₁) C')
    (hC'conv : Convex ℝ C') :
    C' = mixedConvexHull (n := n) (S₀ ∩ C') (S₁ ∩ Set.recessionCone C') := by
  classical
  refine Set.Subset.antisymm ?_ ?_
  · intro x hxC'
    have hxC : x ∈ mixedConvexHull (n := n) S₀ S₁ := hC'.2.subset hxC'
    rcases
        exists_strict_mixedConvexCombination_of_mem_mixedConvexHull (n := n) (S₀ := S₀)
          (S₁ := S₁) (x := x) hxC with
      ⟨k, m, p, d, a, b, hp, hd, ha, hb, hsum, hxeq⟩
    let D : Set (Fin n → ℝ) := mixedConvexHull (n := n) (Set.range p) (Set.range d)
    have hxD : x ∈ D := by
      refine
        mem_mixedConvexHull_range_of_exists_coeffs (n := n) (p := p) (d := d) (y := x) a b
          (fun i => le_of_lt (ha i)) (fun j => le_of_lt (hb j)) hsum ?_
      simp [hxeq]
    have hxri : x ∈ euclideanRelativeInterior_fin n D := by
      refine
        mem_euclideanRelativeInterior_mixedConvexHull_range_of_strict_mixedConvexCombination
          (n := n) (p := p) (d := d) (a := a) (b := b) ha hb hsum ?_
      simp [hxeq]
    have hDsubsetC : D ⊆ mixedConvexHull (n := n) S₀ S₁ := by
      refine mixedConvexHull_mono (n := n) ?_ ?_
      · intro y hy
        rcases hy with ⟨i, rfl⟩
        exact hp i
      · intro y hy
        rcases hy with ⟨j, rfl⟩
        exact hd j
    have hDsubsetC' : D ⊆ C' := by
      refine
        subset_of_isFace_of_convex_of_euclideanRelativeInterior_fin_inter
          (C := mixedConvexHull (n := n) S₀ S₁) (C' := C') (D := D) hC' hDsubsetC ?_
      exact ⟨x, ⟨hxri, hxC'⟩⟩
    have hpC' : Set.range p ⊆ S₀ ∩ C' := by
      intro y hy
      rcases hy with ⟨i, rfl⟩
      have h0ray : (0 : Fin n → ℝ) ∈ ray n (Set.range d) := by
        exact (Set.mem_insert_iff).2 (Or.inl rfl)
      have hyadd : p i + (0 : Fin n → ℝ) ∈ Set.range p + ray n (Set.range d) :=
        Set.add_mem_add ⟨i, rfl⟩ h0ray
      have hyD : p i ∈ D := by
        have hyD' :
            p i + (0 : Fin n → ℝ) ∈ D :=
          (add_ray_subset_mixedConvexHull (n := n) (S₀ := Set.range p) (S₁ := Set.range d))
            (by simpa using hyadd)
        simpa using hyD'
      exact ⟨hp i, hDsubsetC' hyD⟩
    have hdC' : Set.range d ⊆ S₁ ∩ Set.recessionCone C' := by
      intro y hy
      rcases hy with ⟨j, rfl⟩
      have hdjD : d j ∈ Set.recessionCone D := by
        exact
          mem_recessionCone_mixedConvexHull_of_mem_directions (n := n)
            (S₀ := Set.range p) (S₁ := Set.range d) (d := d j) ⟨j, rfl⟩
      have hRayC' : ∀ t : ℝ, 0 ≤ t → x + t • d j ∈ C' := by
        intro t ht
        have hxD' : x + t • d j ∈ D := hdjD (x := x) hxD (t := t) ht
        exact hDsubsetC' hxD'
      have hdjCl : d j ∈ Set.recessionCone (closure C') := by
        refine
          mem_recessionCone_closure_of_exists_ray (n := n) (K := C') (d := d j) hC'conv ?_
        exact ⟨x, hxC', hRayC'⟩
      have hdjC : d j ∈ Set.recessionCone (mixedConvexHull (n := n) S₀ S₁) := by
        exact
          mem_recessionCone_mixedConvexHull_of_mem_directions (n := n)
            (S₀ := S₀) (S₁ := S₁) (d := d j) (hd := hd j)
      have hdjC' : d j ∈ Set.recessionCone C' :=
        mem_recessionCone_face_of_mem_recessionCone_of_mem_recessionCone_closure
          (n := n) (S₀ := S₀) (S₁ := S₁) (C' := C') hC' hC'conv hdjC hdjCl
      exact ⟨hd j, hdjC'⟩
    have hmono :
        D ⊆ mixedConvexHull (n := n) (S₀ ∩ C') (S₁ ∩ Set.recessionCone C') :=
      mixedConvexHull_mono (n := n) (S₀ := Set.range p) (S₁ := Set.range d)
        (T₀ := S₀ ∩ C') (T₁ := S₁ ∩ Set.recessionCone C') hpC' hdC'
    exact hmono hxD
  ·
    refine
      mixedConvexHull_subset_of_convex_of_subset_of_recedes (n := n)
        (S₀ := S₀ ∩ C') (S₁ := S₁ ∩ Set.recessionCone C') (Ccand := C') hC'conv
        (by intro x hx; exact hx.2) ?_
    intro d hd x hx t ht
    exact hd.2 hx (t := t) ht

/-- A singleton face arises from an extreme point of a mixed convex hull. -/
lemma isFace_singleton_of_isExtremePoint_mixedConvexHull {n : ℕ} {S₀ S₁ : Set (Fin n → ℝ)}
    {x : Fin n → ℝ}
    (hx : IsExtremePoint (𝕜 := ℝ) (mixedConvexHull (n := n) S₀ S₁) x) :
    IsFace (𝕜 := ℝ) (mixedConvexHull (n := n) S₀ S₁) ({x} : Set (Fin n → ℝ)) := by
  have hconv : Convex ℝ (mixedConvexHull (n := n) S₀ S₁) :=
    convex_mixedConvexHull (n := n) S₀ S₁
  have hface :
      Convex ℝ (mixedConvexHull (n := n) S₀ S₁) ∧
        IsExtremePoint (𝕜 := ℝ) (mixedConvexHull (n := n) S₀ S₁) x := by
    exact ⟨hconv, hx⟩
  simpa using
    (isFace_singleton_iff_isExtremePoint (𝕜 := ℝ)
      (C := mixedConvexHull (n := n) S₀ S₁) x).2 hface

/-- Corollary 18.3.1. Suppose `C = conv S`, where `S` is given as a set of points `S₀` and
directions `S₁` (so here `C = mixedConvexHull S₀ S₁`). Then every extreme point of `C` is a point
of `S` (i.e. lies in `S₀`). -/
theorem mem_points_of_isExtremePoint_mixedConvexHull {n : ℕ} {S₀ S₁ : Set (Fin n → ℝ)}
    {x : Fin n → ℝ} :
    IsExtremePoint (𝕜 := ℝ) (mixedConvexHull (n := n) S₀ S₁) x → x ∈ S₀ := by
  intro hxext
  classical
  have hface :
      IsFace (𝕜 := ℝ) (mixedConvexHull (n := n) S₀ S₁) ({x} : Set (Fin n → ℝ)) :=
    isFace_singleton_of_isExtremePoint_mixedConvexHull (n := n) (S₀ := S₀) (S₁ := S₁) hxext
  have hconv_singleton : Convex ℝ ({x} : Set (Fin n → ℝ)) := by
    simpa using (convex_singleton (x := x))
  have hEq :
      ({x} : Set (Fin n → ℝ)) =
        mixedConvexHull (n := n) (S₀ ∩ {x}) (S₁ ∩ Set.recessionCone ({x} : Set (Fin n → ℝ))) :=
    face_mixedConvexHull_eq_mixedConvexHull_inter_recessionCone (n := n)
      (S₀ := S₀) (S₁ := S₁) (C' := ({x} : Set (Fin n → ℝ))) hface hconv_singleton
  by_contra hxnot
  have hinter : S₀ ∩ ({x} : Set (Fin n → ℝ)) = (∅ : Set (Fin n → ℝ)) := by
    ext y
    constructor
    · intro hy
      rcases hy with ⟨hyS₀, hyx⟩
      have hyx' : y = x := by
        simpa using hyx
      subst hyx'
      exact (hxnot hyS₀).elim
    · intro hy
      cases hy
  have hEq' :
      ({x} : Set (Fin n → ℝ)) =
        mixedConvexHull (n := n) (∅ : Set (Fin n → ℝ))
          (S₁ ∩ Set.recessionCone ({x} : Set (Fin n → ℝ))) := by
    simpa [hinter] using hEq
  have hxmem : x ∈ ({x} : Set (Fin n → ℝ)) := by
    simp
  have hxmem' :
      x ∈ mixedConvexHull (n := n) (∅ : Set (Fin n → ℝ))
        (S₁ ∩ Set.recessionCone ({x} : Set (Fin n → ℝ))) := by
    rw [← hEq']
    exact hxmem
  have hEmpty :
      mixedConvexHull (n := n) (∅ : Set (Fin n → ℝ))
          (S₁ ∩ Set.recessionCone ({x} : Set (Fin n → ℝ))) =
        (∅ : Set (Fin n → ℝ)) := by
    simpa using
      (mixedConvexHull_empty_points (n := n)
        (S₁ := S₁ ∩ Set.recessionCone ({x} : Set (Fin n → ℝ))))
  have : x ∈ (∅ : Set (Fin n → ℝ)) := by
    simpa [hEmpty] using hxmem'
  simpa using this

/-- A half-line `{x + t • d | t ≥ 0}` is convex. -/
lemma convex_ray_image {n : ℕ} (x d : Fin n → ℝ) :
    Convex ℝ ((fun t : ℝ => x + t • d) '' Set.Ici (0 : ℝ)) := by
  have hconv : Convex ℝ (Set.Ici (0 : ℝ)) := by
    simpa using (convex_Ici (𝕜 := ℝ) (r := (0 : ℝ)))
  let f : ℝ →ᵃ[ℝ] (Fin n → ℝ) := AffineMap.lineMap x (x + d)
  have hconv' : Convex ℝ (f '' Set.Ici (0 : ℝ)) := hconv.affine_image f
  have hEq :
      f '' Set.Ici (0 : ℝ) =
        (fun t : ℝ => x + t • d) '' Set.Ici (0 : ℝ) := by
    ext y
    constructor
    · intro hy
      rcases hy with ⟨t, ht, rfl⟩
      refine ⟨t, ht, ?_⟩
      simp [f, AffineMap.lineMap_apply_module', add_comm, add_left_comm, add_assoc]
    · intro hy
      rcases hy with ⟨t, ht, rfl⟩
      refine ⟨t, ht, ?_⟩
      simp [f, AffineMap.lineMap_apply_module', add_comm, add_left_comm, add_assoc]
  simpa [hEq] using hconv'

/-- A half-line `{x + t • d | t ≥ 0}` is nonempty. -/
lemma ray_image_nonempty {n : ℕ} (x d : Fin n → ℝ) :
    ((fun t : ℝ => x + t • d) '' Set.Ici (0 : ℝ)).Nonempty := by
  refine ⟨x, ⟨0, ?_, by simp⟩⟩
  exact (by simp : (0 : ℝ) ∈ Set.Ici (0 : ℝ))

/-- The recession cone of a half-line is the nonnegative ray of its direction. -/
lemma recessionCone_ray_eq_rayNonneg_singleton {n : ℕ} (x d : Fin n → ℝ) :
    Set.recessionCone ((fun t : ℝ => x + t • d) '' Set.Ici (0 : ℝ)) =
      rayNonneg n ({d} : Set (Fin n → ℝ)) := by
  ext y
  constructor
  · intro hy
    have hx : x ∈ (fun t : ℝ => x + t • d) '' Set.Ici (0 : ℝ) := by
      refine ⟨0, by simp, by simp⟩
    have hy' : x + (1 : ℝ) • y ∈ (fun t : ℝ => x + t • d) '' Set.Ici (0 : ℝ) :=
      hy (x := x) hx (t := (1 : ℝ)) (by norm_num)
    have hy'' : x + y ∈ (fun t : ℝ => x + t • d) '' Set.Ici (0 : ℝ) := by
      simpa using hy'
    rcases hy'' with ⟨t, ht, hEq⟩
    have hEq' : y = t • d := by
      exact (add_left_cancel hEq).symm
    exact ⟨d, by simp, t, ht, hEq'⟩
  · intro hy
    rcases hy with ⟨x', hx', t, ht, rfl⟩
    have hx'' : x' = d := by
      simpa using hx'
    subst x'
    intro z hz s hs
    rcases hz with ⟨u, hu, rfl⟩
    refine ⟨u + s * t, ?_, ?_⟩
    · exact add_nonneg hu (mul_nonneg hs ht)
    · simp [smul_smul, add_smul, add_assoc, add_comm, add_left_comm, mul_comm, mul_left_comm,
        mul_assoc]

/-- If a positive multiple of `d` lies in `S₁`, then `d` lies in `rayNonneg n S₁`. -/
lemma mem_rayNonneg_of_exists_pos_smul_mem {n : ℕ} {S₁ : Set (Fin n → ℝ)} {d : Fin n → ℝ}
    (h : ∃ s ∈ S₁, ∃ a : ℝ, 0 < a ∧ s = a • d) :
    d ∈ rayNonneg n S₁ := by
  rcases h with ⟨s, hs, a, ha, hsd⟩
  have ha_ne : a ≠ 0 := by exact ne_of_gt ha
  have hda : d = a⁻¹ • s := by
    calc
      d = a⁻¹ • (a • d) := by
            simp [smul_smul, ha_ne]
      _ = a⁻¹ • s := by
            simp [hsd]
  refine ⟨s, hs, a⁻¹, ?_, hda⟩
  exact inv_nonneg.mpr (le_of_lt ha)

/-- A nonzero ray `{x + t • d | t ≥ 0}` is unbounded. -/
lemma not_isBounded_ray_image_of_ne_zero {n : ℕ} {x d : Fin n → ℝ} (hd : d ≠ 0) :
    ¬ Bornology.IsBounded ((fun t : ℝ => x + t • d) '' Set.Ici (0 : ℝ)) := by
  intro hbounded
  rcases (Metric.isBounded_iff_subset_closedBall (c := x)).1 hbounded with ⟨r, hr⟩
  have hxmem : x ∈ (fun t : ℝ => x + t • d) '' Set.Ici (0 : ℝ) := by
    refine ⟨0, by simp, by simp⟩
  have hr_nonneg : 0 ≤ r := by
    have hxball : x ∈ Metric.closedBall x r := hr hxmem
    have : dist x x ≤ r := (Metric.mem_closedBall).1 hxball
    simpa using this
  have hnorm_pos : 0 < ‖d‖ := (norm_pos_iff.mpr hd)
  have hnorm_ne : ‖d‖ ≠ 0 := ne_of_gt hnorm_pos
  let t : ℝ := r / ‖d‖ + 1
  have ht : 0 ≤ t := by
    have : 0 ≤ r / ‖d‖ := div_nonneg hr_nonneg (le_of_lt hnorm_pos)
    exact add_nonneg this (by norm_num)
  have ht_mem : t ∈ Set.Ici (0 : ℝ) := ht
  have hx_t : x + t • d ∈ (fun t : ℝ => x + t • d) '' Set.Ici (0 : ℝ) := ⟨t, ht_mem, rfl⟩
  have hxball : x + t • d ∈ Metric.closedBall x r := hr hx_t
  have hdist_le : dist (x + t • d) x ≤ r := (Metric.mem_closedBall).1 hxball
  have hdist_eq : dist (x + t • d) x = t * ‖d‖ := by
    calc
      dist (x + t • d) x = ‖t • d‖ := by
        simp [dist_eq_norm, add_sub_cancel_left]
      _ = t * ‖d‖ := by
        simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
  have hdist_gt : r < dist (x + t • d) x := by
    have ht_mul : t * ‖d‖ = r + ‖d‖ := by
      dsimp [t]
      field_simp [hnorm_ne]
    have : r < r + ‖d‖ := by linarith [hnorm_pos]
    simpa [hdist_eq, ht_mul] using this
  exact (not_lt_of_ge hdist_le hdist_gt)

/-- If a direction set is contained in `{0}`, its cone is `{0}`. -/
lemma cone_eq_singleton_zero_of_subset {n : ℕ} {S : Set (Fin n → ℝ)}
    (hS : S ⊆ ({0} : Set (Fin n → ℝ))) :
    cone n S = ({0} : Set (Fin n → ℝ)) := by
  have hRay : ray n S = ({0} : Set (Fin n → ℝ)) := by
    ext y
    constructor
    · intro hy
      have hy' : y = 0 ∨ y ∈ rayNonneg n S := by
        simpa [ray, Set.mem_insert_iff] using hy
      cases hy' with
      | inl hy0 =>
          simpa [hy0]
      | inr hyray =>
          rcases hyray with ⟨x, hxS, t, ht, rfl⟩
          have hx0 : x = 0 := by
            have hx0' : x ∈ ({0} : Set (Fin n → ℝ)) := hS hxS
            simpa using hx0'
          simp [hx0]
    · intro hy
      have hy0 : y = 0 := by simpa using hy
      subst hy0
      exact (Set.mem_insert_iff).2 (Or.inl rfl)
  simpa [cone, conv, hRay] using (convexHull_singleton (0 : Fin n → ℝ))

/-- A half-line face of a mixed convex hull yields a nonzero direction from `S₁`. -/
lemma exists_ne_zero_mem_S₁_inter_recessionCone_of_face_ray {n : ℕ}
    {S₀ S₁ : Set (Fin n → ℝ)} {x d : Fin n → ℝ}
    (hd : d ≠ 0)
    (hface :
      IsFace (𝕜 := ℝ) (mixedConvexHull (n := n) S₀ S₁)
        ((fun t : ℝ => x + t • d) '' Set.Ici (0 : ℝ)))
    (hconv : Convex ℝ ((fun t : ℝ => x + t • d) '' Set.Ici (0 : ℝ)))
    (hNoUnbounded :
      ∀ x d' : Fin n → ℝ,
        ((fun t : ℝ => x + t • d') '' Set.Ici (0 : ℝ)) ⊆ mixedConvexHull (n := n) S₀ S₁ →
          Bornology.IsBounded (S₀ ∩ ((fun t : ℝ => x + t • d') '' Set.Ici (0 : ℝ)))) :
    ∃ s, s ∈ S₁ ∩ Set.recessionCone ((fun t : ℝ => x + t • d) '' Set.Ici (0 : ℝ)) ∧ s ≠ 0 := by
  classical
  set C' : Set (Fin n → ℝ) := (fun t : ℝ => x + t • d) '' Set.Ici (0 : ℝ) with hC'
  have hface' : IsFace (𝕜 := ℝ) (mixedConvexHull (n := n) S₀ S₁) C' := by
    simpa [hC'] using hface
  have hconv' : Convex ℝ C' := by
    simpa [hC'] using hconv
  have hCsub : C' ⊆ mixedConvexHull (n := n) S₀ S₁ := hface'.2.subset
  have hS0bdd : Bornology.IsBounded (S₀ ∩ C') := hNoUnbounded x d hCsub
  have hEq :
      C' = mixedConvexHull (n := n) (S₀ ∩ C') (S₁ ∩ Set.recessionCone C') := by
    simpa [hC'] using
      (face_mixedConvexHull_eq_mixedConvexHull_inter_recessionCone (n := n)
        (S₀ := S₀) (S₁ := S₁) (C' := C') hface' hconv')
  have hnot : ¬ S₁ ∩ Set.recessionCone C' ⊆ ({0} : Set (Fin n → ℝ)) := by
    intro hsub
    have hcone0 :
        cone n (S₁ ∩ Set.recessionCone C') = ({0} : Set (Fin n → ℝ)) :=
      cone_eq_singleton_zero_of_subset (n := n) (S := S₁ ∩ Set.recessionCone C') hsub
    have hrepr :=
      mixedConvexHull_eq_conv_add_ray_eq_conv_add_cone (n := n)
        (S₀ := S₀ ∩ C') (S₁ := S₁ ∩ Set.recessionCone C')
    have hEq' :
        C' = conv (S₀ ∩ C') + cone n (S₁ ∩ Set.recessionCone C') := by
      have hEq'' :
          mixedConvexHull (n := n) (S₀ ∩ C') (S₁ ∩ Set.recessionCone C') =
            conv (S₀ ∩ C') + cone n (S₁ ∩ Set.recessionCone C') := by
        exact hrepr.1.trans hrepr.2
      simpa [hEq''] using hEq
    have hconv_bd : Bornology.IsBounded (conv (S₀ ∩ C')) := by
      simpa [conv] using (isBounded_convexHull (s := S₀ ∩ C')).2 hS0bdd
    have hcone_bd : Bornology.IsBounded (cone n (S₁ ∩ Set.recessionCone C')) := by
      simpa [hcone0] using (Bornology.isBounded_singleton (x := (0 : Fin n → ℝ)))
    have hsum_bd :
        Bornology.IsBounded (conv (S₀ ∩ C') + cone n (S₁ ∩ Set.recessionCone C')) :=
      isBounded_add hconv_bd hcone_bd
    have hC'bd : Bornology.IsBounded C' := by
      rw [hEq']
      exact hsum_bd
    have hnotbdd : ¬ Bornology.IsBounded C' := by
      simpa [hC'] using
        (not_isBounded_ray_image_of_ne_zero (n := n) (x := x) (d := d) hd)
    exact (hnotbdd hC'bd)
  rcases (Set.not_subset.mp hnot) with ⟨s, hs, hsnot⟩
  refine ⟨s, hs, ?_⟩
  simpa using hsnot

/-- Corollary 18.3.1. Suppose `C = conv S`, where `S` is given as a set of points `S₀` and
directions `S₁` (so `C = mixedConvexHull S₀ S₁`). If no half-line in `C` contains an unbounded set
of points of `S` (i.e. along any ray contained in `C`, the subset of points from `S₀` is bounded),
then every extreme direction of `C` is a nonnegative multiple of a direction in `S₁`. -/
theorem mem_directions_of_isExtremeDirection_mixedConvexHull {n : ℕ} {S₀ S₁ : Set (Fin n → ℝ)}
    {d : Fin n → ℝ}
    (hNoUnbounded :
      ∀ x d' : Fin n → ℝ,
        ((fun t : ℝ => x + t • d') '' Set.Ici (0 : ℝ)) ⊆ mixedConvexHull (n := n) S₀ S₁ →
          Bornology.IsBounded (S₀ ∩ ((fun t : ℝ => x + t • d') '' Set.Ici (0 : ℝ)))) :
    IsExtremeDirection (𝕜 := ℝ) (mixedConvexHull (n := n) S₀ S₁) d → d ∈ rayNonneg n S₁ := by
  intro hdext
  classical
  rcases hdext with ⟨C', hhalf, hdir⟩
  rcases hdir with ⟨x, hdne, hC'Eq⟩
  have hface : IsFace (𝕜 := ℝ) (mixedConvexHull (n := n) S₀ S₁) C' := hhalf.1
  have hface' :
      IsFace (𝕜 := ℝ) (mixedConvexHull (n := n) S₀ S₁)
        ((fun t : ℝ => x + t • d) '' Set.Ici (0 : ℝ)) := by
    simpa [hC'Eq] using hface
  have hconv' : Convex ℝ ((fun t : ℝ => x + t • d) '' Set.Ici (0 : ℝ)) :=
    convex_ray_image (n := n) x d
  obtain ⟨s, hs, hsne⟩ :=
    exists_ne_zero_mem_S₁_inter_recessionCone_of_face_ray (n := n)
      (S₀ := S₀) (S₁ := S₁) (x := x) (d := d) hdne hface' hconv' hNoUnbounded
  have hs_rec : s ∈ Set.recessionCone ((fun t : ℝ => x + t • d) '' Set.Ici (0 : ℝ)) := hs.2
  have hs_ray : s ∈ rayNonneg n ({d} : Set (Fin n → ℝ)) := by
    simpa [recessionCone_ray_eq_rayNonneg_singleton (n := n) (x := x) (d := d)] using hs_rec
  rcases hs_ray with ⟨x', hx', t, ht, hsd⟩
  have hx'' : x' = d := by
    simpa using hx'
  subst x'
  have htpos : 0 < t := by
    have htne : t ≠ 0 := by
      intro ht0
      apply hsne
      simp [hsd, ht0]
    exact lt_of_le_of_ne ht (by symm; exact htne)
  refine mem_rayNonneg_of_exists_pos_smul_mem (n := n) (S₁ := S₁) (d := d) ?_
  exact ⟨s, hs.1, t, htpos, hsd⟩

/-- Lineality directions translate points of a convex set. -/
lemma add_sub_mem_of_mem_linealitySpace {n : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))}
    (hC : Convex ℝ C) {v x : EuclideanSpace ℝ (Fin n)}
    (hv : v ∈ Set.linealitySpace C) (hx : x ∈ C) :
    x + v ∈ C ∧ x - v ∈ C := by
  have hv' : v ∈ (-Set.recessionCone C) ∩ Set.recessionCone C := by
    simpa [Set.linealitySpace] using hv
  have hvpos : v ∈ Set.recessionCone C := hv'.2
  have hvneg : -v ∈ Set.recessionCone C := by
    simpa [Set.mem_neg] using hv'.1
  have hpos : x + v ∈ C := by
    have hvpos' : v ∈ { y | ∀ x ∈ C, x + y ∈ C } := by
      simpa [recessionCone_eq_add_mem (C := C) hC] using hvpos
    exact hvpos' x hx
  have hneg : x - v ∈ C := by
    have hvneg' : (-v) ∈ { y | ∀ x ∈ C, x + y ∈ C } := by
      simpa [recessionCone_eq_add_mem (C := C) hC] using hvneg
    have : x + (-v) ∈ C := hvneg' x hx
    simpa [sub_eq_add_neg] using this
  exact ⟨hpos, hneg⟩

/-- The midpoint of `x + v` and `x - v` lies in their open segment. -/
lemma mem_openSegment_add_sub_half {n : ℕ} (x v : EuclideanSpace ℝ (Fin n)) :
    x ∈ openSegment ℝ (x + v) (x - v) := by
  refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num, by norm_num, ?_⟩
  have hmid : (1 / 2 : ℝ) • (x + v) + (1 / 2 : ℝ) • (x - v) = x := by
    calc
      (1 / 2 : ℝ) • (x + v) + (1 / 2 : ℝ) • (x - v)
          = (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • x := by
              simp [sub_eq_add_neg, smul_add, smul_neg, add_assoc, add_left_comm, add_comm]
      _ = ((1 / 2 : ℝ) + (1 / 2 : ℝ)) • x := by
              simpa using
                (add_smul (r := (1 / 2 : ℝ)) (s := (1 / 2 : ℝ)) (x := x)).symm
      _ = x := by norm_num
  exact hmid

/-- A nonzero lineality direction prevents extreme points. -/
lemma not_mem_extremePoints_of_exists_nonzero_lineality {n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin n))} (hC : Convex ℝ C)
    {v : EuclideanSpace ℝ (Fin n)} (hv0 : v ≠ 0) (hvL : v ∈ Set.linealitySpace C) :
    ∀ x, x ∉ C.extremePoints ℝ := by
  intro x hxext
  have hxC : x ∈ C := hxext.1
  have hxaddsub :
      x + v ∈ C ∧ x - v ∈ C :=
    add_sub_mem_of_mem_linealitySpace (n := n) (C := C) hC hvL hxC
  have hxseg : x ∈ openSegment ℝ (x + v) (x - v) :=
    mem_openSegment_add_sub_half (n := n) x v
  have hxleft : x + v = x :=
    hxext.2 (x₁ := x + v) hxaddsub.1 (x₂ := x - v) hxaddsub.2 hxseg
  have hvzero : v = 0 := by
    have hxleft' : x + v = x + 0 := by
      simpa using hxleft
    exact add_left_cancel hxleft'
  exact hv0 hvzero

/-- Text 18.3.1. If the lineality space `L` of a convex set `C` is non-zero (equivalently: `C`
contains at least one line), then `C` has no extreme points. -/
theorem extremePoints_eq_empty_of_linealitySpace_nontrivial {n : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin n))) (hC : Convex ℝ C)
    (hL : ∃ y : EuclideanSpace ℝ (Fin n), y ≠ 0 ∧ y ∈ Set.linealitySpace C) :
    C.extremePoints ℝ = ∅ := by
  classical
  rcases hL with ⟨v, hv0, hvL⟩
  refine Set.eq_empty_iff_forall_notMem.mpr ?_
  intro x hx
  exact not_mem_extremePoints_of_exists_nonzero_lineality (n := n) (C := C) hC hv0 hvL x hx

/-- For a closed set, the relative boundary is `C \ ri C`. -/
lemma euclideanRelativeBoundary_eq_diff_of_isClosed {n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin n))} (hC : IsClosed C) :
    euclideanRelativeBoundary n C = C \ euclideanRelativeInterior n C := by
  simpa [euclideanRelativeBoundary, hC.closure_eq]

/-- From nonconvex relative boundary, pick boundary endpoints with a relative interior point
on their open segment. -/
lemma exists_two_rb_points_with_ri_point_on_openSegment {n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin n))} (hCclosed : IsClosed C) (hCconv : Convex ℝ C)
    (hnotconv : ¬ Convex ℝ (euclideanRelativeBoundary n C)) :
    ∃ x₁ x₂ : EuclideanSpace ℝ (Fin n),
      x₁ ∈ euclideanRelativeBoundary n C ∧ x₂ ∈ euclideanRelativeBoundary n C ∧ x₁ ≠ x₂ ∧
        ∃ y : EuclideanSpace ℝ (Fin n),
          y ∈ euclideanRelativeInterior n C ∧ y ∈ openSegment ℝ x₁ x₂ := by
  classical
  set D : Set (EuclideanSpace ℝ (Fin n)) := euclideanRelativeBoundary n C
  have hnot' :
      ¬ ∀ x₁ ∈ D, ∀ x₂ ∈ D, openSegment ℝ x₁ x₂ ⊆ D := by
    intro h
    apply hnotconv
    exact (convex_iff_openSegment_subset).2 (by intro x hx y hy; exact h x hx y hy)
  have hnot'' :
      ∃ x₁ ∈ D, ∃ x₂ ∈ D, ∃ z, z ∈ openSegment ℝ x₁ x₂ ∧ z ∉ D := by
    by_contra hcontra
    have hsubset : ∀ x₁ ∈ D, ∀ x₂ ∈ D, openSegment ℝ x₁ x₂ ⊆ D := by
      intro x₁ hx₁ x₂ hx₂ z hz
      by_contra hznot
      apply hcontra
      exact ⟨x₁, hx₁, x₂, hx₂, z, hz, hznot⟩
    exact hnot' hsubset
  rcases hnot'' with ⟨x₁, hx₁D, x₂, hx₂D, z, hzseg, hznotD⟩
  have hD_eq :
      D = C \ euclideanRelativeInterior n C := by
    simpa [D] using (euclideanRelativeBoundary_eq_diff_of_isClosed (n := n) (C := C) hCclosed)
  have hx₁C : x₁ ∈ C := by
    have : x₁ ∈ C \ euclideanRelativeInterior n C := by simpa [hD_eq] using hx₁D
    exact this.1
  have hx₂C : x₂ ∈ C := by
    have : x₂ ∈ C \ euclideanRelativeInterior n C := by simpa [hD_eq] using hx₂D
    exact this.1
  have hzC : z ∈ C := by
    have hsegC : segment ℝ x₁ x₂ ⊆ C := hCconv.segment_subset hx₁C hx₂C
    rcases hzseg with ⟨a, b, ha, hb, hab, rfl⟩
    have hzseg' : (a • x₁ + b • x₂) ∈ segment ℝ x₁ x₂ :=
      ⟨a, b, le_of_lt ha, le_of_lt hb, hab, rfl⟩
    exact hsegC hzseg'
  have hzri : z ∈ euclideanRelativeInterior n C := by
    have hznot' : z ∉ C \ euclideanRelativeInterior n C := by simpa [hD_eq] using hznotD
    by_contra hzri'
    exact hznot' ⟨hzC, hzri'⟩
  have hx₁x₂ : x₁ ≠ x₂ := by
    intro h
    subst h
    have hzmem : z ∈ ({x₁} : Set (EuclideanSpace ℝ (Fin n))) := by
      have : z ∈ openSegment ℝ x₁ x₁ := by simpa using hzseg
      have hopen : openSegment ℝ x₁ x₁ = ({x₁} : Set (EuclideanSpace ℝ (Fin n))) := by
        simpa using (openSegment_same (𝕜 := ℝ) x₁)
      simpa [hopen] using this
    have : z ∈ D := by
      have : z = x₁ := by simpa using hzmem
      simpa [this] using hx₁D
    exact hznotD this
  refine ⟨x₁, x₂, hx₁D, hx₂D, hx₁x₂, z, hzri, ?_⟩
  exact hzseg

/-- If `y ∈ ri C` and `x ∈ aff C` lies outside `C`, then the open segment `y–x` meets `rb C`. -/
lemma exists_rb_point_on_segment_of_mem_ri_of_not_mem {n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin n))} (hCclosed : IsClosed C)
    {y x : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ euclideanRelativeInterior n C)
    (hxaff : x ∈ affineSpan ℝ C) (hxC : x ∉ C) :
    ∃ z, z ∈ euclideanRelativeBoundary n C ∧ z ∈ openSegment ℝ y x := by
  classical
  have hyC : y ∈ C := (euclideanRelativeInterior_subset_closure n C).1 hy
  have hxne : x ≠ y := by
    intro hxy
    apply hxC
    simpa [hxy] using hyC
  rcases hy with ⟨hy_aff, ε, hε, hsub⟩
  set v : EuclideanSpace ℝ (Fin n) := x - y
  have hv0 : v ≠ 0 := by
    intro hv
    apply hxne
    have : x - y = 0 := by simpa [v] using hv
    exact sub_eq_zero.mp this
  have hvnorm : 0 < ‖v‖ := by simpa using (norm_pos_iff.mpr hv0)
  have hvdir : v ∈ (affineSpan ℝ C).direction := by
    have hv' : x -ᵥ y ∈ (affineSpan ℝ C).direction :=
      (affineSpan ℝ C).vsub_mem_direction hxaff hy_aff
    simpa [vsub_eq_sub, v] using hv'
  let g : ℝ → EuclideanSpace ℝ (Fin n) := fun t => AffineMap.lineMap y x t
  let S : Set ℝ := g ⁻¹' C ∩ Set.Icc (0 : ℝ) 1
  have hcont : Continuous g := by
    simpa [g] using (AffineMap.lineMap_continuous (p := y) (q := x))
  have hSclosed : IsClosed S := (hCclosed.preimage hcont).inter isClosed_Icc
  have hScompact : IsCompact S :=
    IsCompact.of_isClosed_subset isCompact_Icc hSclosed (by intro t ht; exact ht.2)
  have hSnonempty : S.Nonempty := by
    refine ⟨0, ?_⟩
    have h0C : g 0 ∈ C := by
      simpa [g, AffineMap.lineMap_apply_module] using hyC
    have h0I : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
    exact ⟨h0C, h0I⟩
  obtain ⟨t0, ht0S, ht0max⟩ :=
    hScompact.exists_isMaxOn hSnonempty (continuous_id.continuousOn)
  have ht0max' : ∀ t ∈ S, t ≤ t0 := (isMaxOn_iff).1 ht0max
  have ht0le1 : t0 ≤ 1 := ht0S.2.2
  have ht0ne1 : t0 ≠ 1 := by
    intro ht0eq
    apply hxC
    have hxC' : g t0 ∈ C := ht0S.1
    simpa [g, ht0eq, AffineMap.lineMap_apply_module] using hxC'
  have ht0lt1 : t0 < 1 := lt_of_le_of_ne ht0le1 ht0ne1
  -- Produce a positive parameter in `S` from `y ∈ ri C`.
  set t1 : ℝ := min (ε / ‖v‖) (1 / 2 : ℝ)
  have ht1pos : 0 < t1 := by
    have h1 : 0 < ε / ‖v‖ := div_pos hε hvnorm
    have h2 : 0 < (1 / 2 : ℝ) := by norm_num
    exact (lt_min_iff).2 ⟨h1, h2⟩
  have ht1le : t1 ≤ ε / ‖v‖ := min_le_left _ _
  have ht1lehalf : t1 ≤ (1 / 2 : ℝ) := min_le_right _ _
  have ht1Icc : t1 ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨le_of_lt ht1pos, ?_⟩
    linarith [ht1lehalf]
  have hnorm : ‖t1 • v‖ ≤ ε := by
    have ht1nonneg : 0 ≤ t1 := le_of_lt ht1pos
    have hle : t1 * ‖v‖ ≤ (ε / ‖v‖) * ‖v‖ :=
      mul_le_mul_of_nonneg_right ht1le (norm_nonneg v)
    have hvne : (‖v‖ : ℝ) ≠ 0 := by exact ne_of_gt hvnorm
    have hcalc : (ε / ‖v‖) * ‖v‖ = ε := by
      field_simp [hvne]
    calc
      ‖t1 • v‖ = t1 * ‖v‖ := by
        simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht1nonneg]
      _ ≤ (ε / ‖v‖) * ‖v‖ := hle
      _ = ε := hcalc
  have ht1ball : t1 • v ∈ ε • euclideanUnitBall n :=
    mem_smul_unitBall_of_norm_le hε hnorm
  have ht1aff : g t1 ∈ affineSpan ℝ C := by
    have h := AffineMap.lineMap_mem (Q := affineSpan ℝ C) (p₀ := y) (p₁ := x) t1 hy_aff hxaff
    simpa [g, AffineMap.lineMap_apply_module] using h
  have ht1C : g t1 ∈ C := by
    have ht1img :
        g t1 ∈ (fun z => y + z) '' (ε • euclideanUnitBall n) := by
      refine ⟨t1 • v, ht1ball, ?_⟩
      simp [g, v, AffineMap.lineMap_apply_module', add_comm, add_left_comm, add_assoc,
        sub_eq_add_neg]
    exact hsub ⟨ht1img, ht1aff⟩
  have ht1S : t1 ∈ S := ⟨ht1C, ht1Icc⟩
  have ht0pos : 0 < t0 := by
    have ht1le0 : t1 ≤ t0 := ht0max' t1 ht1S
    exact lt_of_lt_of_le ht1pos ht1le0
  set z : EuclideanSpace ℝ (Fin n) := g t0
  have hzC : z ∈ C := ht0S.1
  have hz_aff : z ∈ affineSpan ℝ C := by
    have h := AffineMap.lineMap_mem (Q := affineSpan ℝ C) (p₀ := y) (p₁ := x) t0 hy_aff hxaff
    simpa [z, g, AffineMap.lineMap_apply_module] using h
  have hzseg : z ∈ openSegment ℝ y x := by
    refine ⟨1 - t0, t0, ?_, ?_, ?_, ?_⟩
    · linarith [ht0lt1]
    · exact ht0pos
    · linarith
    · simpa [z, g, AffineMap.lineMap_apply_module] using (rfl : g t0 = g t0)
  have hz_not_ri : z ∉ euclideanRelativeInterior n C := by
    intro hzri
    rcases hzri with ⟨hz_aff', εz, hεz, hzsub⟩
    set δ : ℝ := min (εz / ‖v‖) ((1 - t0) / 2)
    have hδpos : 0 < δ := by
      have h1 : 0 < εz / ‖v‖ := div_pos hεz hvnorm
      have h2 : 0 < (1 - t0) / 2 := by linarith [ht0lt1]
      exact (lt_min_iff).2 ⟨h1, h2⟩
    have hδle : δ ≤ εz / ‖v‖ := min_le_left _ _
    have hδle' : δ ≤ (1 - t0) / 2 := min_le_right _ _
    have hδnonneg : 0 ≤ δ := le_of_lt hδpos
    have hnorm' : ‖δ • v‖ ≤ εz := by
      have hle : δ * ‖v‖ ≤ (εz / ‖v‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right hδle (norm_nonneg v)
      have hvne : (‖v‖ : ℝ) ≠ 0 := by exact ne_of_gt hvnorm
      have hcalc : (εz / ‖v‖) * ‖v‖ = εz := by
        field_simp [hvne]
      calc
        ‖δ • v‖ = δ * ‖v‖ := by
          simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hδnonneg]
        _ ≤ (εz / ‖v‖) * ‖v‖ := hle
        _ = εz := hcalc
    have hδball : δ • v ∈ εz • euclideanUnitBall n :=
      mem_smul_unitBall_of_norm_le hεz hnorm'
    have hzplus_aff : z + δ • v ∈ affineSpan ℝ C := by
      have hdir : δ • v ∈ (affineSpan ℝ C).direction :=
        (affineSpan ℝ C).direction.smul_mem δ hvdir
      have hz' : (δ • v) +ᵥ z ∈ affineSpan ℝ C :=
        AffineSubspace.vadd_mem_of_mem_direction (s := affineSpan ℝ C) hdir hz_aff
      simpa [vadd_eq_add, add_comm] using hz'
    have hzplusC : z + δ • v ∈ C := by
      have hzimg :
          z + δ • v ∈ (fun w => z + w) '' (εz • euclideanUnitBall n) := by
        refine ⟨δ • v, hδball, by simp⟩
      exact hzsub ⟨hzimg, hzplus_aff⟩
    have hz_eq : z = y + t0 • v := by
      simp [z, g, v, AffineMap.lineMap_apply_module', add_comm, add_left_comm, add_assoc]
    have htdir : g (t0 + δ) = z + δ • v := by
      calc
        g (t0 + δ) = y + (t0 + δ) • v := by
          simp [g, v, AffineMap.lineMap_apply_module', add_comm, add_left_comm, add_assoc]
        _ = y + t0 • v + δ • v := by
          simp [add_smul, add_assoc, add_left_comm, add_comm]
        _ = z + δ • v := by
          simpa [hz_eq, add_assoc, add_comm, add_left_comm] using
            (rfl : y + t0 • v + δ • v = y + t0 • v + δ • v)
    have ht0δIcc : t0 + δ ∈ Set.Icc (0 : ℝ) 1 := by
      refine ⟨?_, ?_⟩
      · linarith [hδnonneg, ht0S.2.1]
      ·
        have h1 : t0 + δ ≤ t0 + (1 - t0) / 2 := by linarith [hδle']
        have h2 : t0 + (1 - t0) / 2 ≤ 1 := by linarith [ht0le1]
        exact le_trans h1 h2
    have ht0δS : t0 + δ ∈ S := by
      have hC' : g (t0 + δ) ∈ C := by simpa [htdir] using hzplusC
      exact ⟨hC', ht0δIcc⟩
    have hcontr : t0 + δ ≤ t0 := ht0max' (t0 + δ) ht0δS
    have ht0δgt : t0 < t0 + δ := by linarith [hδpos]
    exact (lt_irrefl _ (lt_of_lt_of_le ht0δgt hcontr))
  have hzrb : z ∈ euclideanRelativeBoundary n C := by
    have : z ∈ C \ euclideanRelativeInterior n C := ⟨hzC, hz_not_ri⟩
    simpa [euclideanRelativeBoundary_eq_diff_of_isClosed (n := n) (C := C) hCclosed] using this
  exact ⟨z, hzrb, hzseg⟩

/-- A closed convex set that is not affine has nonempty relative boundary. -/
lemma euclideanRelativeBoundary_nonempty_of_isClosed_convex_of_not_affine {n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin n))} (hCclosed : IsClosed C) (hCconv : Convex ℝ C)
    (hCne : C.Nonempty)
    (hC_not_affine :
      ¬ ∃ A : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)),
        (A : Set (EuclideanSpace ℝ (Fin n))) = C) :
    (euclideanRelativeBoundary n C).Nonempty := by
  classical
  obtain ⟨y, hyri⟩ :=
    (euclideanRelativeInterior_closure_convex_affineSpan n C hCconv).2.2.2.2 hCne
  by_contra hDne
  have hDempty : euclideanRelativeBoundary n C = ∅ := Set.not_nonempty_iff_eq_empty.mp hDne
  have hsubset : (affineSpan ℝ C : Set (EuclideanSpace ℝ (Fin n))) ⊆ C := by
    intro x hxaff
    by_contra hxC
    rcases
        exists_rb_point_on_segment_of_mem_ri_of_not_mem (n := n) (C := C) hCclosed
          (y := y) (x := x) hyri hxaff hxC with ⟨z, hzrb, _hzseg⟩
    have : z ∈ (euclideanRelativeBoundary n C) := hzrb
    simpa [hDempty] using hzrb
  have hCeq :
      (affineSpan ℝ C : Set (EuclideanSpace ℝ (Fin n))) = C :=
    Set.Subset.antisymm hsubset (subset_affineSpan ℝ C)
  exact hC_not_affine ⟨affineSpan ℝ C, hCeq⟩

/-- Convexity of the relative boundary yields supporting hyperplane data. -/
lemma exists_supportingHyperplane_data_of_convex_rb {n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin n))} (hCclosed : IsClosed C) (hCconv : Convex ℝ C)
    (hDconv : Convex ℝ (euclideanRelativeBoundary n C))
    (hDne : (euclideanRelativeBoundary n C).Nonempty) :
    ∃ (f : (EuclideanSpace ℝ (Fin n)) →ₗ[ℝ] ℝ) (a : ℝ),
      f ≠ 0 ∧ (∀ x ∈ C, f x ≤ a) ∧
        (∀ x ∈ euclideanRelativeBoundary n C, f x = a) ∧
          ∃ x0 ∈ C, f x0 < a := by
  classical
  set D : Set (EuclideanSpace ℝ (Fin n)) := euclideanRelativeBoundary n C
  have hDsub : D ⊆ C := by
    intro x hxD
    have hxD' : x ∈ C \ euclideanRelativeInterior n C := by
      simpa [D, euclideanRelativeBoundary_eq_diff_of_isClosed (n := n) (C := C) hCclosed] using hxD
    exact hxD'.1
  have hDdisj : Disjoint D (intrinsicInterior ℝ C) := by
    refine Set.disjoint_left.2 ?_
    intro x hxD hxI
    have hxD' :
        x ∈ C \ euclideanRelativeInterior n C := by
      simpa [D, euclideanRelativeBoundary_eq_diff_of_isClosed (n := n) (C := C) hCclosed] using hxD
    have hxI' : x ∈ euclideanRelativeInterior n C :=
      (intrinsicInterior_subset_euclideanRelativeInterior n C) hxI
    exact hxD'.2 hxI'
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) :=
    EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)
  let Cfun : Set (Fin n → ℝ) := e '' C
  let Dfun : Set (Fin n → ℝ) := e '' D
  have hCfunconv : Convex ℝ Cfun := hCconv.linear_image e.toLinearMap
  have hDfunconv : Convex ℝ Dfun := hDconv.linear_image e.toLinearMap
  have hDfunne : Dfun.Nonempty := hDne.image e
  have hDfunsub : Dfun ⊆ Cfun := by
    intro y hy
    rcases hy with ⟨x, hxD, rfl⟩
    exact ⟨x, hDsub hxD, rfl⟩
  have hriCfun : intrinsicInterior ℝ Cfun = e '' intrinsicInterior ℝ C := by
    simpa [Cfun] using (ContinuousLinearEquiv.image_intrinsicInterior (e := e) (s := C))
  have hDfun_disj : Disjoint Dfun (intrinsicInterior ℝ Cfun) := by
    refine Set.disjoint_left.2 ?_
    intro y hyD hyI
    rcases hyD with ⟨x, hxD, rfl⟩
    have hyI' : e x ∈ e '' intrinsicInterior ℝ C := by
      simpa [hriCfun] using hyI
    rcases hyI' with ⟨x', hx'I, hEq⟩
    have hxEq : x = x' := e.injective (by simpa using hEq.symm)
    have hxI : x ∈ intrinsicInterior ℝ C := by simpa [hxEq] using hx'I
    exact (Set.disjoint_left.1 hDdisj) hxD hxI
  obtain ⟨Hfun, hHnontriv, hDfunH⟩ :=
    (exists_nontrivialSupportingHyperplane_containing_iff_disjoint_intrinsicInterior (n := n)
        (C := Cfun) (D := Dfun) hCfunconv hDfunne hDfunconv hDfunsub).2 hDfun_disj
  rcases hHnontriv with ⟨hHsupport, hCfunnot⟩
  rcases cor11_6_2_exists_lt_of_isSupportingHyperplane_of_not_subset
      (n := n) (C := Cfun) (H := Hfun) hHsupport hCfunnot with
    ⟨b, β, hb0, hHdef, hC_le, ⟨y0, hy0Cfun, hy0lt⟩⟩
  let f : (EuclideanSpace ℝ (Fin n)) →ₗ[ℝ] ℝ := (dotProductLinear n b) ∘ₗ e.toLinearMap
  have hf0 : f ≠ 0 := by
    intro hf
    have hzero : b ⬝ᵥ b = 0 := by
      have : f (e.symm b) = 0 := by simpa [hf]
      simpa [f, dotProductLinear] using this
    have hb' : b = 0 := (dotProduct_self_eq_zero (v := b)).1 hzero
    exact hb0 hb'
  have hC_le' : ∀ x ∈ C, f x ≤ β := by
    intro x hxC
    have hxCfun : e x ∈ Cfun := ⟨x, hxC, rfl⟩
    have hle : e x ⬝ᵥ b ≤ β := hC_le (e x) hxCfun
    simpa [f, dotProductLinear] using hle
  have hD_eq : ∀ x ∈ D, f x = β := by
    intro x hxD
    have hxH : e x ∈ Hfun := hDfunH ⟨x, hxD, rfl⟩
    have hxEq : e x ⬝ᵥ b = β := by simpa [hHdef] using hxH
    simpa [f, dotProductLinear] using hxEq
  rcases hy0Cfun with ⟨x0, hx0C, rfl⟩
  have hx0lt' : f x0 < β := by
    simpa [f, dotProductLinear] using hy0lt
  refine ⟨f, β, hf0, hC_le', ?_, ⟨x0, hx0C, hx0lt'⟩⟩
  intro x hxD
  exact hD_eq x (by simpa [D] using hxD)

/-- The relative boundary of a closed convex set is not convex under the non-affine and
non-closed-halfspace hypotheses. -/
lemma not_convex_euclideanRelativeBoundary_of_not_affine_not_closedHalf {n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin n))} (hCclosed : IsClosed C) (hCconv : Convex ℝ C)
    (hCne : C.Nonempty)
    (hC_not_affine :
      ¬ ∃ A : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)),
        (A : Set (EuclideanSpace ℝ (Fin n))) = C)
    (hC_not_closedHalf_affine :
      ¬ ∃ (A : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)))
          (f : (EuclideanSpace ℝ (Fin n)) →ₗ[ℝ] ℝ) (a : ℝ),
          f ≠ 0 ∧ C = (A : Set (EuclideanSpace ℝ (Fin n))) ∩ {x | f x ≤ a}) :
    ¬ Convex ℝ (euclideanRelativeBoundary n C) := by
  classical
  intro hDconv
  have hDne :
      (euclideanRelativeBoundary n C).Nonempty :=
    euclideanRelativeBoundary_nonempty_of_isClosed_convex_of_not_affine (n := n) (C := C)
      hCclosed hCconv hCne hC_not_affine
  obtain ⟨f, a, hf0, hC_le, hD_eq, ⟨x0, hx0C, hx0lt⟩⟩ :=
    exists_supportingHyperplane_data_of_convex_rb (n := n) (C := C) hCclosed hCconv hDconv hDne
  obtain ⟨y0, hy0ri⟩ :=
    (euclideanRelativeInterior_closure_convex_affineSpan n C hCconv).2.2.2.2 hCne
  have hy0C : y0 ∈ C := (euclideanRelativeInterior_subset_closure n C).1 hy0ri
  let y : EuclideanSpace ℝ (Fin n) :=
    (1 - (1 / 2 : ℝ)) • y0 + (1 / 2 : ℝ) • x0
  have hyri : y ∈ euclideanRelativeInterior n C := by
    have hx0cl : x0 ∈ closure C := subset_closure hx0C
    have hy' :=
      euclideanRelativeInterior_convex_combination_mem (n := n) C hCconv y0 x0 hy0ri hx0cl
        (1 / 2 : ℝ) (by norm_num) (by norm_num)
    simpa [y] using hy'
  have hfy_lt : f y < a := by
    have hfy0 : f y0 ≤ a := hC_le y0 hy0C
    have hfy :
        f y = (1 - (1 / 2 : ℝ)) * f y0 + (1 / 2 : ℝ) * f x0 := by
      simp [y, map_add, map_smul, mul_add, add_comm, add_left_comm, add_assoc]
    have hhalf : (1 - (2⁻¹ : ℝ)) = (2⁻¹ : ℝ) := by norm_num
    have hfy' :
        f y = (1 / 2 : ℝ) * f y0 + (1 / 2 : ℝ) * f x0 := by
      simpa [hhalf] using hfy
    linarith [hfy', hfy0, hx0lt]
  have hsub :
      (affineSpan ℝ C : Set (EuclideanSpace ℝ (Fin n))) ∩ {x | f x ≤ a} ⊆ C := by
    intro x hx
    by_contra hxC
    have hxaff : x ∈ affineSpan ℝ C := hx.1
    have hxfle : f x ≤ a := hx.2
    rcases
        exists_rb_point_on_segment_of_mem_ri_of_not_mem (n := n) (C := C) hCclosed
          (y := y) (x := x) hyri hxaff hxC with ⟨z, hzrb, hzseg⟩
    rcases hzseg with ⟨s, t, hs, ht, hst, rfl⟩
    have hfz : f (s • y + t • x) = s * f y + t * f x := by
      simp [map_add, map_smul, mul_add, add_comm, add_left_comm, add_assoc]
    have hfz_lt : f (s • y + t • x) < a := by
      calc
        f (s • y + t • x) = s * f y + t * f x := hfz
        _ < s * a + t * a := by
              exact
                add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hfy_lt hs)
                  (mul_le_mul_of_nonneg_left hxfle (le_of_lt ht))
        _ = (s + t) * a := by ring
        _ = a := by simpa [hst]
    have hfz_eq : f (s • y + t • x) = a := by
      exact hD_eq _ hzrb
    have : f (s • y + t • x) < f (s • y + t • x) := by
      simpa [hfz_eq] using hfz_lt
    exact (lt_irrefl _ this)
  have hCeq :
      C = (affineSpan ℝ C : Set (EuclideanSpace ℝ (Fin n))) ∩ {x | f x ≤ a} := by
    refine Set.Subset.antisymm ?_ hsub
    intro x hxC
    exact ⟨subset_affineSpan ℝ C hxC, hC_le x hxC⟩
  exact hC_not_closedHalf_affine ⟨affineSpan ℝ C, f, a, hf0, hCeq⟩

/-- A line segment in Euclidean space is bounded. -/
lemma isBounded_segment {n : ℕ} (x₁ x₂ : EuclideanSpace ℝ (Fin n)) :
    Bornology.IsBounded (segment ℝ x₁ x₂) := by
  have h1 : Bornology.IsBounded ({x₁} : Set (EuclideanSpace ℝ (Fin n))) :=
    Bornology.isBounded_singleton
  have h2 : Bornology.IsBounded ({x₂} : Set (EuclideanSpace ℝ (Fin n))) :=
    Bornology.isBounded_singleton
  have h12 : Bornology.IsBounded
      (({x₁} : Set (EuclideanSpace ℝ (Fin n))) ∪ {x₂}) := h1.union h2
  have hpair : Bornology.IsBounded ({x₁, x₂} : Set (EuclideanSpace ℝ (Fin n))) := by
    simpa [Set.union_singleton, Set.pair_comm] using h12
  have hconv :
      Bornology.IsBounded (convexHull ℝ ({x₁, x₂} : Set (EuclideanSpace ℝ (Fin n)))) :=
    (isBounded_convexHull
        (s := ({x₁, x₂} : Set (EuclideanSpace ℝ (Fin n)))).2 hpair)
  simpa [convexHull_pair] using hconv

/-- A relative interior point allows a small step in any affine-span direction. -/
lemma exists_add_sub_mem_of_mem_ri_of_mem_direction {n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin n))} {x v : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ euclideanRelativeInterior n C)
    (hv : v ∈ (affineSpan ℝ C).direction) :
    ∃ ε : ℝ, 0 < ε ∧ x + ε • v ∈ C ∧ x - ε • v ∈ C := by
  rcases hx with ⟨hx_aff, ε, hε, hsub⟩
  set δ : ℝ := ε / (‖v‖ + 1)
  have hden : 0 < ‖v‖ + 1 := by linarith [norm_nonneg v]
  have hδpos : 0 < δ := by exact div_pos hε hden
  have hδnonneg : 0 ≤ δ := le_of_lt hδpos
  have hnorm : ‖δ • v‖ ≤ ε := by
    have hnorm_le : ‖v‖ ≤ ‖v‖ + 1 := by linarith [norm_nonneg v]
    have hmul : δ * ‖v‖ ≤ δ * (‖v‖ + 1) :=
      mul_le_mul_of_nonneg_left hnorm_le hδnonneg
    have hδmul : δ * (‖v‖ + 1) = ε := by
      have hden_ne : ‖v‖ + 1 ≠ 0 := by linarith [norm_nonneg v]
      calc
        δ * (‖v‖ + 1) = (ε / (‖v‖ + 1)) * (‖v‖ + 1) := by simp [δ]
        _ = ε := by field_simp [hden_ne]
    calc
      ‖δ • v‖ = δ * ‖v‖ := by
        simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hδnonneg]
      _ ≤ δ * (‖v‖ + 1) := hmul
      _ = ε := hδmul
  have hnorm_neg : ‖(-δ) • v‖ ≤ ε := by
    simpa [neg_smul, Real.norm_eq_abs, abs_of_nonneg hδnonneg] using hnorm
  have hvball : δ • v ∈ ε • euclideanUnitBall n :=
    mem_smul_unitBall_of_norm_le hε hnorm
  have hvball_neg : (-δ) • v ∈ ε • euclideanUnitBall n :=
    mem_smul_unitBall_of_norm_le hε hnorm_neg
  have hxplus_aff : x + δ • v ∈ affineSpan ℝ C := by
    have hdir : δ • v ∈ (affineSpan ℝ C).direction :=
      (affineSpan ℝ C).direction.smul_mem δ hv
    have hx' :
        (δ • v) +ᵥ x ∈ affineSpan ℝ C :=
      AffineSubspace.vadd_mem_of_mem_direction (s := affineSpan ℝ C) hdir hx_aff
    simpa [vadd_eq_add, add_comm] using hx'
  have hxminus_aff : x - δ • v ∈ affineSpan ℝ C := by
    have hdir : (-δ) • v ∈ (affineSpan ℝ C).direction :=
      (affineSpan ℝ C).direction.smul_mem (-δ) hv
    have hx' :
        ((-δ) • v) +ᵥ x ∈ affineSpan ℝ C :=
      AffineSubspace.vadd_mem_of_mem_direction (s := affineSpan ℝ C) hdir hx_aff
    simpa [vadd_eq_add, add_comm, sub_eq_add_neg] using hx'
  have hxplus_mem :
      x + δ • v ∈ (fun y => x + y) '' (ε • euclideanUnitBall n) :=
    ⟨δ • v, hvball, by simp⟩
  have hxminus_mem :
      x - δ • v ∈ (fun y => x + y) '' (ε • euclideanUnitBall n) := by
    refine ⟨(-δ) • v, hvball_neg, ?_⟩
    simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have hxplus : x + δ • v ∈ C := hsub ⟨hxplus_mem, hxplus_aff⟩
  have hxminus : x - δ • v ∈ C := hsub ⟨hxminus_mem, hxminus_aff⟩
  exact ⟨δ, hδpos, hxplus, hxminus⟩

end Section18
end Chap04
