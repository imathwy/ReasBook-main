/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Xinyi Guo, Siyuan Shao, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap04.section19_part1

open scoped BigOperators
open scoped Pointwise
open Topology

section Chap19
section Section19

/-- Helper for Theorem 19.1: directions of the same half-line are positive multiples. -/
lemma helperForTheorem_19_1_IsDirectionOf_posMul_of_same_halfLine
    {n : ℕ} {C' : Set (Fin n → ℝ)} {d d0 : Fin n → ℝ}
    (hd : IsDirectionOf (𝕜 := ℝ) C' d) (hd0 : IsDirectionOf (𝕜 := ℝ) C' d0) :
    ∃ t : ℝ, 0 < t ∧ d = t • d0 := by
  classical
  rcases hd with ⟨x, hdne, hC⟩
  rcases hd0 with ⟨x0, hd0ne, hC0⟩
  have hxmem : x ∈ C' := by
    have hxmem' :
        x + (0 : ℝ) • d ∈ (fun t : ℝ => x + t • d) '' Set.Ici (0 : ℝ) := by
      refine ⟨0, ?_, ?_⟩
      · simp
      · simp
    simpa [hC] using hxmem'
  have hx0mem : x0 ∈ C' := by
    have hx0mem' :
        x0 + (0 : ℝ) • d0 ∈ (fun t : ℝ => x0 + t • d0) '' Set.Ici (0 : ℝ) := by
      refine ⟨0, ?_, ?_⟩
      · simp
      · simp
    simpa [hC0] using hx0mem'
  have hx0repr : ∃ s : ℝ, 0 ≤ s ∧ x0 = x + s • d := by
    have : x0 ∈ (fun t : ℝ => x + t • d) '' Set.Ici (0 : ℝ) := by
      simpa [hC] using hx0mem
    rcases this with ⟨s, hs, rfl⟩
    exact ⟨s, hs, rfl⟩
  have hx0d0repr : ∃ u : ℝ, 0 ≤ u ∧ x0 + d0 = x + u • d := by
    have hx0d0mem : x0 + d0 ∈ C' := by
      have hx0d0mem' :
          x0 + (1 : ℝ) • d0 ∈ (fun t : ℝ => x0 + t • d0) '' Set.Ici (0 : ℝ) := by
        refine ⟨1, ?_, ?_⟩
        · norm_num
        · simp
      simpa [hC0] using hx0d0mem'
    have : x0 + d0 ∈ (fun t : ℝ => x + t • d) '' Set.Ici (0 : ℝ) := by
      simpa [hC] using hx0d0mem
    rcases this with ⟨u, hu, hEq⟩
    exact ⟨u, hu, hEq.symm⟩
  rcases hx0repr with ⟨s, hs, hx0eq⟩
  rcases hx0d0repr with ⟨u, hu, hx0d0eq⟩
  have hparam_unique : ∀ {t t' : ℝ}, x + t • d = x + t' • d → t = t' := by
    intro t t' hEq
    have hEq' : t • d = t' • d := by
      exact add_left_cancel hEq
    have hzero : (t - t') • d = 0 := by
      calc
        (t - t') • d = t • d - t' • d := by
          simpa using (sub_smul t t' d)
        _ = 0 := by simpa [hEq']
    rcases smul_eq_zero.mp hzero with ht | hdzero
    · exact sub_eq_zero.mp ht
    · exact (hdne hdzero).elim
  have hparam_nonneg : ∀ t : ℝ, x + t • d ∈ C' → 0 ≤ t := by
    intro t ht
    have ht' : x + t • d ∈ (fun u : ℝ => x + u • d) '' Set.Ici (0 : ℝ) := by
      simpa [hC] using ht
    rcases ht' with ⟨u, hu, hEq⟩
    have htu : t = u := hparam_unique hEq.symm
    simpa [htu] using hu
  have hd0eq : d0 = (u - s) • d := by
    have h1 := congrArg (fun y => y - x0) hx0d0eq
    have h1' : d0 = x + u • d - x0 := by
      simpa using h1
    calc
      d0 = x + u • d - x0 := h1'
      _ = x + u • d - (x + s • d) := by simp [hx0eq]
      _ = u • d - s • d := by
        simpa [add_assoc] using (add_sub_add_left_eq_sub (u • d) (s • d) x)
      _ = (u - s) • d := by
        symm
        simpa using (sub_smul u s d)
  let r : ℝ := u - s
  have hrne : r ≠ 0 := by
    intro hrzero
    have : d0 = 0 := by
      simpa [r, hrzero] using hd0eq
    exact hd0ne this
  have hrpos : 0 < r := by
    by_contra hnotpos
    have hrle : r ≤ 0 := by linarith
    have hrlt : r < 0 := lt_of_le_of_ne hrle hrne
    let t : ℝ := (s + 1) / (-r)
    have htpos : 0 ≤ t := by
      have hnum : 0 ≤ s + 1 := by linarith
      have hden : 0 < -r := by linarith
      exact div_nonneg hnum (le_of_lt hden)
    have hx0t_mem : x0 + t • d0 ∈ C' := by
      have : x0 + t • d0 ∈ (fun q : ℝ => x0 + q • d0) '' Set.Ici (0 : ℝ) := by
        refine ⟨t, ?_, rfl⟩
        simpa [t] using htpos
      simpa [hC0] using this
    have hx0t_eq : x0 + t • d0 = x + (s + t * r) • d := by
      calc
        x0 + t • d0 = (x + s • d) + t • (r • d) := by
          simp [hx0eq, hd0eq, r, add_assoc]
        _ = x + (s • d + t • (r • d)) := by
          simp [add_assoc]
        _ = x + (s • d + (t * r) • d) := by
          simp [smul_smul, mul_comm, mul_left_comm, mul_assoc]
        _ = x + (s + t * r) • d := by
          have hsum : s • d + (t * r) • d = (s + t * r) • d := by
            symm
            simpa using (add_smul s (t * r) d)
          simp [hsum]
    have hx0t_mem' : x + (s + t * r) • d ∈ C' := by
      simpa [hx0t_eq] using hx0t_mem
    have hnonneg : 0 ≤ s + t * r := hparam_nonneg (s + t * r) hx0t_mem'
    have hcalc : s + t * r = -1 := by
      dsimp [t]
      field_simp [hrne]
      ring
    have : (0 : ℝ) ≤ -1 := by
      simpa [hcalc] using hnonneg
    linarith
  have hd0eq' : d0 = r • d := by
    simpa [r] using hd0eq
  have hd_eq : d = (1 / r) • d0 := by
    have hmul := congrArg (fun v => (1 / r) • v) hd0eq'
    have hmul' : (1 / r) • d0 = d := by
      calc
        (1 / r) • d0 = (1 / r) • (r • d) := by simpa [hd0eq']
        _ = (1 / r * r) • d := by simp [smul_smul]
        _ = d := by
          have hcoef : (r⁻¹ * r : ℝ) = 1 := by
            field_simp [hrne]
          simpa [hcoef]
    exact hmul'.symm
  refine ⟨1 / r, ?_, hd_eq⟩
  exact one_div_pos.mpr hrpos

/-- Helper for Theorem 19.1: finite faces give finitely many direction representatives. -/
lemma helperForTheorem_19_1_finiteFaces_imp_exists_finite_direction_reps
    {n : ℕ} {C : Set (Fin n → ℝ)} :
    {F : Set (Fin n → ℝ) | IsFace (𝕜 := ℝ) C F}.Finite →
      ∃ S₁ : Set (Fin n → ℝ),
        Set.Finite S₁ ∧
          (∀ d, IsExtremeDirection (𝕜 := ℝ) C d →
            ∃ d0 ∈ S₁, ∃ t : ℝ, 0 < t ∧ d = t • d0) ∧
          S₁ ⊆ {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d} := by
  classical
  intro hfaces
  let H : Set (Set (Fin n → ℝ)) := {C' : Set (Fin n → ℝ) | IsHalfLineFace (𝕜 := ℝ) C C'}
  have hHsubset : H ⊆ {F : Set (Fin n → ℝ) | IsFace (𝕜 := ℝ) C F} := by
    intro C' hC'
    exact hC'.1
  have hHfinite : H.Finite := hfaces.subset hHsubset
  have hdir :
      ∀ C' : {C' : Set (Fin n → ℝ) // C' ∈ H},
        ∃ d : Fin n → ℝ, IsDirectionOf (𝕜 := ℝ) (C' : Set (Fin n → ℝ)) d := by
    intro C'
    rcases C'.2 with ⟨_hface, ⟨d, hdir⟩⟩
    exact ⟨d, hdir⟩
  choose g hg using hdir
  let S₁ : Set (Fin n → ℝ) := Set.range g
  have hS₁finite : Set.Finite S₁ := by
    classical
    have : Finite {C' : Set (Fin n → ℝ) // C' ∈ H} := by
      simpa using (Set.finite_coe_iff.mpr hHfinite)
    simpa [S₁] using (Set.finite_range g)
  refine ⟨S₁, hS₁finite, ?_, ?_⟩
  · intro d hdext
    rcases hdext with ⟨C', hhalf, hdir'⟩
    have hC'H : (C' : Set (Fin n → ℝ)) ∈ H := hhalf
    let C'sub : {C' : Set (Fin n → ℝ) // C' ∈ H} := ⟨C', hC'H⟩
    have hd0dir : IsDirectionOf (𝕜 := ℝ) (C' : Set (Fin n → ℝ)) (g C'sub) := hg C'sub
    rcases
        helperForTheorem_19_1_IsDirectionOf_posMul_of_same_halfLine
          (C' := C') (d := d) (d0 := g C'sub) hdir' hd0dir with
      ⟨t, ht, hdeq⟩
    refine ⟨g C'sub, ?_, t, ht, hdeq⟩
    exact ⟨C'sub, rfl⟩
  · intro d hd
    rcases hd with ⟨C'sub, rfl⟩
    have hhalf : IsHalfLineFace (𝕜 := ℝ) C (C'sub : Set (Fin n → ℝ)) := C'sub.2
    exact ⟨C'sub, hhalf, hg C'sub⟩

/-- Helper for Theorem 19.1: replace direction sets by positive-multiple representatives. -/
lemma helperForTheorem_19_1_mixedConvexHull_directionSet_eq_of_posMul_cover
    {n : ℕ} {S₀ S₁ S₁' : Set (Fin n → ℝ)}
    (hS₁ : S₁ ⊆ S₁')
    (hpos :
      ∀ d ∈ S₁', ∃ d0 ∈ S₁, ∃ t : ℝ, 0 < t ∧ d = t • d0) :
    mixedConvexHull (n := n) S₀ S₁' = mixedConvexHull (n := n) S₀ S₁ := by
  have hraynonneg : rayNonneg n S₁' = rayNonneg n S₁ := by
    apply Set.Subset.antisymm
    · intro x hx
      rcases hx with ⟨d, hdS₁', t, ht, rfl⟩
      rcases hpos d hdS₁' with ⟨d0, hd0S₁, t0, ht0, rfl⟩
      refine ⟨d0, hd0S₁, t * t0, ?_, ?_⟩
      · exact mul_nonneg ht (le_of_lt ht0)
      · simp [smul_smul, mul_comm, mul_left_comm, mul_assoc]
    · intro x hx
      rcases hx with ⟨d, hdS₁, t, ht, rfl⟩
      exact ⟨d, hS₁ hdS₁, t, ht, rfl⟩
  have hray : ray n S₁' = ray n S₁ := by
    ext x
    constructor
    · intro hx
      have hx' : x = 0 ∨ x ∈ rayNonneg n S₁' := by
        simpa [ray, Set.mem_insert_iff] using hx
      cases hx' with
      | inl hx0 =>
          subst hx0
          exact (Set.mem_insert_iff).2 (Or.inl rfl)
      | inr hxray =>
          have hxray' : x ∈ rayNonneg n S₁ := by
            simpa [hraynonneg] using hxray
          exact (Set.mem_insert_iff).2 (Or.inr hxray')
    · intro hx
      have hx' : x = 0 ∨ x ∈ rayNonneg n S₁ := by
        simpa [ray, Set.mem_insert_iff] using hx
      cases hx' with
      | inl hx0 =>
          subst hx0
          exact (Set.mem_insert_iff).2 (Or.inl rfl)
      | inr hxray =>
          have hxray' : x ∈ rayNonneg n S₁' := by
            simpa [hraynonneg] using hxray
          exact (Set.mem_insert_iff).2 (Or.inr hxray')
  have hrepr' := mixedConvexHull_eq_conv_add_ray_eq_conv_add_cone (n := n) S₀ S₁'
  have hrepr := mixedConvexHull_eq_conv_add_ray_eq_conv_add_cone (n := n) S₀ S₁
  calc
    mixedConvexHull (n := n) S₀ S₁' = conv (S₀ + ray n S₁') := hrepr'.1
    _ = conv (S₀ + ray n S₁) := by simpa [hray]
    _ = mixedConvexHull (n := n) S₀ S₁ := by symm; exact hrepr.1

/-- Helper for Theorem 19.1: closed convex sets with no lines equal the mixed convex hull of their
extreme points and extreme directions. -/
lemma helperForTheorem_19_1_closed_finiteFaces_eq_mixedConvexHull_extremePoints_extremeDirections
    {n : ℕ} {C : Set (Fin n → ℝ)} (hc : Convex ℝ C) (hclosed : IsClosed C)
    (hNoLines :
      ¬ ∃ y : Fin n → ℝ, y ≠ 0 ∧ y ∈ (-Set.recessionCone C) ∩ Set.recessionCone C) :
    C =
      mixedConvexHull (n := n)
        {x : Fin n → ℝ | IsExtremePoint (𝕜 := ℝ) C x}
        {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d} := by
  have hEq :
      (C.extremePoints ℝ) = {x : Fin n → ℝ | IsExtremePoint (𝕜 := ℝ) C x} := by
    ext x
    exact (isExtremePoint_iff_mem_extremePoints (𝕜 := ℝ) (C := C) (x := x)).symm
  simpa [hEq] using
    (closedConvex_eq_mixedConvexHull_extremePoints_extremeDirections
      (n := n) (C := C) hclosed hc hNoLines)

/-- Helper for Theorem 19.1: lineality space in `Fin n → ℝ`. -/
abbrev linealitySpace_fin {n : ℕ} (C : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  (-Set.recessionCone C) ∩ Set.recessionCone C

/-- Helper for Theorem 19.1: the lineality space is a submodule in `Fin n → ℝ`. -/
lemma helperForTheorem_19_1_linealitySpace_isSubmodule
    {n : ℕ} {C : Set (Fin n → ℝ)} (hCconv : Convex ℝ C) :
    ∃ L : Submodule ℝ (Fin n → ℝ), (L : Set _) = linealitySpace_fin C := by
  classical
  let e := euclideanEquiv n
  let C' : Set (EuclideanSpace ℝ (Fin n)) := e.symm '' C
  have hCconv' : Convex ℝ C' := hCconv.linear_image e.symm.toLinearMap
  rcases linealitySpace_isSubmodule (C := C') hCconv' with ⟨L, hL⟩
  let L' : Submodule ℝ (Fin n → ℝ) := L.map e.toLinearMap
  have hCe : e '' C' = C := by
    ext x
    constructor
    · rintro ⟨y, ⟨x0, hx0, rfl⟩, rfl⟩
      simpa using hx0
    · intro hx
      refine ⟨e.symm x, ?_, ?_⟩
      · exact ⟨x, hx, by simp⟩
      · simp
  have hrec :
      Set.recessionCone C = e '' Set.recessionCone C' := by
    simpa [hCe] using
      (recessionCone_image_linearEquiv (e := e.toLinearEquiv) (C := C'))
  have hlin :
      e '' Set.linealitySpace C' = linealitySpace_fin C := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : y ∈ (-Set.recessionCone C') ∩ Set.recessionCone C' := by
        simpa [Set.linealitySpace] using hy
      have hypos : y ∈ Set.recessionCone C' := hy'.2
      have hyneg : -y ∈ Set.recessionCone C' := by
        simpa using hy'.1
      have hypos' : e y ∈ Set.recessionCone C := by
        have : e y ∈ e '' Set.recessionCone C' := ⟨y, hypos, rfl⟩
        simpa [hrec] using this
      have hyneg' : -e y ∈ Set.recessionCone C := by
        have : e (-y) ∈ e '' Set.recessionCone C' := ⟨-y, hyneg, rfl⟩
        have : e (-y) ∈ Set.recessionCone C := by
          simpa [hrec] using this
        simpa using this
      have hyneg'' : e y ∈ -Set.recessionCone C := by
        simpa using hyneg'
      exact ⟨hyneg'', hypos'⟩
    · intro hx
      have hxpos : x ∈ Set.recessionCone C := hx.2
      have hxneg : -x ∈ Set.recessionCone C := by
        simpa using hx.1
      have hxpos' : x ∈ e '' Set.recessionCone C' := by
        simpa [hrec] using hxpos
      rcases hxpos' with ⟨y, hy, hyx⟩
      have hxneg' : -x ∈ e '' Set.recessionCone C' := by
        simpa [hrec] using hxneg
      rcases hxneg' with ⟨y', hy', hyx'⟩
      have hy'': y' = -y := by
        apply e.injective
        calc
          e y' = -x := hyx'
          _ = -(e y) := by simpa [hyx]
          _ = e (-y) := by simp
      have hyneg : -y ∈ Set.recessionCone C' := by
        simpa [hy''] using hy'
      have hylineal : y ∈ Set.linealitySpace C' := by
        have : y ∈ (-Set.recessionCone C') ∩ Set.recessionCone C' := by
          refine ⟨?_, hy⟩
          simpa using hyneg
        simpa [Set.linealitySpace] using this
      exact ⟨y, hylineal, hyx⟩
  have hmap : (L' : Set _) = e '' (L : Set _) := by
    ext x
    constructor
    · intro hx
      rcases (Submodule.mem_map (p := L) (f := e.toLinearMap) (x := x)).1 hx with ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact (Submodule.mem_map (p := L) (f := e.toLinearMap) (x := e y)).2 ⟨y, hy, rfl⟩
  refine ⟨L', ?_⟩
  calc
    (L' : Set _) = e '' (L : Set _) := hmap
    _ = e '' Set.linealitySpace C' := by simpa [hL]
    _ = linealitySpace_fin C := hlin

/-- Helper for Theorem 19.1: lineality directions translate points in `Fin n → ℝ`. -/
lemma helperForTheorem_19_1_add_sub_mem_of_mem_linealitySpace_fin
    {n : ℕ} {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) {v x : Fin n → ℝ}
    (hv : v ∈ linealitySpace_fin C) (hx : x ∈ C) :
    x + v ∈ C ∧ x - v ∈ C := by
  let e := euclideanEquiv n
  let C' : Set (EuclideanSpace ℝ (Fin n)) := e.symm '' C
  have hCconv' : Convex ℝ C' := hC.linear_image e.symm.toLinearMap
  have hCe : e '' C' = C := by
    ext y
    constructor
    · rintro ⟨z, ⟨y0, hy0, rfl⟩, rfl⟩
      simpa using hy0
    · intro hy
      refine ⟨e.symm y, ?_, ?_⟩
      · exact ⟨y, hy, by simp⟩
      · simp
  have hrec :
      Set.recessionCone C = e '' Set.recessionCone C' := by
    simpa [hCe] using
      (recessionCone_image_linearEquiv (e := e.toLinearEquiv) (C := C'))
  have hv' : e.symm v ∈ Set.linealitySpace C' := by
    have hvpos : v ∈ Set.recessionCone C := hv.2
    have hvneg : -v ∈ Set.recessionCone C := by
      simpa using hv.1
    have hvpos' : v ∈ e '' Set.recessionCone C' := by
      simpa [hrec] using hvpos
    rcases hvpos' with ⟨y, hy, hyv⟩
    have hvneg' : -v ∈ e '' Set.recessionCone C' := by
      simpa [hrec] using hvneg
    rcases hvneg' with ⟨y', hy', hyv'⟩
    have hy'': y' = -y := by
      apply e.injective
      calc
        e y' = -v := hyv'
        _ = -(e y) := by simpa [hyv]
        _ = e (-y) := by simp
    have hyneg : -y ∈ Set.recessionCone C' := by
      simpa [hy''] using hy'
    have hylineal : y ∈ Set.linealitySpace C' := by
      have : y ∈ (-Set.recessionCone C') ∩ Set.recessionCone C' := by
        refine ⟨?_, hy⟩
        simpa using hyneg
      simpa [Set.linealitySpace] using this
    have : y = e.symm v := by
      apply e.injective
      have hev : e (e.symm v) = v := by
        simp
      rw [hyv, hev]
    simpa [this] using hylineal
  have hx' : e.symm x ∈ C' := by
    exact ⟨x, hx, by simp⟩
  have hmem :=
    add_sub_mem_of_mem_linealitySpace (n := n) (C := C') hCconv' hv' hx'
  have hpos : x + v ∈ C := by
    have : e (e.symm x + e.symm v) ∈ e '' C' := ⟨e.symm x + e.symm v, hmem.1, rfl⟩
    simpa [hCe] using this
  have hneg : x - v ∈ C := by
    have : e (e.symm x - e.symm v) ∈ e '' C' := ⟨e.symm x - e.symm v, hmem.2, rfl⟩
    simpa [hCe] using this
  exact ⟨hpos, hneg⟩

/-- Helper for Theorem 19.1: split off lineality using a complementary projection. -/
lemma helperForTheorem_19_1_linealitySplit_projection_setup
    {n : ℕ} {C : Set (Fin n → ℝ)} (hc : Convex ℝ C) (hCne : C.Nonempty) :
    ∃ L : Submodule ℝ (Fin n → ℝ), (L : Set _) = linealitySpace_fin C ∧
      ∃ W : Submodule ℝ (Fin n → ℝ), IsCompl W L ∧
        ∃ π : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ),
          LinearMap.ker π = L ∧ LinearMap.range π = W ∧
            (∀ w ∈ W, π w = w) ∧ (∀ l ∈ L, π l = 0) := by
  classical
  rcases helperForTheorem_19_1_linealitySpace_isSubmodule (n := n) (C := C) hc with ⟨L, hL⟩
  obtain ⟨W, hLW⟩ := L.exists_isCompl
  have hWL : IsCompl W L := hLW.symm
  let π : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) := Submodule.IsCompl.projection hWL
  have hker : LinearMap.ker π = L := by
    simpa [π] using (Submodule.IsCompl.projection_ker (hpq := hWL))
  have hrange : LinearMap.range π = W := by
    simpa [π] using (Submodule.IsCompl.projection_range (hpq := hWL))
  have hprojW : ∀ w ∈ W, π w = w := by
    intro w hw
    have hfix : π (⟨w, hw⟩ : W) = (⟨w, hw⟩ : W) := by
      exact Submodule.IsCompl.projection_apply_left (hpq := hWL) (x := ⟨w, hw⟩)
    simpa using hfix
  have hprojL : ∀ l ∈ L, π l = 0 := by
    intro l hl
    exact (Submodule.IsCompl.projection_apply_eq_zero_iff (hpq := hWL)).2 hl
  refine ⟨L, hL, W, hWL, π, ?_⟩
  refine ⟨hker, ?_⟩
  refine ⟨hrange, ?_⟩
  exact ⟨hprojW, hprojL⟩

/-- Helper for Theorem 19.1: lineality-kernel projection gives preimage/image decomposition. -/
lemma helperForTheorem_19_1_projection_preimage_image_eq_of_linealityKernel
    {n : ℕ} {C : Set (Fin n → ℝ)} (hc : Convex ℝ C) (hCne : C.Nonempty)
    {L W : Submodule ℝ (Fin n → ℝ)} (hWL : IsCompl W L)
    {π : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)} (hker : LinearMap.ker π = L)
    (hrange : LinearMap.range π = W) (hL : (L : Set _) = linealitySpace_fin C) :
    let K := π '' C;
      (C = π ⁻¹' K) ∧ (K ⊆ (W : Set _)) ∧ K.Nonempty := by
  classical
  intro K
  have hsubset : C ⊆ π ⁻¹' K := by
    intro x hx
    refine ⟨x, hx, rfl⟩
  have hsup : π ⁻¹' K ⊆ C := by
    intro x hx
    have hxK : π x ∈ K := by
      simpa using hx
    rcases (by simpa [K] using hxK) with ⟨y, hyC, hy⟩
    have hkerxy : x - y ∈ LinearMap.ker π := by
      apply (LinearMap.mem_ker).2
      calc
        π (x - y) = π x - π y := by simp
        _ = 0 := by
          have hxy : π x = π y := by simpa [hy] using rfl
          simp [hxy]
    have hxL : x - y ∈ L := by
      simpa [hker] using hkerxy
    have hxLineal : x - y ∈ linealitySpace_fin C := by
      rw [← hL]
      exact hxL
    have hmem := helperForTheorem_19_1_add_sub_mem_of_mem_linealitySpace_fin
      (n := n) (C := C) hc hxLineal hyC
    have hxC' : y + (x - y) ∈ C := hmem.1
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hxC'
  have hEq : C = π ⁻¹' K := Set.Subset.antisymm hsubset hsup
  have hKsubset : K ⊆ (W : Set _) := by
    intro z hz
    rcases hz with ⟨x, hxC, rfl⟩
    have hz' : π x ∈ (LinearMap.range π : Set (Fin n → ℝ)) := by
      exact ⟨x, rfl⟩
    simpa [hrange] using hz'
  have hKne : K.Nonempty := by
    rcases hCne with ⟨x, hx⟩
    exact ⟨π x, ⟨x, hx, rfl⟩⟩
  exact ⟨hEq, hKsubset, hKne⟩

/-- Helper for Theorem 19.1: pull back faces along a projection. -/
lemma helperForTheorem_19_1_face_preimage_of_projection
    {n : ℕ} {C K F : Set (Fin n → ℝ)} (hc : Convex ℝ C)
    {π : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)} (hK : K = π '' C) (hCpre : C = π ⁻¹' K)
    (hF : IsFace (𝕜 := ℝ) K F) :
    IsFace (𝕜 := ℝ) C (C ∩ π ⁻¹' F) := by
  classical
  refine ⟨hc, ?_⟩
  refine ⟨Set.inter_subset_left, ?_⟩
  intro x hxC y hyC z hz hzseg
  have hzC : z ∈ C := hz.1
  have hzF : π z ∈ F := by
    have : z ∈ π ⁻¹' F := hz.2
    simpa using this
  have hxK : π x ∈ K := by
    have : π x ∈ π '' C := ⟨x, hxC, rfl⟩
    simpa [hK] using this
  have hyK : π y ∈ K := by
    have : π y ∈ π '' C := ⟨y, hyC, rfl⟩
    simpa [hK] using this
  have hzseg' : π z ∈ openSegment ℝ (π x) (π y) := by
    rcases hzseg with ⟨a, b, ha, hb, hab, hzEq⟩
    refine ⟨a, b, ha, hb, hab, ?_⟩
    rw [hzEq.symm]
    simp [map_add, map_smul]
  have hxF : π x ∈ F :=
    hF.2.left_mem_of_mem_openSegment hxK hyK hzF hzseg'
  have hxpre : x ∈ π ⁻¹' F := by
    simpa using hxF
  exact ⟨hxC, hxpre⟩

/-- Helper for Theorem 19.1: properties of the projection along lineality. -/
lemma helperForTheorem_19_1_closed_finiteFaces_noLines_of_linealityProjection
    {n : ℕ} {C : Set (Fin n → ℝ)} (hc : Convex ℝ C) (hclosed : IsClosed C)
    (hfaces : {F : Set (Fin n → ℝ) | IsFace (𝕜 := ℝ) C F}.Finite) (hCne : C.Nonempty)
    {L W : Submodule ℝ (Fin n → ℝ)} (hWL : IsCompl W L)
    {π : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)} (hker : LinearMap.ker π = L)
    (hrange : LinearMap.range π = W) (hprojW : ∀ w ∈ W, π w = w)
    (hL : (L : Set _) = linealitySpace_fin C) :
    let K := π '' C;
      IsClosed K ∧
        {F : Set (Fin n → ℝ) | IsFace (𝕜 := ℝ) K F}.Finite ∧
          (¬ ∃ y : Fin n → ℝ, y ≠ 0 ∧ y ∈ (-Set.recessionCone K) ∩ Set.recessionCone K) := by
  classical
  intro K
  have hpre :
      (C = π ⁻¹' K) ∧ (K ⊆ (W : Set _)) ∧ K.Nonempty := by
    simpa [K] using
      (helperForTheorem_19_1_projection_preimage_image_eq_of_linealityKernel
        (n := n) (C := C) hc hCne (L := L) (W := W) hWL (π := π) hker hrange hL)
  have hCpre : C = π ⁻¹' K := hpre.1
  have hKsubsetW : K ⊆ (W : Set _) := hpre.2.1
  have hKne : K.Nonempty := hpre.2.2
  have hclosedK : IsClosed K := by
    let e := euclideanEquiv n
    let C' : Set (EuclideanSpace ℝ (Fin n)) := e.symm '' C
    let A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
      (e.symm.toLinearMap).comp (π.comp e.toLinearMap)
    have hCne' : C'.Nonempty := by
      rcases hCne with ⟨x, hx⟩
      refine ⟨e.symm x, ?_⟩
      refine ⟨x, hx, ?_⟩
      simp
    have hCconv' : Convex ℝ C' := hc.linear_image e.symm.toLinearMap
    let hhome := (e.symm.toAffineEquiv).toHomeomorphOfFiniteDimensional
    have hCclosed' : IsClosed C' := by
      have hclosed' :
          IsClosed ((hhome : _ → _) '' C) :=
        (hhome.isClosed_image (s := C)).2 hclosed
      simpa [C', hhome, AffineEquiv.coe_toHomeomorphOfFiniteDimensional] using hclosed'
    have hCcl : closure C' = C' := hCclosed'.closure_eq
    have hlineal :
        ∀ z, z ≠ 0 → z ∈ Set.recessionCone (closure C') → A z = 0 →
          z ∈ Set.linealitySpace (closure C') := by
      intro z _hz0 _hzrec hzA
      have hzAeq : e (A z) = π (e z) := by
        simp [A]
      have hzA0 : e (A z) = 0 := by
        have hzA' := congrArg e hzA
        simpa using hzA'
      have hzAker : π (e z) = 0 := by
        simpa [hzAeq] using hzA0
      have hzker : e z ∈ LinearMap.ker π := by
        exact (LinearMap.mem_ker).2 hzAker
      have hzL : e z ∈ L := by
        simpa [hker] using hzker
      have hzlinealC : e z ∈ linealitySpace_fin C := by
        rw [← hL]
        exact hzL
      have hzrecC : e z ∈ Set.recessionCone C := hzlinealC.2
      have hznegC : -e z ∈ Set.recessionCone C := by
        simpa using hzlinealC.1
      have hrecC' :
          Set.recessionCone C' = e.symm '' Set.recessionCone C := by
        simpa [C'] using
          (recessionCone_image_linearEquiv (e := e.symm.toLinearEquiv) (C := C))
      have hzrecC' : z ∈ Set.recessionCone C' := by
        have hzmem : z ∈ e.symm '' Set.recessionCone C := by
          refine ⟨e z, hzrecC, ?_⟩
          simp
        simpa [hrecC'] using hzmem
      have hznegC' : -z ∈ Set.recessionCone C' := by
        have hzmem : -z ∈ e.symm '' Set.recessionCone C := by
          refine ⟨-e z, hznegC, ?_⟩
          simp
        simpa [hrecC'] using hzmem
      have hzneg' : z ∈ -Set.recessionCone C' := by
        simpa using hznegC'
      have hzlinealC' :
          z ∈ Set.linealitySpace C' := by
        have : z ∈ (-Set.recessionCone C') ∩ Set.recessionCone C' :=
          ⟨hzneg', hzrecC'⟩
        simpa [Set.linealitySpace] using this
      simpa [hCcl] using hzlinealC'
    have hclosure :
        closure (A '' C') = A '' closure C' :=
      closure_image_eq_image_closure_of_kernel_lineality
        (hCne := hCne') (hCconv := hCconv') A hlineal
    have hclosedA : IsClosed (A '' C') := by
      have hcl' : closure (A '' C') = A '' C' := by
        simpa [hCcl] using hclosure
      exact (closure_eq_iff_isClosed).1 hcl'
    have hAeq : A '' C' = e.symm '' K := by
      ext y
      constructor
      · rintro ⟨x, hxC', rfl⟩
        rcases hxC' with ⟨x0, hx0C, hx0eq⟩
        have hx0 : x = e.symm x0 := hx0eq.symm
        have hAx : A x = e.symm (π x0) := by
          simp [A, hx0]
        have hxK : π x0 ∈ K := by
          exact ⟨x0, hx0C, rfl⟩
        refine ⟨π x0, hxK, ?_⟩
        exact hAx.symm
      · rintro ⟨y0, hy0K, rfl⟩
        rcases hy0K with ⟨x0, hx0C, rfl⟩
        refine ⟨e.symm x0, ?_, ?_⟩
        · exact ⟨x0, hx0C, rfl⟩
        · simp [A]
    have hclosedK' : IsClosed (e.symm '' K) := by
      simpa [hAeq] using hclosedA
    let hhome' := (e.toAffineEquiv).toHomeomorphOfFiniteDimensional
    have hclosedK'' :
        IsClosed ((hhome' : _ → _) '' (e.symm '' K)) :=
      (hhome'.isClosed_image (s := e.symm '' K)).2 hclosedK'
    have hKeq : (e '' (e.symm '' K)) = K := by
      ext x
      constructor
      · rintro ⟨y, ⟨x0, hx0K, hx0eq⟩, rfl⟩
        have hy : y = e.symm x0 := hx0eq.symm
        simpa [hy] using hx0K
      · intro hx
        refine ⟨e.symm x, ?_, ?_⟩
        ·
          refine ⟨x, hx, ?_⟩
          simp
        · simp
    simpa [hKeq, hhome', AffineEquiv.coe_toHomeomorphOfFiniteDimensional] using hclosedK''
  have hfacesK : {F : Set (Fin n → ℝ) | IsFace (𝕜 := ℝ) K F}.Finite := by
    let f : Set (Fin n → ℝ) → Set (Fin n → ℝ) := fun F => C ∩ π ⁻¹' F
    have hK : K = π '' C := rfl
    have hMaps :
        Set.MapsTo f
          {F : Set (Fin n → ℝ) | IsFace (𝕜 := ℝ) K F}
          {F : Set (Fin n → ℝ) | IsFace (𝕜 := ℝ) C F} := by
      intro F hF
      have hface :
          IsFace (𝕜 := ℝ) C (C ∩ π ⁻¹' F) :=
        helperForTheorem_19_1_face_preimage_of_projection
          (n := n) (C := C) (K := K) (F := F) hc hK hCpre hF
      simpa [f] using hface
    have hInj :
        Set.InjOn f {F : Set (Fin n → ℝ) | IsFace (𝕜 := ℝ) K F} := by
      intro F₁ hF₁ F₂ hF₂ hEq
      have hF₁subset : F₁ ⊆ K := hF₁.2.subset
      have hF₂subset : F₂ ⊆ K := hF₂.2.subset
      have hEq' : C ∩ π ⁻¹' F₁ = C ∩ π ⁻¹' F₂ := by
        simpa [f] using hEq
      ext y
      constructor
      · intro hy
        have hyK : y ∈ K := hF₁subset hy
        have hyK' : y ∈ π '' C := by
          simpa [hK] using hyK
        rcases hyK' with ⟨x, hxC, hxy⟩
        have hxpre₁ : x ∈ C ∩ π ⁻¹' F₁ := by
          refine ⟨hxC, ?_⟩
          have hpx : π x ∈ F₁ := by
            have hy' : y ∈ F₁ := hy
            simpa [hxy] using hy'
          simpa using hpx
        have hxpre₂ : x ∈ C ∩ π ⁻¹' F₂ := by
          simpa [hEq'] using hxpre₁
        have hpx : π x ∈ F₂ := by
          exact hxpre₂.2
        simpa [hxy] using hpx
      · intro hy
        have hyK : y ∈ K := hF₂subset hy
        have hyK' : y ∈ π '' C := by
          simpa [hK] using hyK
        rcases hyK' with ⟨x, hxC, hxy⟩
        have hxpre₂ : x ∈ C ∩ π ⁻¹' F₂ := by
          refine ⟨hxC, ?_⟩
          have hpx : π x ∈ F₂ := by
            have hy' : y ∈ F₂ := hy
            simpa [hxy] using hy'
          simpa using hpx
        have hxpre₁ : x ∈ C ∩ π ⁻¹' F₁ := by
          have hEq'' : C ∩ π ⁻¹' F₂ = C ∩ π ⁻¹' F₁ := by
            symm
            exact hEq'
          simpa [hEq''] using hxpre₂
        have hpx : π x ∈ F₁ := by
          exact hxpre₁.2
        simpa [hxy] using hpx
    exact Set.Finite.of_injOn hMaps hInj hfaces
  have hNoLinesK :
      ¬ ∃ y : Fin n → ℝ, y ≠ 0 ∧
        y ∈ (-Set.recessionCone K) ∩ Set.recessionCone K := by
    intro hbad
    rcases hbad with ⟨y, hyne, hylineal⟩
    have hyrec : y ∈ Set.recessionCone K := hylineal.2
    have hyneg : -y ∈ Set.recessionCone K := by
      simpa using hylineal.1
    rcases hKne with ⟨x0, hx0⟩
    have hx0W : x0 ∈ W := hKsubsetW hx0
    have hyrec' :
        ∀ x ∈ K, ∀ t : ℝ, 0 ≤ t → x + t • y ∈ K := by
      simpa [Set.recessionCone] using hyrec
    have h1 : (0 : ℝ) ≤ 1 := by
      norm_num
    have hx0y : x0 + (1 : ℝ) • y ∈ K := hyrec' x0 hx0 1 h1
    have hx0y' : x0 + y ∈ K := by
      simpa using hx0y
    have hx0yW : x0 + y ∈ W := hKsubsetW hx0y'
    have hyW : y ∈ W := by
      have hsub : x0 + y - x0 ∈ W := by
        exact Submodule.sub_mem W hx0yW hx0W
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub
    have hpy : π y = y := hprojW y hyW
    have hyrecC :
        y ∈ Set.recessionCone C := by
      have hyrec'' :
          ∀ x ∈ C, ∀ t : ℝ, 0 ≤ t → x + t • y ∈ C := by
        intro x hx t ht
        have hxK : π x ∈ K := by
          refine ⟨x, hx, rfl⟩
        have hxK' : π x + t • y ∈ K := hyrec' (π x) hxK t ht
        have hπ : π (x + t • y) = π x + t • y := by
          calc
            π (x + t • y) = π x + π (t • y) := by simp
            _ = π x + t • π y := by simp
            _ = π x + t • y := by simpa [hpy]
        have hxpre' : x + t • y ∈ π ⁻¹' K := by
          have : π (x + t • y) ∈ K := by
            simpa [hπ] using hxK'
          simpa using this
        simpa [hCpre] using hxpre'
      simpa [Set.recessionCone] using hyrec''
    have hynegC :
        -y ∈ Set.recessionCone C := by
      have hyrec'neg :
          ∀ x ∈ K, ∀ t : ℝ, 0 ≤ t → x + t • (-y) ∈ K := by
        simpa [Set.recessionCone] using hyneg
      have hyrec'' :
          ∀ x ∈ C, ∀ t : ℝ, 0 ≤ t → x + t • (-y) ∈ C := by
        intro x hx t ht
        have hxK : π x ∈ K := by
          refine ⟨x, hx, rfl⟩
        have hxK' : π x + t • (-y) ∈ K := hyrec'neg (π x) hxK t ht
        have hπ : π (x + t • (-y)) = π x + -(t • π y) := by
          simp [map_add, map_smul, map_neg, smul_neg]
        have hxK'' : π x + -(t • π y) ∈ K := by
          have hxK''' : π x + -(t • y) ∈ K := by
            simpa [smul_neg] using hxK'
          simpa [hpy] using hxK'''
        have hxpre' : x + t • (-y) ∈ π ⁻¹' K := by
          have : π (x + t • (-y)) ∈ K := by
            simpa [hπ] using hxK''
          simpa using this
        simpa [hCpre] using hxpre'
      simpa [Set.recessionCone] using hyrec''
    have hylinealC : y ∈ linealitySpace_fin C := by
      have hyneg' : y ∈ -Set.recessionCone C := by
        simpa using hynegC
      exact ⟨hyneg', hyrecC⟩
    have hyL : y ∈ L := by
      change y ∈ (L : Set _)
      rw [hL]
      exact hylinealC
    have hyWL : y ∈ (W ⊓ L : Submodule ℝ (Fin n → ℝ)) :=
      Submodule.mem_inf.mpr ⟨hyW, hyL⟩
    have hbot : (W ⊓ L : Submodule ℝ (Fin n → ℝ)) = ⊥ := by
      simpa using hWL.inf_eq_bot
    have hy0 : y ∈ (⊥ : Submodule ℝ (Fin n → ℝ)) := by
      simpa [hbot] using hyWL
    have hy0' : y = 0 := by
      simpa using hy0
    exact (hyne hy0').elim
  exact ⟨hclosedK, hfacesK, hNoLinesK⟩

/-- Helper for Theorem 19.1: mixed convex hulls recede along their direction set. -/
lemma helperForTheorem_19_1_mixedConvexHull_recedes
    {n : ℕ} {S₀ S₁ : Set (Fin n → ℝ)} {d x : Fin n → ℝ}
    (hd : d ∈ S₁) (hx : x ∈ mixedConvexHull (n := n) S₀ S₁) :
    ∀ t : ℝ, 0 ≤ t → x + t • d ∈ mixedConvexHull (n := n) S₀ S₁ := by
  intro t ht
  have hx' :
      x ∈ ⋂₀ {C : Set (Fin n → ℝ) |
        Convex ℝ C ∧ S₀ ⊆ C ∧
          ∀ ⦃d⦄, d ∈ S₁ → ∀ ⦃x⦄, x ∈ C → ∀ s : ℝ, 0 ≤ s → x + s • d ∈ C} := by
    simpa [mixedConvexHull] using hx
  refine (Set.mem_sInter).2 ?_
  intro C hC
  have hC' :
      Convex ℝ C ∧ S₀ ⊆ C ∧
        ∀ ⦃d⦄, d ∈ S₁ → ∀ ⦃x⦄, x ∈ C → ∀ s : ℝ, 0 ≤ s → x + s • d ∈ C := by
    simpa using hC
  have hxC : x ∈ C := (Set.mem_sInter).1 hx' C hC
  exact hC'.2.2 hd hxC t ht

/-- Helper for Theorem 19.1: monotonicity of the generated cone. -/
lemma helperForTheorem_19_1_cone_mono
    {n : ℕ} {S T : Set (Fin n → ℝ)} (hST : S ⊆ T) :
    cone n S ⊆ cone n T := by
  intro x hx
  have hsubset : ray n S ⊆ ray n T := by
    intro y hy
    have hy' : y = 0 ∨ y ∈ rayNonneg n S := by
      simpa [ray, Set.mem_insert_iff] using hy
    cases hy' with
    | inl hy0 =>
        subst hy0
        change (0 : Fin n → ℝ) ∈ Set.insert 0 (rayNonneg n T)
        exact (Set.mem_insert_iff).2 (Or.inl rfl)
    | inr hyRay =>
        rcases hyRay with ⟨d, hdS, t, ht, rfl⟩
        have hdT : d ∈ T := hST hdS
        have : t • d ∈ rayNonneg n T := ⟨d, hdT, t, ht, rfl⟩
        exact (Set.mem_insert_iff).2 (Or.inr this)
  have hx' : x ∈ conv (ray n S) := by
    simpa [cone, conv] using hx
  have hx'' : x ∈ conv (ray n T) := by
    have hsubset' : ray n S ⊆ conv (ray n T) := by
      intro y hy
      exact (subset_convexHull (𝕜:=ℝ) (s:=ray n T)) (hsubset hy)
    exact
      (convexHull_min hsubset' (convex_convexHull (𝕜:=ℝ) (s:=ray n T))) hx'
  simpa [cone, conv] using hx''

/-- Helper for Theorem 19.1: recession directions of a subset of a submodule lie in it. -/
lemma helperForTheorem_19_1_recessionCone_subset_submodule
    {n : ℕ} {K : Set (Fin n → ℝ)} {W : Submodule ℝ (Fin n → ℝ)}
    (hKsubset : K ⊆ (W : Set _)) (hKne : K.Nonempty) :
    Set.recessionCone K ⊆ (W : Set _) := by
  intro y hy
  rcases hKne with ⟨x0, hx0⟩
  have hx0W : x0 ∈ W := hKsubset hx0
  have hyrec :
      ∀ x ∈ K, ∀ t : ℝ, 0 ≤ t → x + t • y ∈ K := by
    simpa [Set.recessionCone] using hy
  have h1 : (0 : ℝ) ≤ 1 := by norm_num
  have hx0y : x0 + (1 : ℝ) • y ∈ K := hyrec x0 hx0 1 h1
  have hx0yW : x0 + y ∈ W := by
    have hx0y' : x0 + (1 : ℝ) • y ∈ K := hx0y
    have hx0y'' : x0 + y ∈ K := by
      simpa using hx0y'
    exact hKsubset hx0y''
  have hyW : y ∈ W := by
    have hsub : x0 + y - x0 ∈ W := Submodule.sub_mem W hx0yW hx0W
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub
  exact hyW

/-- Helper for Theorem 19.1: a finite basis yields a finite cone covering a submodule. -/
lemma helperForTheorem_19_1_submodule_subset_cone_of_finiteBasis
    {n : ℕ} (L : Submodule ℝ (Fin n → ℝ)) :
    ∃ (SL : Set (Fin n → ℝ)),
      Set.Finite SL ∧ SL ⊆ (L : Set _) ∧ (L : Set _) ⊆ cone n SL := by
  classical
  let b := Module.finBasis ℝ L
  let SL : Set (Fin n → ℝ) :=
    Set.range (fun i : Fin (Module.finrank ℝ L) => (b i : Fin n → ℝ)) ∪
      Set.range (fun i : Fin (Module.finrank ℝ L) => -(b i : Fin n → ℝ))
  have hSLfinite : Set.Finite SL := by
    have h1 :
        Set.Finite (Set.range (fun i : Fin (Module.finrank ℝ L) => (b i : Fin n → ℝ))) := by
      simpa using (Set.finite_range (fun i : Fin (Module.finrank ℝ L) => (b i : Fin n → ℝ)))
    have h2 :
        Set.Finite (Set.range (fun i : Fin (Module.finrank ℝ L) => -(b i : Fin n → ℝ))) := by
      simpa using (Set.finite_range (fun i : Fin (Module.finrank ℝ L) => -(b i : Fin n → ℝ)))
    exact h1.union h2
  have hSLsubset : SL ⊆ (L : Set _) := by
    intro x hx
    rcases hx with hx | hx
    · rcases hx with ⟨i, rfl⟩
      exact (b i).property
    · rcases hx with ⟨i, rfl⟩
      exact (Submodule.neg_mem L (b i).property)
  have hcone : IsConvexCone n (cone n SL) := by
    simpa [cone_eq_convexConeGenerated (n := n) (S₁ := SL)] using
      (isConvexCone_convexConeGenerated (n := n) (S₁ := SL))
  have hadd :
      ∀ x ∈ cone n SL, ∀ y ∈ cone n SL, x + y ∈ cone n SL :=
    isConvexCone_add_closed n (cone n SL) hcone
  have h0cone : (0 : Fin n → ℝ) ∈ cone n SL := by
    have h0ray : (0 : Fin n → ℝ) ∈ ray n SL := by
      change (0 : Fin n → ℝ) ∈ Set.insert 0 (rayNonneg n SL)
      exact (Set.mem_insert_iff).2 (Or.inl rfl)
    simpa [cone, conv] using (subset_convexHull (𝕜:=ℝ) (s:=ray n SL)) h0ray
  have hLsubset : (L : Set _) ⊆ cone n SL := by
    intro x hx
    let xL : L := ⟨x, hx⟩
    have hxrepr :
        Finset.sum Finset.univ (fun i : Fin (Module.finrank ℝ L) =>
          (b.repr xL) i • (b i : L)) = xL := by
      simpa using (b.sum_repr xL)
    have hxrepr' :
        (∑ i : Fin (Module.finrank ℝ L), (b.repr xL) i • (b i : Fin n → ℝ)) = x := by
      have hcoe :
          (∑ i : Fin (Module.finrank ℝ L), (b.repr xL) i • (b i : Fin n → ℝ)) =
            ((∑ i : Fin (Module.finrank ℝ L), (b.repr xL) i • b i : L) : Fin n → ℝ) := by
        simpa [Submodule.coe_smul] using
          (Submodule.coe_sum (s := Finset.univ)
            (x := fun i : Fin (Module.finrank ℝ L) => (b.repr xL) i • b i)).symm
      have hxrepr'' :
          ((∑ i : Fin (Module.finrank ℝ L), (b.repr xL) i • b i : L) : Fin n → ℝ) = x := by
        have hxrepr''' := congrArg (fun z : L => (z : Fin n → ℝ)) hxrepr
        simpa [xL] using hxrepr'''
      simpa [hcoe] using hxrepr''
    have hterm :
        ∀ i : Fin (Module.finrank ℝ L), (b.repr xL) i • (b i : Fin n → ℝ) ∈ cone n SL := by
      intro i
      by_cases hci : 0 ≤ (b.repr xL) i
      · rcases lt_or_eq_of_le hci with hpos | hzero
        · have hmem : (b i : Fin n → ℝ) ∈ cone n SL := by
            have hb : (b i : Fin n → ℝ) ∈ SL := by
              left
              exact ⟨i, rfl⟩
            have hray : (b i : Fin n → ℝ) ∈ ray n SL := by
              have hray' : (b i : Fin n → ℝ) ∈ rayNonneg n SL := by
                refine ⟨b i, hb, 1, ?_, ?_⟩
                · norm_num
                · simp
              exact (Set.mem_insert_iff).2 (Or.inr hray')
            simpa [cone, conv] using (subset_convexHull (𝕜:=ℝ) (s:=ray n SL)) hray
          exact hcone.1 (b i : Fin n → ℝ) hmem (b.repr xL i) hpos
        · have hzero' : (b.repr xL) i = 0 := by
            simpa [eq_comm] using hzero
          simpa [hzero'] using h0cone
      · have hneg : (b.repr xL) i < 0 := lt_of_not_ge hci
        have hpos : 0 < -(b.repr xL) i := by linarith
        have hmem : (-(b i : Fin n → ℝ)) ∈ cone n SL := by
          have hb : (-(b i : Fin n → ℝ)) ∈ SL := by
            right
            exact ⟨i, rfl⟩
          have hray : (-(b i : Fin n → ℝ)) ∈ ray n SL := by
            have hray' : (-(b i : Fin n → ℝ)) ∈ rayNonneg n SL := by
              refine ⟨-(b i : Fin n → ℝ), hb, 1, ?_, ?_⟩
              · norm_num
              · simp
            exact (Set.mem_insert_iff).2 (Or.inr hray')
          simpa [cone, conv] using (subset_convexHull (𝕜:=ℝ) (s:=ray n SL)) hray
        have hsmul :
            (-(b.repr xL) i) • (-(b i : Fin n → ℝ)) ∈ cone n SL :=
          hcone.1 (-(b i : Fin n → ℝ)) hmem (-(b.repr xL) i) hpos
        have hterm_eq :
            (-(b.repr xL) i) • (-(b i : Fin n → ℝ)) =
              (b.repr xL) i • (b i : Fin n → ℝ) := by
          calc
            (-(b.repr xL) i) • (-(b i : Fin n → ℝ)) =
                -((-(b.repr xL) i) • (b i : Fin n → ℝ)) := by
                  simp [smul_neg]
            _ = -(-(b.repr xL i) • (b i : Fin n → ℝ)) := by
                  simp [neg_smul]
            _ = (b.repr xL) i • (b i : Fin n → ℝ) := by simp
        simpa [hterm_eq] using hsmul
    have hsum :
        ∀ s : Finset (Fin (Module.finrank ℝ L)),
          (Finset.sum s (fun i => (b.repr xL) i • (b i : Fin n → ℝ))) ∈ cone n SL := by
      intro s
      refine Finset.induction_on s ?_ ?_
      · simpa using h0cone
      · intro a s ha hs
        have ha' : (b.repr xL) a • (b a : Fin n → ℝ) ∈ cone n SL := hterm a
        have hs' :
            (Finset.sum s (fun i => (b.repr xL) i • (b i : Fin n → ℝ))) ∈ cone n SL := hs
        have hsum' :
            (b.repr xL) a • (b a : Fin n → ℝ) +
              (Finset.sum s (fun i => (b.repr xL) i • (b i : Fin n → ℝ))) ∈ cone n SL :=
          hadd ((b.repr xL) a • (b a : Fin n → ℝ)) ha'
            (Finset.sum s (fun i => (b.repr xL) i • (b i : Fin n → ℝ))) hs'
        simpa [Finset.sum_insert, ha, add_comm, add_left_comm, add_assoc] using hsum'
    have hxmem :
        (∑ i : Fin (Module.finrank ℝ L), (b.repr xL) i • (b i : Fin n → ℝ)) ∈ cone n SL := by
      simpa using (hsum Finset.univ)
    simpa [hxrepr'] using hxmem
  exact ⟨SL, hSLfinite, hSLsubset, hLsubset⟩


end Section19
end Chap19
