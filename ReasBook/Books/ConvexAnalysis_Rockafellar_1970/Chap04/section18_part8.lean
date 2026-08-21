/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Changyu Zou, Yunxi Duan, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section17_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section18_part7

open scoped Pointwise

section Chap04
section Section18

noncomputable section

variable {𝕜 E : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [SMul 𝕜 E]

set_option maxHeartbeats 600000

/-- A closed half-affine set of affine direction finrank `1` is a ray. -/
lemma exists_eq_image_add_smul_Ici_of_closedHalf_affine_finrank_one {n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin n))} (hCne : C.Nonempty)
    (hfin : Module.finrank ℝ (affineSpan ℝ C).direction = 1)
    (hNoLines : ¬ ∃ y : EuclideanSpace ℝ (Fin n), y ≠ 0 ∧
      y ∈ (-Set.recessionCone C) ∩ Set.recessionCone C)
    (hHalf :
      ∃ (A : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)))
          (f : (EuclideanSpace ℝ (Fin n)) →ₗ[ℝ] ℝ) (a : ℝ),
        f ≠ 0 ∧ C = (A : Set (EuclideanSpace ℝ (Fin n))) ∩ {x | f x ≤ a}) :
    ∃ x0 d : EuclideanSpace ℝ (Fin n), d ≠ 0 ∧
      C = (fun t : ℝ => x0 + t • d) '' Set.Ici (0 : ℝ) := by
  classical
  rcases hHalf with ⟨A, f, a, _hfne, hCeq⟩
  let A0 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)) := affineSpan ℝ C
  have hCsubA : C ⊆ (A : Set (EuclideanSpace ℝ (Fin n))) := by
    intro x hx
    have hx' : x ∈ (A : Set (EuclideanSpace ℝ (Fin n))) ∩ {x | f x ≤ a} := by
      simpa [hCeq] using hx
    exact hx'.1
  have hA0le : A0 ≤ A := affineSpan_le_of_subset_coe hCsubA
  have hCeqA0 :
      C = (A0 : Set (EuclideanSpace ℝ (Fin n))) ∩ {x | f x ≤ a} := by
    ext x; constructor
    · intro hx
      have hx' : x ∈ (A : Set (EuclideanSpace ℝ (Fin n))) ∩ {x | f x ≤ a} := by
        simpa [hCeq] using hx
      refine ⟨?_, hx'.2⟩
      exact subset_affineSpan (k := ℝ) (s := C) hx
    · intro hx
      have hxA : x ∈ (A : Set (EuclideanSpace ℝ (Fin n))) := hA0le hx.1
      have hx' : x ∈ (A : Set (EuclideanSpace ℝ (Fin n))) ∩ {x | f x ≤ a} :=
        ⟨hxA, hx.2⟩
      simpa [hCeq] using hx'
  have hpos : 0 < Module.finrank ℝ A0.direction := by
    have hpos' : (0 : ℕ) < Module.finrank ℝ (affineSpan ℝ C).direction := by
      rw [hfin]
      exact Nat.succ_pos 0
    simpa [A0] using hpos'
  obtain ⟨v, hvne⟩ :=
    (Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := A0.direction)).1 hpos
  let v' : EuclideanSpace ℝ (Fin n) := v
  have hvdir : v' ∈ A0.direction := v.property
  have hvne' : v' ≠ 0 := by
    intro hv0
    apply hvne
    apply Subtype.ext
    simpa [v'] using hv0
  have hfv : f v' ≠ 0 := by
    intro hfv
    have hvrec : v' ∈ Set.recessionCone C := by
      intro x hx t ht
      have hx' : x ∈ (A0 : Set (EuclideanSpace ℝ (Fin n))) ∩ {x | f x ≤ a} := by
        simpa [hCeqA0] using hx
      have hxA0 : x ∈ A0 := hx'.1
      have hxle : f x ≤ a := hx'.2
      have hvdir' : t • v' ∈ A0.direction := by
        simpa using (A0.direction.smul_mem t hvdir)
      have hxA0' : (t • v') +ᵥ x ∈ A0 :=
        AffineSubspace.vadd_mem_of_mem_direction (s := A0) hvdir' hxA0
      have hxA0'' : x + t • v' ∈ (A0 : Set (EuclideanSpace ℝ (Fin n))) := by
        simpa [vadd_eq_add, add_comm, add_left_comm, add_assoc] using hxA0'
      have hfx : f (x + t • v') ≤ a := by
        calc
          f (x + t • v') = f x + t * f v' := by
            simp [map_add, map_smul, smul_eq_mul]
          _ = f x := by simp [hfv]
          _ ≤ a := hxle
      have hx'' :
          x + t • v' ∈ (A0 : Set (EuclideanSpace ℝ (Fin n))) ∩ {x | f x ≤ a} :=
        ⟨hxA0'', hfx⟩
      simpa [hCeqA0] using hx''
    have hvrec_neg : (-v') ∈ Set.recessionCone C := by
      intro x hx t ht
      have hx' : x ∈ (A0 : Set (EuclideanSpace ℝ (Fin n))) ∩ {x | f x ≤ a} := by
        simpa [hCeqA0] using hx
      have hxA0 : x ∈ A0 := hx'.1
      have hxle : f x ≤ a := hx'.2
      have hvdir' : t • (-v') ∈ A0.direction := by
        simpa using (A0.direction.smul_mem t (A0.direction.neg_mem hvdir))
      have hxA0' : (t • (-v')) +ᵥ x ∈ A0 :=
        AffineSubspace.vadd_mem_of_mem_direction (s := A0) hvdir' hxA0
      have hxA0'' : x + t • (-v') ∈ (A0 : Set (EuclideanSpace ℝ (Fin n))) := by
        simpa [vadd_eq_add, add_comm, add_left_comm, add_assoc] using hxA0'
      have hfx : f (x + t • (-v')) ≤ a := by
        calc
          f (x + t • (-v')) = f x + t * f (-v') := by
            simp [map_add, map_smul, smul_eq_mul]
          _ = f x := by simp [hfv]
          _ ≤ a := hxle
      have hx'' :
          x + t • (-v') ∈ (A0 : Set (EuclideanSpace ℝ (Fin n))) ∩ {x | f x ≤ a} :=
        ⟨hxA0'', hfx⟩
      simpa [hCeqA0] using hx''
    have hlin :
        ∃ y : EuclideanSpace ℝ (Fin n), y ≠ 0 ∧
          y ∈ (-Set.recessionCone C) ∩ Set.recessionCone C := by
      refine ⟨v', hvne', ?_⟩
      refine ⟨?_, hvrec⟩
      simpa [Set.mem_neg] using hvrec_neg
    exact hNoLines hlin
  let d0 : A0.direction := if hlt : f v' < 0 then v else -v
  let d : EuclideanSpace ℝ (Fin n) := d0
  have hd0ne : (d0 : A0.direction) ≠ 0 := by
    by_cases hlt : f v' < 0
    · simpa [d0, hlt] using hvne
    · have : (-v : A0.direction) ≠ 0 := by simpa using (neg_ne_zero.mpr hvne)
      simpa [d0, hlt] using this
  have hdne : d ≠ 0 := by
    intro h0
    apply hd0ne
    apply Subtype.ext
    simpa [d] using h0
  have hfdlt : f d < 0 := by
    by_cases hlt : f v' < 0
    ·
      have : d = v' := by
        simp [d, d0, hlt, v']
      simpa [this] using hlt
    ·
      have hgt : 0 < f v' := by
        have hge : 0 ≤ f v' := not_lt.mp hlt
        exact lt_of_le_of_ne hge (ne_comm.mp hfv)
      have : d = -v' := by simp [d, d0, hlt, v']
      have : f d = -f v' := by simp [this]
      have hlt' : -f v' < 0 := by nlinarith
      simpa [this] using hlt'
  rcases hCne with ⟨x1, hx1⟩
  have hx1' : x1 ∈ (A0 : Set (EuclideanSpace ℝ (Fin n))) ∩ {x | f x ≤ a} := by
    simpa [hCeqA0] using hx1
  have hx1le : f x1 ≤ a := hx1'.2
  let t0 : ℝ := (a - f x1) / (-f d)
  have ht0 : 0 ≤ t0 := by
    have hnum : 0 ≤ a - f x1 := sub_nonneg.mpr hx1le
    have hden : 0 < -f d := by nlinarith [hfdlt]
    exact div_nonneg hnum (le_of_lt hden)
  let x0 : EuclideanSpace ℝ (Fin n) := x1 + t0 • (-d)
  have hd_dir : d ∈ A0.direction := d0.property
  have hx0A0 : x0 ∈ A0 := by
    have hdir' : t0 • (-d) ∈ A0.direction := by
      simpa using (A0.direction.smul_mem t0 (A0.direction.neg_mem hd_dir))
    have hx0A0' : (t0 • (-d)) +ᵥ x1 ∈ A0 :=
      AffineSubspace.vadd_mem_of_mem_direction (s := A0) hdir' hx1'.1
    have hx0A0'' : t0 • (-d) + x1 ∈ A0 := by
      simpa [vadd_eq_add] using hx0A0'
    simpa [x0, add_comm, add_left_comm, add_assoc] using hx0A0''
  have hfx0 : f x0 = a := by
    have h1 : f x0 = f x1 + t0 * (-f d) := by
      calc
        f x0 = f (x1 + t0 • (-d)) := by rfl
        _ = f x1 + f (t0 • (-d)) := by
          exact map_add f x1 (t0 • (-d))
        _ = f x1 + t0 • f (-d) := by
          exact congrArg (fun z => f x1 + z) (map_smul f t0 (-d))
        _ = f x1 + t0 * f (-d) := by
          rw [smul_eq_mul]
        _ = f x1 + t0 * (-f d) := by
          rw [map_neg]
    have hden : (-f d) ≠ 0 := by
      have hden' : 0 < -f d := by
        simpa using (neg_pos.mpr hfdlt)
      exact ne_of_gt hden'
    have h2 : t0 * (-f d) = a - f x1 := by
      have hdiv :
          (a - f x1) / (-f d) * (-f d) = (a - f x1) * (-f d) / (-f d) := by
        exact (div_mul_eq_mul_div (a - f x1) (-f d) (-f d))
      calc
        (a - f x1) / (-f d) * (-f d) = (a - f x1) * (-f d) / (-f d) := hdiv
        _ = a - f x1 := by
          exact mul_div_cancel_right₀ (a - f x1) hden
    calc
      f x0 = f x1 + t0 * (-f d) := h1
      _ = f x1 + (a - f x1) := by rw [h2]
      _ = a := by ring_nf
  have hsubset1 : C ⊆ (fun t : ℝ => x0 + t • d) '' Set.Ici (0 : ℝ) := by
    intro x hxC
    have hx' : x ∈ (A0 : Set (EuclideanSpace ℝ (Fin n))) ∩ {x | f x ≤ a} := by
      simpa [hCeqA0] using hxC
    have hxA0 : x ∈ A0 := hx'.1
    have hxle : f x ≤ a := hx'.2
    have hxv : x -ᵥ x0 ∈ A0.direction :=
      AffineSubspace.vsub_mem_direction hxA0 hx0A0
    have hmul :
        ∀ w : A0.direction, ∃ t : ℝ, t • d0 = w := by
      exact (finrank_eq_one_iff_of_nonzero' (v := d0) (nz := hd0ne)).1 hfin
    rcases hmul ⟨x -ᵥ x0, hxv⟩ with ⟨t, ht⟩
    have hxv' : x -ᵥ x0 = t • d := by
      have := congrArg Subtype.val ht
      simpa [d] using this.symm
    have hxv'' : x - x0 = t • d := by
      simpa [vsub_eq_sub] using hxv'
    have hx_eq : x = x0 + t • d := by
      have hx_eq' : x = t • d + x0 := (sub_eq_iff_eq_add).1 hxv''
      simpa [add_comm] using hx_eq'
    have hfxle : f (x - x0) ≤ 0 := by
      have : f x - f x0 ≤ 0 := by linarith [hxle, hfx0]
      simpa [map_sub] using this
    have htle : t * f d ≤ 0 := by
      have : f (x - x0) = t * f d := by
        simp [hxv'', map_smul]
      simpa [this] using hfxle
    have ht0 : 0 ≤ t := by
      have htle' : t * f d ≤ 0 * f d := by simpa using htle
      exact (mul_le_mul_right_of_neg hfdlt).1 htle'
    refine ⟨t, ht0, hx_eq.symm⟩
  have hsubset2 :
      (fun t : ℝ => x0 + t • d) '' Set.Ici (0 : ℝ) ⊆ C := by
    intro x hx
    rcases hx with ⟨t, ht, rfl⟩
    have hxA0 : x0 + t • d ∈ (A0 : Set (EuclideanSpace ℝ (Fin n))) := by
      have hdir' : t • d ∈ A0.direction := by
        simpa using (A0.direction.smul_mem t hd_dir)
      have hxA0' : (t • d) +ᵥ x0 ∈ A0 :=
        AffineSubspace.vadd_mem_of_mem_direction (s := A0) hdir' hx0A0
      have hxA0'' : t • d + x0 ∈ A0 := by
        simpa [vadd_eq_add] using hxA0'
      rw [add_comm]
      exact hxA0''
    have hfx : f (x0 + t • d) ≤ a := by
      have hnonpos : t * f d ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos ht (le_of_lt hfdlt)
      have : f (x0 + t • d) = a + t * f d := by
        have h1' : f (x0 + t • d) = f x0 + f (t • d) := map_add f x0 (t • d)
        have h2' : f (t • d) = t * f d := by
          simp [smul_eq_mul]
        calc
          f (x0 + t • d) = f x0 + f (t • d) := h1'
          _ = f x0 + t * f d := by rw [h2']
          _ = a + t * f d := by simp [hfx0]
      linarith
    have hx' :
        x0 + t • d ∈ (A0 : Set (EuclideanSpace ℝ (Fin n))) ∩ {x | f x ≤ a} :=
      ⟨hxA0, hfx⟩
    simpa [hCeqA0] using hx'
  refine ⟨x0, d, hdne, ?_⟩
  exact Set.Subset.antisymm hsubset1 hsubset2

set_option maxHeartbeats 200000

/-- In the closed-half-affine finrank-one case, every point lies in the mixed convex hull. -/
lemma ray_subset_mixedConvexHull_of_closedHalf_affine_finrank_one {n : ℕ}
    {C : Set (Fin n → ℝ)} (hCconv : Convex ℝ C)
    (hNoLines : ¬ ∃ y : Fin n → ℝ, y ≠ 0 ∧
      y ∈ (-Set.recessionCone C) ∩ Set.recessionCone C)
    (hCne : C.Nonempty)
    (hfin : Module.finrank ℝ (affineSpan ℝ C).direction = 1)
    (hHalf :
      ∃ (A : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)))
          (f : (EuclideanSpace ℝ (Fin n)) →ₗ[ℝ] ℝ) (a : ℝ),
        f ≠ 0 ∧ (euclideanEquiv n).symm '' C =
          (A : Set (EuclideanSpace ℝ (Fin n))) ∩ {x | f x ≤ a}) :
    C ⊆ mixedConvexHull (n := n) (C.extremePoints ℝ)
      {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d} := by
  classical
  let e := euclideanEquiv n
  have hCneE : (e.symm '' C).Nonempty := by
    rcases hCne with ⟨x, hx⟩
    exact ⟨e.symm x, ⟨x, hx, rfl⟩⟩
  have hfinE :
      Module.finrank ℝ (affineSpan ℝ (e.symm '' C)).direction = 1 := by
    exact (finrank_direction_affineSpan_equiv (n := n) (C := C)).trans hfin
  have hNoLinesE :
      ¬ ∃ y : EuclideanSpace ℝ (Fin n), y ≠ 0 ∧
        y ∈ (-Set.recessionCone (e.symm '' C)) ∩ Set.recessionCone (e.symm '' C) :=
    noLines_equiv_fin (n := n) (C := C) hNoLines
  rcases
      exists_eq_image_add_smul_Ici_of_closedHalf_affine_finrank_one (n := n) (C := e.symm '' C)
        hCneE hfinE hNoLinesE hHalf with ⟨x0E, dE, hdneE, hCeqE⟩
  have himageC : e '' (e.symm '' C) = C := by
    ext x
    constructor
    · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
      simpa using hw
    · intro hx
      exact ⟨e.symm x, ⟨x, hx, rfl⟩, by simp⟩
  have hCeq : C = (fun t : ℝ => e x0E + t • e dE) '' Set.Ici (0 : ℝ) := by
    ext x
    constructor
    · intro hx
      have hxE : e.symm x ∈ (e.symm '' C) := ⟨x, hx, rfl⟩
      rcases (by simpa [hCeqE] using hxE) with ⟨t, ht, hxt⟩
      refine ⟨t, ht, ?_⟩
      have hx' : e (x0E + t • dE) = x := by
        have := congrArg e hxt
        simpa using this
      calc
        e x0E + t • e dE = e (x0E + t • dE) := by simp [map_add, map_smul]
        _ = x := hx'
    · rintro ⟨t, ht, rfl⟩
      have hxE : x0E + t • dE ∈ (e.symm '' C) := by
        have : x0E + t • dE ∈ (fun t : ℝ => x0E + t • dE) '' Set.Ici (0 : ℝ) :=
          ⟨t, ht, rfl⟩
        simpa [hCeqE] using this
      have hx : e (x0E + t • dE) ∈ e '' (e.symm '' C) := ⟨x0E + t • dE, hxE, rfl⟩
      have hx' : e x0E + t • e dE ∈ e '' (e.symm '' C) := by
        simpa [map_add, map_smul] using hx
      simpa [himageC] using hx'
  have hdne : (e dE) ≠ 0 := by
    intro h0
    apply hdneE
    have : dE = 0 := by
      have := congrArg e.symm h0
      simpa using this
    exact this
  intro x hx
  rcases (by simpa [hCeq] using hx) with ⟨t, ht, rfl⟩
  have hx0ext : e x0E ∈ C.extremePoints ℝ :=
    mem_extremePoints_endpoint_of_eq_image_add_smul_Ici (n := n) (C := C) hdne hCeq
  have hdir : IsExtremeDirection (𝕜 := ℝ) C (e dE) :=
    isExtremeDirection_of_eq_image_add_smul_Ici (n := n) (C := C) (x0 := e x0E) (d := e dE) hdne
      hCeq hCconv
  have ht_ray : t • e dE ∈ ray n {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d} := by
    have ht_raynonneg :
        t • e dE ∈ rayNonneg n {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d} := by
      exact ⟨e dE, hdir, t, ht, rfl⟩
    exact (Set.mem_insert_iff).2 (Or.inr ht_raynonneg)
  have hxadd :
      e x0E + t • e dE ∈ C.extremePoints ℝ +
        ray n {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d} := by
    exact Set.mem_add.mpr ⟨e x0E, hx0ext, t • e dE, ht_ray, rfl⟩
  exact
    (add_ray_subset_mixedConvexHull (n := n) (S₀ := C.extremePoints ℝ)
        (S₁ := {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d})) hxadd

/-- Base case: one-dimensional closed convex sets without lines are generated by extreme points and
directions. -/
lemma closedConvex_eq_mixedConvexHull_of_finrank_direction_eq_one {n : ℕ}
    {C : Set (Fin n → ℝ)} (hCclosed : IsClosed C) (hCconv : Convex ℝ C)
    (hNoLines : ¬ ∃ y : Fin n → ℝ, y ≠ 0 ∧
      y ∈ (-Set.recessionCone C) ∩ Set.recessionCone C)
    (hfin : Module.finrank ℝ (affineSpan ℝ C).direction = 1) :
    C =
      mixedConvexHull (n := n) (C.extremePoints ℝ)
        {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d} := by
  classical
  refine Set.Subset.antisymm ?_ ?_
  ·
    by_cases hCne : C.Nonempty
    ·
      by_cases hHalf :
          ∃ (A : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)))
            (f : (EuclideanSpace ℝ (Fin n)) →ₗ[ℝ] ℝ) (a : ℝ),
            f ≠ 0 ∧ (euclideanEquiv n).symm '' C =
              (A : Set (EuclideanSpace ℝ (Fin n))) ∩ {x | f x ≤ a}
      ·
        intro x hxC
        exact
          (ray_subset_mixedConvexHull_of_closedHalf_affine_finrank_one (n := n) (C := C) hCconv
              hNoLines hCne hfin hHalf) hxC
      ·
        intro x hxC
        have hC_not_affine :
            ¬ ∃ A : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)),
              (A : Set (EuclideanSpace ℝ (Fin n))) = (euclideanEquiv n).symm '' C := by
          intro hAff
          rcases hAff with ⟨A, hAeq⟩
          let e := euclideanEquiv n
          have hAeq' : (A : Set (EuclideanSpace ℝ (Fin n))) = e.symm '' C := by
            simpa using hAeq
          have hspan : affineSpan ℝ (e.symm '' C) = A := by
            simpa [hAeq'] using (AffineSubspace.affineSpan_coe (s := A) (k := ℝ))
          have hfinE :
              Module.finrank ℝ (affineSpan ℝ (e.symm '' C)).direction = 1 :=
            (finrank_direction_affineSpan_equiv (n := n) (C := C)).trans hfin
          have hfinA : Module.finrank ℝ A.direction = 1 := by
            rw [← hspan]
            exact hfinE
          have hpos : 0 < Module.finrank ℝ A.direction := by
            rw [hfinA]
            exact Nat.succ_pos 0
          obtain ⟨v, hvne⟩ :=
            (Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := A.direction)).1 hpos
          let v' : EuclideanSpace ℝ (Fin n) := v
          have hvdir : v' ∈ A.direction := v.property
          have hvne' : v' ≠ 0 := by
            intro hv0
            apply hvne
            apply Subtype.ext
            simpa [v'] using hv0
          have hvrec : v' ∈ Set.recessionCone (e.symm '' C) := by
            intro x hx t ht
            have hxA : x ∈ A := by simpa [hAeq'.symm] using hx
            have hvdir' : t • v' ∈ A.direction := by
              simpa using (A.direction.smul_mem t hvdir)
            have hxA' : (t • v') +ᵥ x ∈ A :=
              AffineSubspace.vadd_mem_of_mem_direction (s := A) hvdir' hxA
            have hxA'' : x + t • v' ∈ (A : Set (EuclideanSpace ℝ (Fin n))) := by
              simpa [vadd_eq_add, add_comm, add_left_comm, add_assoc] using hxA'
            simpa [hAeq'] using hxA''
          have hvrec_neg : (-v') ∈ Set.recessionCone (e.symm '' C) := by
            intro x hx t ht
            have hxA : x ∈ A := by simpa [hAeq'.symm] using hx
            have hvdir' : t • (-v') ∈ A.direction := by
              simpa using (A.direction.smul_mem t (A.direction.neg_mem hvdir))
            have hxA' : (t • (-v')) +ᵥ x ∈ A :=
              AffineSubspace.vadd_mem_of_mem_direction (s := A) hvdir' hxA
            have hxA'' : x + t • (-v') ∈ (A : Set (EuclideanSpace ℝ (Fin n))) := by
              simpa [vadd_eq_add, add_comm, add_left_comm, add_assoc] using hxA'
            simpa [hAeq'] using hxA''
          have hlin :
              ∃ y : EuclideanSpace ℝ (Fin n), y ≠ 0 ∧
                y ∈ (-Set.recessionCone (e.symm '' C)) ∩ Set.recessionCone (e.symm '' C) := by
            refine ⟨v', hvne', ?_⟩
            refine ⟨?_, hvrec⟩
            simpa [Set.mem_neg] using hvrec_neg
          have hNoLinesE :
              ¬ ∃ y : EuclideanSpace ℝ (Fin n), y ≠ 0 ∧
                y ∈ (-Set.recessionCone (e.symm '' C)) ∩ Set.recessionCone (e.symm '' C) :=
            noLines_equiv_fin (n := n) (C := C) hNoLines
          exact hNoLinesE hlin
        have hIH :
            ∀ ⦃F : Set (Fin n → ℝ)⦄, IsClosed F → Convex ℝ F →
              (¬ ∃ y : Fin n → ℝ, y ≠ 0 ∧
                y ∈ (-Set.recessionCone F) ∩ Set.recessionCone F) →
              Module.finrank ℝ (affineSpan ℝ F).direction <
                Module.finrank ℝ (affineSpan ℝ C).direction →
                F ⊆ mixedConvexHull (n := n) (F.extremePoints ℝ)
                  {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) F d} := by
          intro F hFclosed hFconv hNoLinesF hfinlt
          by_cases hFne : F.Nonempty
          ·
            have hfinF : Module.finrank ℝ (affineSpan ℝ F).direction = 0 := by
              have hlt : Module.finrank ℝ (affineSpan ℝ F).direction < 1 := by
                simpa [hfin] using hfinlt
              exact (Nat.lt_one_iff.mp hlt)
            have hEq :=
              closedConvex_eq_mixedConvexHull_of_finrank_direction_eq_zero (n := n) (C := F)
                hFclosed hFconv hfinF
            intro y hy
            have hy' : y ∈ F := hy
            rw [hEq] at hy'
            exact hy'
          ·
            intro y hy
            exact (hFne ⟨y, hy⟩).elim
        have hbdy :
            ∀ y ∈ euclideanRelativeBoundary_fin n C,
              y ∈ mixedConvexHull (n := n) (C.extremePoints ℝ)
                {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d} := by
          intro y hy
          exact
            mem_mixedConvexHull_of_mem_euclideanRelativeBoundary_under_IH (n := n) (C := C)
              hCclosed hCconv hNoLines hIH hy
        by_cases hxri : x ∈ euclideanRelativeInterior_fin n C
        ·
          exact
            mem_mixedConvexHull_of_mem_euclideanRelativeInterior_of_boundary_in_hull (n := n)
              (C := C) hCclosed hCconv hC_not_affine hHalf hbdy hxri
        ·
          have hxrb : x ∈ euclideanRelativeBoundary_fin n C := by
            have : x ∈ C \ euclideanRelativeInterior_fin n C := ⟨hxC, hxri⟩
            simpa [euclideanRelativeBoundary_fin_eq_diff_of_isClosed (hCclosed := hCclosed)] using
              this
          exact hbdy x hxrb
    ·
      intro x hx
      exact (hCne ⟨x, hx⟩).elim
  ·
    refine
      mixedConvexHull_subset_of_convex_of_subset_of_recedes (n := n)
        (S₀ := C.extremePoints ℝ)
        (S₁ := {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d}) (Ccand := C) hCconv
        ?_ ?_
    · exact extremePoints_subset
    · intro d hd x hxC t ht
      have hdrec :
          d ∈ Set.recessionCone C :=
        mem_recessionCone_of_isExtremeDirection_fin (hCclosed := hCclosed) (by simpa using hd)
      exact hdrec hxC ht

/-- In dimension > 1, a closed convex set with no lines is neither affine nor a closed half
of an affine set. -/
lemma not_affine_or_closedHalf_of_noLines_finrank_gt_one {n : ℕ}
    {C : Set (Fin n → ℝ)}
    (hNoLines : ¬ ∃ y : Fin n → ℝ, y ≠ 0 ∧
      y ∈ (-Set.recessionCone C) ∩ Set.recessionCone C)
    (hfin : 1 < Module.finrank ℝ (affineSpan ℝ C).direction) :
    (¬ ∃ A : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)),
        (A : Set (EuclideanSpace ℝ (Fin n))) = (euclideanEquiv n).symm '' C) ∧
      (¬ ∃ (A : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)))
          (f : (EuclideanSpace ℝ (Fin n)) →ₗ[ℝ] ℝ) (a : ℝ),
          f ≠ 0 ∧ (euclideanEquiv n).symm '' C =
            (A : Set (EuclideanSpace ℝ (Fin n))) ∩ {x | f x ≤ a}) := by
  classical
  let e := euclideanEquiv n
  have hNoLinesE :
      ¬ ∃ y : EuclideanSpace ℝ (Fin n), y ≠ 0 ∧
        y ∈ (-Set.recessionCone (e.symm '' C)) ∩ Set.recessionCone (e.symm '' C) :=
    noLines_equiv_fin (n := n) (C := C) hNoLines
  have hfinE :
      1 < Module.finrank ℝ (affineSpan ℝ (e.symm '' C)).direction := by
    rw [finrank_direction_affineSpan_equiv (n := n) (C := C)]
    exact hfin
  constructor
  ·
    intro hAff
    rcases hAff with ⟨A, hAeq⟩
    have hAeq' : (A : Set (EuclideanSpace ℝ (Fin n))) = e.symm '' C := by
      simpa using hAeq
    have hspan : affineSpan ℝ (e.symm '' C) = A := by
      simpa [hAeq'] using (AffineSubspace.affineSpan_coe (s := A) (k := ℝ))
    have hfinA : 1 < Module.finrank ℝ A.direction := by
      rw [← hspan]
      exact hfinE
    have hpos : 0 < Module.finrank ℝ A.direction := by
      exact lt_trans (Nat.succ_pos 0) hfinA
    obtain ⟨v, hvne⟩ :=
      (Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := A.direction)).1 hpos
    let v' : EuclideanSpace ℝ (Fin n) := v
    have hvdir : v' ∈ A.direction := v.property
    have hvne' : v' ≠ 0 := by
      intro hv0
      apply hvne
      apply Subtype.ext
      simpa [v'] using hv0
    have hvrec : v' ∈ Set.recessionCone (e.symm '' C) := by
      intro x hx t ht
      have hxA : x ∈ A := by simpa [hAeq'.symm] using hx
      have hvdir' : t • v' ∈ A.direction := by
        simpa using (A.direction.smul_mem t hvdir)
      have hxA' : (t • v') +ᵥ x ∈ A :=
        AffineSubspace.vadd_mem_of_mem_direction (s := A) hvdir' hxA
      have hxA'' : x + t • v' ∈ (A : Set (EuclideanSpace ℝ (Fin n))) := by
        simpa [vadd_eq_add, add_comm, add_left_comm, add_assoc] using hxA'
      simpa [hAeq'] using hxA''
    have hvrec_neg : (-v') ∈ Set.recessionCone (e.symm '' C) := by
      intro x hx t ht
      have hxA : x ∈ A := by simpa [hAeq'.symm] using hx
      have hvdir' : t • (-v') ∈ A.direction := by
        simpa using (A.direction.smul_mem t (A.direction.neg_mem hvdir))
      have hxA' : (t • (-v')) +ᵥ x ∈ A :=
        AffineSubspace.vadd_mem_of_mem_direction (s := A) hvdir' hxA
      have hxA'' : x + t • (-v') ∈ (A : Set (EuclideanSpace ℝ (Fin n))) := by
        simpa [vadd_eq_add, add_comm, add_left_comm, add_assoc] using hxA'
      simpa [hAeq'] using hxA''
    have hlin :
        ∃ y : EuclideanSpace ℝ (Fin n), y ≠ 0 ∧
          y ∈ (-Set.recessionCone (e.symm '' C)) ∩ Set.recessionCone (e.symm '' C) := by
      refine ⟨v', hvne', ?_⟩
      refine ⟨?_, hvrec⟩
      simpa [Set.mem_neg] using hvrec_neg
    exact hNoLinesE hlin
  ·
    intro hHalf
    rcases hHalf with ⟨A, f, a, hfne, hCeq⟩
    have hCsubA : (e.symm '' C) ⊆ (A : Set (EuclideanSpace ℝ (Fin n))) := by
      intro x hx
      have hx' : x ∈ (A : Set (EuclideanSpace ℝ (Fin n))) ∩ {x | f x ≤ a} := by
        rw [← hCeq]
        exact hx
      exact hx'.1
    have hspan_le : affineSpan ℝ (e.symm '' C) ≤ A :=
      affineSpan_le_of_subset_coe hCsubA
    have hdir_le : (affineSpan ℝ (e.symm '' C)).direction ≤ A.direction :=
      AffineSubspace.direction_le hspan_le
    have hfinA : 1 < Module.finrank ℝ A.direction := by
      exact lt_of_lt_of_le hfinE (Submodule.finrank_mono hdir_le)
    let fA : A.direction →ₗ[ℝ] ℝ := f.comp A.direction.subtype
    have hrange_le : Module.finrank ℝ (LinearMap.range fA) ≤ 1 := by
      simpa using
        (Submodule.finrank_mono (le_top : LinearMap.range fA ≤ (⊤ : Submodule ℝ ℝ)))
    have hkerpos : 0 < Module.finrank ℝ (LinearMap.ker fA) := by
      by_cases hker0 : Module.finrank ℝ (LinearMap.ker fA) = 0
      ·
        have hsum :
            Module.finrank ℝ A.direction =
              Module.finrank ℝ (LinearMap.range fA) := by
          have hsum' := (LinearMap.finrank_range_add_finrank_ker (f := fA)).symm
          simpa [hker0] using hsum'
        have hAle : Module.finrank ℝ A.direction ≤ 1 := by
          simpa [hsum] using hrange_le
        exfalso
        exact (not_lt_of_ge hAle) hfinA
      · exact Nat.pos_of_ne_zero hker0
    obtain ⟨v, hvne⟩ :=
      (Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := LinearMap.ker fA)).1 hkerpos
    let v' : EuclideanSpace ℝ (Fin n) := (v : A.direction)
    have hvdir : v' ∈ A.direction := (v : A.direction).property
    have hvne' : v' ≠ 0 := by
      intro hv0
      apply hvne
      apply Subtype.ext
      simpa [v'] using hv0
    have hvf : f v' = 0 := by
      change fA v = 0
      exact v.property
    have hvrec : v' ∈ Set.recessionCone (e.symm '' C) := by
      intro x hx t ht
      have hx' : x ∈ (A : Set (EuclideanSpace ℝ (Fin n))) ∩ {x | f x ≤ a} := by
        rw [← hCeq]
        exact hx
      have hxA : x ∈ A := hx'.1
      have hxle : f x ≤ a := hx'.2
      have hvdir' : t • v' ∈ A.direction := by
        simpa using (A.direction.smul_mem t hvdir)
      have hxA' : (t • v') +ᵥ x ∈ A :=
        AffineSubspace.vadd_mem_of_mem_direction (s := A) hvdir' hxA
      have hfx : f (x + t • v') ≤ a := by
        calc
          f (x + t • v') = f x + t * f v' := by
            simp [map_add, map_smul, smul_eq_mul]
          _ = f x := by simp [hvf]
          _ ≤ a := hxle
      have hxA'' : x + t • v' ∈ (A : Set (EuclideanSpace ℝ (Fin n))) := by
        simpa [vadd_eq_add, add_comm, add_left_comm, add_assoc] using hxA'
      have hxC : x + t • v' ∈ (e.symm '' C) := by
        have : x + t • v' ∈ (A : Set (EuclideanSpace ℝ (Fin n))) ∩ {x | f x ≤ a} := by
          exact ⟨hxA'', hfx⟩
        rw [hCeq]
        exact this
      exact hxC
    have hvrec_neg : (-v') ∈ Set.recessionCone (e.symm '' C) := by
      intro x hx t ht
      have hx' : x ∈ (A : Set (EuclideanSpace ℝ (Fin n))) ∩ {x | f x ≤ a} := by
        rw [← hCeq]
        exact hx
      have hxA : x ∈ A := hx'.1
      have hxle : f x ≤ a := hx'.2
      have hvdir' : t • (-v') ∈ A.direction := by
        simpa using (A.direction.smul_mem t (A.direction.neg_mem hvdir))
      have hxA' : (t • (-v')) +ᵥ x ∈ A :=
        AffineSubspace.vadd_mem_of_mem_direction (s := A) hvdir' hxA
      have hfx : f (x + t • (-v')) ≤ a := by
        calc
          f (x + t • (-v')) = f x + t * f (-v') := by
            simp [map_add, map_smul, smul_eq_mul]
          _ = f x := by simp [hvf]
          _ ≤ a := hxle
      have hxA'' : x + t • (-v') ∈ (A : Set (EuclideanSpace ℝ (Fin n))) := by
        simpa [vadd_eq_add, add_comm, add_left_comm, add_assoc] using hxA'
      have hxC : x + t • (-v') ∈ (e.symm '' C) := by
        have : x + t • (-v') ∈ (A : Set (EuclideanSpace ℝ (Fin n))) ∩ {x | f x ≤ a} := by
          exact ⟨hxA'', hfx⟩
        rw [hCeq]
        exact this
      exact hxC
    have hlin :
        ∃ y : EuclideanSpace ℝ (Fin n), y ≠ 0 ∧
          y ∈ (-Set.recessionCone (e.symm '' C)) ∩ Set.recessionCone (e.symm '' C) := by
      refine ⟨v', hvne', ?_⟩
      refine ⟨?_, hvrec⟩
      simpa [Set.mem_neg] using hvrec_neg
    exact hNoLinesE hlin

/-- Strong induction on finrank of the affine span direction to show `C ⊆ mixedConvexHull`. -/
lemma closedConvex_subset_mixedConvexHull_by_finrank_strongInduction {n : ℕ}
    {C : Set (Fin n → ℝ)} (hCclosed : IsClosed C) (hCconv : Convex ℝ C)
    (hNoLines : ¬ ∃ y : Fin n → ℝ, y ≠ 0 ∧
      y ∈ (-Set.recessionCone C) ∩ Set.recessionCone C)
    (hCne : C.Nonempty) :
    C ⊆
      mixedConvexHull (n := n) (C.extremePoints ℝ)
        {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d} := by
  classical
  let p : ℕ → Prop := fun m =>
    ∀ {C : Set (Fin n → ℝ)}, IsClosed C → Convex ℝ C →
      (¬ ∃ y : Fin n → ℝ, y ≠ 0 ∧
        y ∈ (-Set.recessionCone C) ∩ Set.recessionCone C) →
      C.Nonempty →
      Module.finrank ℝ (affineSpan ℝ C).direction = m →
        C ⊆ mixedConvexHull (n := n) (C.extremePoints ℝ)
          {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d}
  have hp : ∀ m, p m := by
    intro m
    refine Nat.strong_induction_on (p := p) m ?_
    intro m IH C hCclosed hCconv hNoLines hCne hfin
    cases m with
    | zero =>
        have hEq :=
          closedConvex_eq_mixedConvexHull_of_finrank_direction_eq_zero (n := n) (C := C) hCclosed
            hCconv hfin
        intro x hx
        have hx' : x ∈ C := hx
        rw [hEq] at hx'
        exact hx'
    | succ m' =>
        cases m' with
        | zero =>
            have hEq :=
              closedConvex_eq_mixedConvexHull_of_finrank_direction_eq_one (n := n) (C := C)
                hCclosed hCconv hNoLines hfin
            intro x hx
            have hx' : x ∈ C := hx
            rw [hEq] at hx'
            exact hx'
        | succ m'' =>
            intro x hxC
            have hfin_gt : 1 < Module.finrank ℝ (affineSpan ℝ C).direction := by
              have : 1 < Nat.succ (Nat.succ m'') := by
                exact Nat.succ_lt_succ (Nat.succ_pos m'')
              rw [hfin]
              exact this
            have hnot :=
              not_affine_or_closedHalf_of_noLines_finrank_gt_one (n := n) (C := C) hNoLines
                hfin_gt
            have hIH' :
                ∀ ⦃F : Set (Fin n → ℝ)⦄, IsClosed F → Convex ℝ F →
                  (¬ ∃ y : Fin n → ℝ, y ≠ 0 ∧
                    y ∈ (-Set.recessionCone F) ∩ Set.recessionCone F) →
                  Module.finrank ℝ (affineSpan ℝ F).direction <
                    Module.finrank ℝ (affineSpan ℝ C).direction →
                    F ⊆ mixedConvexHull (n := n) (F.extremePoints ℝ)
                      {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) F d} := by
              intro F hFclosed hFconv hNoLinesF hfinlt
              by_cases hFne : F.Nonempty
              ·
                have hfinF :
                    Module.finrank ℝ (affineSpan ℝ F).direction =
                      Module.finrank ℝ (affineSpan ℝ F).direction := rfl
                have hfinlt' :
                    Module.finrank ℝ (affineSpan ℝ F).direction < Nat.succ (Nat.succ m'') := by
                  simpa [hfin] using hfinlt
                exact (IH _ hfinlt') hFclosed hFconv hNoLinesF hFne hfinF
              ·
                intro y hy
                exact (hFne ⟨y, hy⟩).elim
            have hbdy :
                ∀ y ∈ euclideanRelativeBoundary_fin n C,
                  y ∈ mixedConvexHull (n := n) (C.extremePoints ℝ)
                    {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d} := by
              intro y hy
              exact
                mem_mixedConvexHull_of_mem_euclideanRelativeBoundary_under_IH (n := n) (C := C)
                  hCclosed hCconv hNoLines hIH' hy
            by_cases hxri : x ∈ euclideanRelativeInterior_fin n C
            ·
              exact
                mem_mixedConvexHull_of_mem_euclideanRelativeInterior_of_boundary_in_hull (n := n)
                  (C := C) hCclosed hCconv hnot.1 hnot.2 hbdy hxri
            ·
              have hxrb : x ∈ euclideanRelativeBoundary_fin n C := by
                have : x ∈ C \ euclideanRelativeInterior_fin n C := ⟨hxC, hxri⟩
                simpa [euclideanRelativeBoundary_fin_eq_diff_of_isClosed (hCclosed := hCclosed)] using
                  this
              exact hbdy x hxrb
  have hfin :
      Module.finrank ℝ (affineSpan ℝ C).direction =
        Module.finrank ℝ (affineSpan ℝ C).direction := rfl
  exact (hp _ hCclosed hCconv hNoLines hCne hfin)

/-- Theorem 18.5. Let `C` be a closed convex set containing no lines, and let `S` be the set of all
extreme points and extreme directions of `C`. Then `C = conv S`.

Here we formalize `conv S` as the mixed convex hull `mixedConvexHull S₀ S₁` (Definition 17.0.4),
with `S₀ = C.extremePoints ℝ` and `S₁ = {d | IsExtremeDirection (𝕜 := ℝ) C d}`. -/
theorem closedConvex_eq_mixedConvexHull_extremePoints_extremeDirections {n : ℕ}
    (C : Set (Fin n → ℝ)) (hCclosed : IsClosed C) (hCconv : Convex ℝ C)
    (hNoLines : ¬ ∃ y : Fin n → ℝ, y ≠ 0 ∧ y ∈ (-Set.recessionCone C) ∩ Set.recessionCone C) :
    C =
      mixedConvexHull (n := n) (C.extremePoints ℝ) {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d} := by
  classical
  refine Set.Subset.antisymm ?_ ?_
  ·
    classical
    by_cases hCne : C.Nonempty
    ·
      exact
        closedConvex_subset_mixedConvexHull_by_finrank_strongInduction (n := n) (C := C) hCclosed
          hCconv hNoLines hCne
    ·
      intro x hx
      exact (hCne ⟨x, hx⟩).elim
  ·
    refine
      mixedConvexHull_subset_of_convex_of_subset_of_recedes (n := n)
        (S₀ := C.extremePoints ℝ)
        (S₁ := {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d}) (Ccand := C) hCconv
        ?_ ?_
    · exact extremePoints_subset
    · intro d hd x hxC t ht
      have hdrec :
          d ∈ Set.recessionCone C :=
        mem_recessionCone_of_isExtremeDirection_fin (hCclosed := hCclosed) (by simpa using hd)
      exact hdrec hxC ht

/-- Regularity along all rays implies the boundedness condition used for mixed convex hulls. -/
lemma hRegular_to_hNoUnbounded_for_mixedConvexHull {n : ℕ} {S₀ S₁ : Set (Fin n → ℝ)}
    (hRegular :
      ∀ x d' : Fin n → ℝ,
        Bornology.IsBounded (S₀ ∩ ((fun t : ℝ => x + t • d') '' Set.Ici (0 : ℝ)))) :
    ∀ x d' : Fin n → ℝ,
      ((fun t : ℝ => x + t • d') '' Set.Ici (0 : ℝ)) ⊆ mixedConvexHull (n := n) S₀ S₁ →
        Bornology.IsBounded (S₀ ∩ ((fun t : ℝ => x + t • d') '' Set.Ici (0 : ℝ))) := by
  intro x d' _hsubset
  exact hRegular x d'

/-- Extreme points of a mixed convex hull lie in the point-generators. -/
lemma extremePoints_subset_S0_of_eq_mixedConvexHull {n : ℕ} {C S₀ S₁ : Set (Fin n → ℝ)}
    (hCgen : C = mixedConvexHull (n := n) S₀ S₁) :
    C.extremePoints ℝ ⊆ S₀ := by
  intro x hx
  have hxext : IsExtremePoint (𝕜 := ℝ) C x :=
    (isExtremePoint_iff_mem_extremePoints (𝕜 := ℝ) (C := C) (x := x)).mpr hx
  have hxext' : IsExtremePoint (𝕜 := ℝ) (mixedConvexHull (n := n) S₀ S₁) x := by
    simpa [hCgen] using hxext
  exact mem_points_of_isExtremePoint_mixedConvexHull (n := n) (S₀ := S₀) (S₁ := S₁) hxext'

/-- Text 18.5.1 (Minimality of Extreme Elements). Let `C` be a closed convex set containing no
lines. Let `S` be the set of all extreme points and extreme directions of `C`.

Suppose `S'` is another set of point-elements and direction-elements such that:

(1) `C` is fully generated by `S'`, i.e. `C = conv(S')` (here formalized as a mixed convex hull
`mixedConvexHull S₀ S₁`).

(2) (Regularity condition) No half-line in `ℝⁿ` contains an unbounded subset of the point-elements
of `S'` (here: the intersection of `S₀` with any ray is bounded).

Then `S ⊆ S'` (here: every extreme point belongs to `S₀`, and every extreme direction belongs to
`S₁`). -/
theorem extremePoints_subset_points_and_extremeDirections_subset_directions_of_eq_mixedConvexHull
    {n : ℕ} {C : Set (Fin n → ℝ)} (S₀ S₁ : Set (Fin n → ℝ))
    (hCgen : C = mixedConvexHull (n := n) S₀ S₁)
    (hRegular :
      ∀ x d' : Fin n → ℝ,
        Bornology.IsBounded (S₀ ∩ ((fun t : ℝ => x + t • d') '' Set.Ici (0 : ℝ)))) :
    C.extremePoints ℝ ⊆ S₀ ∧
      {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d} ⊆ rayNonneg n S₁ := by
  constructor
  · exact extremePoints_subset_S0_of_eq_mixedConvexHull (n := n) (C := C) (S₀ := S₀) (S₁ := S₁)
      hCgen
  ·
    intro d hd
    have hNoUnbounded :
        ∀ x d' : Fin n → ℝ,
          ((fun t : ℝ => x + t • d') '' Set.Ici (0 : ℝ)) ⊆ mixedConvexHull (n := n) S₀ S₁ →
            Bornology.IsBounded (S₀ ∩ ((fun t : ℝ => x + t • d') '' Set.Ici (0 : ℝ))) :=
      hRegular_to_hNoUnbounded_for_mixedConvexHull (n := n) (S₀ := S₀) (S₁ := S₁) hRegular
    have hd' : IsExtremeDirection (𝕜 := ℝ) (mixedConvexHull (n := n) S₀ S₁) d := by
      simpa [hCgen] using hd
    exact
      mem_directions_of_isExtremeDirection_mixedConvexHull (n := n) (S₀ := S₀) (S₁ := S₁)
        hNoUnbounded hd'

/-- Bounded closed convex sets have trivial recession cone in `Fin n → ℝ`. -/
lemma recessionCone_eq_singleton_zero_of_closed_bounded_convex_fin {n : ℕ}
    {C : Set (Fin n → ℝ)} (hCne : C.Nonempty) (hCclosed : IsClosed C) (hCconv : Convex ℝ C)
    (hCbdd : Bornology.IsBounded C) :
    Set.recessionCone C = ({0} : Set (Fin n → ℝ)) := by
  classical
  let e := euclideanEquiv n
  let C' : Set (EuclideanSpace ℝ (Fin n)) := e.symm '' C
  have hC'ne : C'.Nonempty := by
    rcases hCne with ⟨x, hx⟩
    exact ⟨e.symm x, ⟨x, hx, rfl⟩⟩
  have hC'closed : IsClosed C' := by
    exact (e.symm.toHomeomorph.isClosed_image).2 hCclosed
  have hC'conv : Convex ℝ C' := by
    simpa [C'] using hCconv.linear_image (e.symm.toLinearMap)
  have hC'bounded : Bornology.IsBounded C' := by
    simpa [C'] using (e.symm.lipschitz.isBounded_image hCbdd)
  have hrecC' :
      Set.recessionCone C' = ({0} : Set (EuclideanSpace ℝ (Fin n))) := by
    exact
      (bounded_iff_recessionCone_eq_singleton_zero (C := C') hC'ne hC'closed hC'conv).1
        hC'bounded
  have hEq : Set.recessionCone C = e '' Set.recessionCone C' := by
    have hEq' := recessionCone_image_linearEquiv (e := e.toLinearEquiv) (C := C')
    have himage : e '' C' = C := by
      ext x
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        simpa using hz
      · intro hx
        exact ⟨e.symm x, ⟨x, hx, rfl⟩, by simp⟩
    simpa [himage, C'] using hEq'
  have hzero : e '' ({0} : Set (EuclideanSpace ℝ (Fin n))) = ({0} : Set (Fin n → ℝ)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx0 : x = 0 := by simpa [Set.mem_singleton_iff] using hx
      simp [hx0]
    · intro hy
      have hy0 : y = 0 := by simpa [Set.mem_singleton_iff] using hy
      subst hy0
      exact ⟨0, by simp, by simp⟩
  calc
    Set.recessionCone C = e '' Set.recessionCone C' := hEq
    _ = e '' ({0} : Set (EuclideanSpace ℝ (Fin n))) := by simp [hrecC']
    _ = ({0} : Set (Fin n → ℝ)) := hzero

/-- If the recession cone is `{0}`, then `C` contains no lines. -/
lemma noLines_of_recessionCone_eq_singleton_zero {n : ℕ} {C : Set (Fin n → ℝ)}
    (hrec : Set.recessionCone C = ({0} : Set (Fin n → ℝ))) :
    ¬ ∃ y : Fin n → ℝ, y ≠ 0 ∧ y ∈ (-Set.recessionCone C) ∩ Set.recessionCone C := by
  intro hlin
  rcases hlin with ⟨y, hyne, hy⟩
  have hyrec : y ∈ Set.recessionCone C := hy.2
  have hy0 : y = 0 := by
    have : y ∈ ({0} : Set (Fin n → ℝ)) := by simpa [hrec] using hyrec
    simpa [Set.mem_singleton_iff] using this
  exact hyne hy0

/-- If the recession cone is `{0}`, then `C` has no extreme directions. -/
lemma extremeDirections_eq_empty_of_recessionCone_eq_singleton_zero {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCclosed : IsClosed C) (hrec : Set.recessionCone C = ({0} : Set (Fin n → ℝ))) :
    {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d} = (∅ : Set (Fin n → ℝ)) := by
  classical
  refine Set.eq_empty_iff_forall_notMem.2 ?_
  intro d hd
  have hdrec : d ∈ Set.recessionCone C :=
    mem_recessionCone_of_isExtremeDirection_fin (hCclosed := hCclosed) (by simpa using hd)
  have hd0 : d = 0 := by
    have : d ∈ ({0} : Set (Fin n → ℝ)) := by simpa [hrec] using hdrec
    simpa [Set.mem_singleton_iff] using this
  rcases hd with ⟨C', hhalf, hdir⟩
  rcases hdir with ⟨x0, hdne, hC'eq⟩
  exact hdne hd0

/-- Mixed convex hull with empty directions reduces to the usual convex hull. -/
lemma mixedConvexHull_empty_directions_eq_convexHull {n : ℕ} (S₀ : Set (Fin n → ℝ)) :
    mixedConvexHull (n := n) S₀ (∅ : Set (Fin n → ℝ)) = convexHull ℝ S₀ := by
  classical
  have hrepr :=
    mixedConvexHull_eq_conv_add_ray_eq_conv_add_cone (n := n) S₀ (∅ : Set (Fin n → ℝ))
  have hray : ray n (∅ : Set (Fin n → ℝ)) = ({0} : Set (Fin n → ℝ)) := by
    ext x
    constructor
    · intro hx
      have hx' : x = 0 ∨ x ∈ rayNonneg n (∅ : Set (Fin n → ℝ)) := by
        simpa [ray, Set.mem_insert_iff] using hx
      cases hx' with
      | inl hx0 =>
          simp [hx0]
      | inr hxray =>
          rcases hxray with ⟨d, hd, t, ht, rfl⟩
          exact hd.elim
    · intro hx
      have hx0 : x = 0 := by simpa [Set.mem_singleton_iff] using hx
      subst hx0
      exact (Set.mem_insert_iff).2 (Or.inl rfl)
  have hadd : S₀ + ({0} : Set (Fin n → ℝ)) = S₀ := by
    ext x
    constructor
    · intro hx
      rcases (Set.mem_add.mp hx) with ⟨a, ha, b, hb, rfl⟩
      have hb0 : b = 0 := by simpa [Set.mem_singleton_iff] using hb
      simpa [hb0] using ha
    · intro hx
      exact Set.mem_add.mpr ⟨x, hx, 0, by simp, by simp⟩
  calc
    mixedConvexHull (n := n) S₀ (∅ : Set (Fin n → ℝ)) =
        conv (S₀ + ray n (∅ : Set (Fin n → ℝ))) := hrepr.1
    _ = conv (S₀ + ({0} : Set (Fin n → ℝ))) := by simp [hray]
    _ = conv S₀ := by simp [hadd]
    _ = convexHull ℝ S₀ := by simp [conv]

end
end Section18
end Chap04
