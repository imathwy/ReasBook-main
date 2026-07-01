/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Changyu Zou, Yunxi Duan, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap04.section18_part5

open scoped Pointwise

set_option maxHeartbeats 400000

section Chap04
section Section18

variable {𝕜 E : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [SMul 𝕜 E]

/-- The line through two boundary points with a relative interior point on their open segment
has bounded intersection with `C`. -/
lemma isBounded_inter_line_of_rb_endpoints_with_ri_point {n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin n))} (hCclosed : IsClosed C) (hCconv : Convex ℝ C)
    {x₁ x₂ : EuclideanSpace ℝ (Fin n)}
    (hx₁rb : x₁ ∈ euclideanRelativeBoundary n C) (hx₂rb : x₂ ∈ euclideanRelativeBoundary n C)
    (hri :
      ∃ y : EuclideanSpace ℝ (Fin n),
        y ∈ euclideanRelativeInterior n C ∧ y ∈ openSegment ℝ x₁ x₂) :
    Bornology.IsBounded
      (((AffineSubspace.mk' x₁ (Submodule.span ℝ {x₂ - x₁}) :
          AffineSubspace ℝ (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n))) ∩ C) := by
  classical
  rcases hri with ⟨y, hyri, hyseg⟩
  rcases hyseg with ⟨a, b, ha, hb, hab, hy⟩
  have hb1 : b < 1 := by linarith [ha, hab]
  have ha' : a = 1 - b := by linarith [hab]
  set v : EuclideanSpace ℝ (Fin n) := x₂ - x₁
  have hx₁rb' : x₁ ∈ C ∧ x₁ ∉ euclideanRelativeInterior n C := by
    have : x₁ ∈ C \ euclideanRelativeInterior n C := by
      simpa [euclideanRelativeBoundary_eq_diff_of_isClosed (n := n) (C := C) hCclosed] using hx₁rb
    exact this
  have hx₂rb' : x₂ ∈ C ∧ x₂ ∉ euclideanRelativeInterior n C := by
    have : x₂ ∈ C \ euclideanRelativeInterior n C := by
      simpa [euclideanRelativeBoundary_eq_diff_of_isClosed (n := n) (C := C) hCclosed] using hx₂rb
    exact this
  have hyline : y = x₁ + b • v := by
    have hy' : y = AffineMap.lineMap x₁ x₂ b := by
      calc
        y = a • x₁ + b • x₂ := hy.symm
        _ = (1 - b) • x₁ + b • x₂ := by simp [ha']
        _ = AffineMap.lineMap x₁ x₂ b := by
              simp [AffineMap.lineMap_apply_module]
    simpa [AffineMap.lineMap_apply_module', v, add_comm] using hy'
  have hsubset :
      ((AffineSubspace.mk' x₁ (Submodule.span ℝ {x₂ - x₁}) :
          AffineSubspace ℝ (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n))) ∩ C ⊆
        segment ℝ x₁ x₂ := by
    intro z hz
    rcases hz with ⟨hzM, hzC⟩
    have hzM' : z -ᵥ x₁ ∈ Submodule.span ℝ {v} := by
      simpa [AffineSubspace.mem_mk', v] using hzM
    rcases (Submodule.mem_span_singleton).1 hzM' with ⟨s, hs⟩
    have hzline : z = x₁ + s • v := by
      have hz' : z - x₁ = s • v := by
        simpa [vsub_eq_sub] using hs.symm
      have hz'' : z = s • v + x₁ := (sub_eq_iff_eq_add).1 hz'
      simpa [add_comm] using hz''
    have hcomb (t : ℝ) :
        (1 - t) • y + t • z =
          ((1 - t) + t) • x₁ + ((1 - t) * b + t * s) • v := by
      calc
        (1 - t) • y + t • z
            = (1 - t) • (x₁ + b • v) + t • (x₁ + s • v) := by
                simp [hyline, hzline]
        _ =
            ((1 - t) • x₁ + (1 - t) • (b • v)) + (t • x₁ + t • (s • v)) := by
              simp [smul_add, add_assoc, add_left_comm, add_comm]
        _ =
            ((1 - t) • x₁ + t • x₁) + ((1 - t) • (b • v) + t • (s • v)) := by
              abel
        _ =
            ((1 - t) + t) • x₁ + ((1 - t) * b + t * s) • v := by
              have hx1 : (1 - t) • x₁ + t • x₁ = ((1 - t) + t) • x₁ := by
                simpa [add_smul] using (add_smul (1 - t) t x₁).symm
              have hv :
                  (1 - t) • (b • v) + t • (s • v) =
                    ((1 - t) * b + t * s) • v := by
                calc
                  (1 - t) • (b • v) + t • (s • v)
                      = ((1 - t) * b) • v + (t * s) • v := by
                          simp [smul_smul]
                  _ = ((1 - t) * b + t * s) • v := by
                          simpa [add_smul] using
                            (add_smul ((1 - t) * b) (t * s) v).symm
              simp [hx1, hv]
    have hcomb' (t : ℝ) :
        (1 - t) • y + t • z = x₁ + ((1 - t) * b + t * s) • v := by
      have h1 : (1 - t) + t = 1 := by
        simpa using (sub_add_cancel 1 t)
      simpa [h1] using hcomb t
    have hs0 : 0 ≤ s := by
      by_contra hs0
      have hs0' : s < 0 := lt_of_not_ge hs0
      have hdenpos : 0 < b - s := by linarith [hb, hs0']
      have hden : b - s ≠ 0 := by linarith [hb, hs0']
      set t : ℝ := b / (b - s)
      have ht0 : 0 ≤ t := by
        exact div_nonneg (le_of_lt hb) (le_of_lt hdenpos)
      have ht1 : t < 1 := by
        have h : b < 1 * (b - s) := by linarith [hs0']
        have ht' : b / (b - s) < 1 := (div_lt_iff₀ hdenpos).2 (by simpa using h)
        simpa [t] using ht'
      have hcoef : (1 - t) * b + t * s = 0 := by
        dsimp [t]
        field_simp [hden]
        ring
      have hx1eq : (1 - t) • y + t • z = x₁ := by
        simpa [hcoef] using hcomb' t
      have hzcl : z ∈ closure C := subset_closure hzC
      have hx1ri :
          x₁ ∈ euclideanRelativeInterior n C := by
        have hri' :
            (1 - t) • y + t • z ∈ euclideanRelativeInterior n C :=
          euclideanRelativeInterior_convex_combination_mem (n := n) C hCconv y z hyri hzcl t ht0 ht1
        simpa [hx1eq] using hri'
      exact (hx₁rb'.2 hx1ri).elim
    have hs1 : s ≤ 1 := by
      by_contra hs1
      have hs1' : 1 < s := lt_of_not_ge hs1
      have hdenpos : 0 < s - b := by linarith [hb1, hs1']
      have hden : s - b ≠ 0 := by linarith [hb1, hs1']
      set t : ℝ := (1 - b) / (s - b)
      have ht0 : 0 ≤ t := by
        have : 0 ≤ 1 - b := by linarith [hb1]
        exact div_nonneg this (le_of_lt hdenpos)
      have ht1 : t < 1 := by
        have h : 1 - b < 1 * (s - b) := by linarith [hs1']
        have ht' : (1 - b) / (s - b) < 1 := (div_lt_iff₀ hdenpos).2 (by simpa using h)
        simpa [t] using ht'
      have hcoef : (1 - t) * b + t * s = 1 := by
        dsimp [t]
        field_simp [hden]
        ring
      have hx1v : x₁ + v = x₂ := by
        simpa [v, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          (add_sub_cancel_left x₁ x₂)
      have hx2eq : (1 - t) • y + t • z = x₂ := by
        have htmp : (1 - t) • y + t • z = x₁ + (1 : ℝ) • v := by
          simpa [hcoef] using hcomb' t
        simpa [hx1v] using htmp
      have hzcl : z ∈ closure C := subset_closure hzC
      have hx2ri :
          x₂ ∈ euclideanRelativeInterior n C := by
        have hri' :
            (1 - t) • y + t • z ∈ euclideanRelativeInterior n C :=
          euclideanRelativeInterior_convex_combination_mem (n := n) C hCconv y z hyri hzcl t ht0 ht1
        simpa [hx2eq] using hri'
      exact (hx₂rb'.2 hx2ri).elim
    have hzlineMap : z = AffineMap.lineMap x₁ x₂ s := by
      have hz' : z = s • v + x₁ := by simpa [add_comm] using hzline
      simpa [AffineMap.lineMap_apply_module', v] using hz'
    refine ⟨1 - s, s, ?_, ?_, ?_, ?_⟩
    · linarith [hs1]
    · exact hs0
    · linarith
    · have : AffineMap.lineMap x₁ x₂ s = z := hzlineMap.symm
      simpa [AffineMap.lineMap_apply_module] using this
  exact (isBounded_segment (n := n) x₁ x₂).subset hsubset

/-- A bounded line-slice parallel to `M` through a relative interior point yields boundary
endpoints whose segment contains that point. -/
lemma exists_rb_endpoints_for_bounded_parallel_line_slice_through_ri {n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin n))} (hCclosed : IsClosed C) (hCconv : Convex ℝ C)
    (M : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)))
    (hMbdd :
      Bornology.IsBounded ((M : Set (EuclideanSpace ℝ (Fin n))) ∩ C))
    (hMne : ((M : Set (EuclideanSpace ℝ (Fin n))) ∩ C).Nonempty)
    (hv :
      ∃ v : EuclideanSpace ℝ (Fin n),
        v ≠ 0 ∧ v ∈ M.direction ∧ v ∈ (affineSpan ℝ C).direction) :
    ∀ ⦃x : EuclideanSpace ℝ (Fin n)⦄,
      x ∈ euclideanRelativeInterior n C →
        ∃ y z : EuclideanSpace ℝ (Fin n),
          y ∈ euclideanRelativeBoundary n C ∧ z ∈ euclideanRelativeBoundary n C ∧
            x ∈ segment ℝ y z := by
  classical
  intro x hxri
  rcases hv with ⟨v, hv0, hvM, hvA⟩
  let Mx : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)) := AffineSubspace.mk' x M.direction
  have hMx_bdd :
      Bornology.IsBounded ((Mx : Set (EuclideanSpace ℝ (Fin n))) ∩ C) := by
    have hdir : Mx.direction = M.direction := by
      simp [Mx]
    exact
      bounded_inter_of_parallel_affine (n := n) (C := C) hCclosed hCconv M hMne hMbdd Mx hdir
  let Lx : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)) :=
    AffineSubspace.mk' x (Submodule.span ℝ ({v} : Set (EuclideanSpace ℝ (Fin n))))
  have hLx_subset : (Lx : Set (EuclideanSpace ℝ (Fin n))) ⊆ (Mx : Set (EuclideanSpace ℝ (Fin n))) := by
    intro y hy
    have hy' : y -ᵥ x ∈ Submodule.span ℝ ({v} : Set (EuclideanSpace ℝ (Fin n))) := by
      simpa [Lx] using hy
    have hspan_le :
        Submodule.span ℝ ({v} : Set (EuclideanSpace ℝ (Fin n))) ≤ M.direction := by
      intro w hw
      rcases (Submodule.mem_span_singleton).1 hw with ⟨r, rfl⟩
      exact M.direction.smul_mem r hvM
    have : y -ᵥ x ∈ M.direction := hspan_le hy'
    simpa [Mx] using this
  have hLx_bdd :
      Bornology.IsBounded ((Lx : Set (EuclideanSpace ℝ (Fin n))) ∩ C) := by
    refine hMx_bdd.subset ?_
    intro y hy
    exact ⟨hLx_subset hy.1, hy.2⟩
  have hxC : x ∈ C := by
    exact (euclideanRelativeInterior_subset_closure n C).1 hxri
  have hxLx : x ∈ (Lx : Set (EuclideanSpace ℝ (Fin n))) := by
    simp [Lx]
  let K : Set (EuclideanSpace ℝ (Fin n)) := (Lx : Set (EuclideanSpace ℝ (Fin n))) ∩ C
  have hKne : K.Nonempty := ⟨x, ⟨hxLx, hxC⟩⟩
  have hKclosed : IsClosed K := by
    have hLxclosed : IsClosed (Lx : Set (EuclideanSpace ℝ (Fin n))) := by
      simpa using (AffineSubspace.closed_of_finiteDimensional (s := Lx))
    exact hLxclosed.inter hCclosed
  have hKcompact : IsCompact K := (Metric.isCompact_iff_isClosed_bounded).2 ⟨hKclosed, hLx_bdd⟩
  let f : EuclideanSpace ℝ (Fin n) → ℝ := fun p => inner ℝ p v
  have hfcont : Continuous f := by
    have h1 : Continuous (fun p : EuclideanSpace ℝ (Fin n) => p) := continuous_id
    have h2 : Continuous (fun _ : EuclideanSpace ℝ (Fin n) => v) := continuous_const
    simpa [f] using (Continuous.inner h1 h2)
  have hfcontOn : ContinuousOn f K := hfcont.continuousOn
  obtain ⟨y, hyK, hymin⟩ := hKcompact.exists_isMinOn hKne hfcontOn
  obtain ⟨z, hzK, hzmax⟩ := hKcompact.exists_isMaxOn hKne hfcontOn
  have hyLx : y ∈ (Lx : Set (EuclideanSpace ℝ (Fin n))) := hyK.1
  have hzLx : z ∈ (Lx : Set (EuclideanSpace ℝ (Fin n))) := hzK.1
  rcases (Submodule.mem_span_singleton).1 (by simpa [Lx] using hyLx) with ⟨ty, hty⟩
  rcases (Submodule.mem_span_singleton).1 (by simpa [Lx] using hzLx) with ⟨tz, htz⟩
  have hy_eq : y = x + ty • v := by
    have : y - x = ty • v := by
      simpa [vsub_eq_sub] using hty.symm
    have : y = ty • v + x := (sub_eq_iff_eq_add).1 this
    simpa [add_comm] using this
  have hz_eq : z = x + tz • v := by
    have : z - x = tz • v := by
      simpa [vsub_eq_sub] using htz.symm
    have : z = tz • v + x := (sub_eq_iff_eq_add).1 this
    simpa [add_comm] using this
  have hvinner : 0 < inner ℝ v v := by
    have hnonneg : 0 ≤ inner ℝ v v := by
      have : 0 ≤ ‖v‖ ^ 2 := by nlinarith
      simpa [real_inner_self_eq_norm_sq] using this
    have hneq : inner ℝ v v ≠ 0 := by
      intro h
      apply hv0
      exact (inner_self_eq_zero).1 h
    exact lt_of_le_of_ne hnonneg (Ne.symm hneq)
  have hxK : x ∈ K := ⟨hxLx, hxC⟩
  have hymin' : ∀ p ∈ K, f y ≤ f p := (isMinOn_iff).1 hymin
  have hzmax' : ∀ p ∈ K, f p ≤ f z := (isMaxOn_iff).1 hzmax
  have hy_le : f y ≤ f x := hymin' x hxK
  have hz_ge : f x ≤ f z := hzmax' x hxK
  have hfy : f y = f x + ty * inner ℝ v v := by
    simp [f, hy_eq, inner_add_left, inner_smul_left, inner_smul_right, mul_comm, mul_left_comm,
      mul_assoc, add_comm, add_left_comm, add_assoc]
  have hfz : f z = f x + tz * inner ℝ v v := by
    simp [f, hz_eq, inner_add_left, inner_smul_left, inner_smul_right, mul_comm, mul_left_comm,
      mul_assoc, add_comm, add_left_comm, add_assoc]
  have hty_le : ty ≤ 0 := by
    nlinarith [hy_le, hfy, hvinner]
  have htz_ge : 0 ≤ tz := by
    nlinarith [hz_ge, hfz, hvinner]
  rcases
      exists_add_sub_mem_of_mem_ri_of_mem_direction (n := n) (C := C)
        (x := x) (v := v) hxri hvA with ⟨ε, hεpos, hxplus, hxminus⟩
  have hxplusLx : x + ε • v ∈ (Lx : Set (EuclideanSpace ℝ (Fin n))) := by
    have hdir : ε • v ∈ Lx.direction := by
      have : ε • v ∈ Submodule.span ℝ ({v} : Set (EuclideanSpace ℝ (Fin n))) :=
        (Submodule.span ℝ ({v} : Set (EuclideanSpace ℝ (Fin n)))).smul_mem ε
          (Submodule.subset_span (by simp))
      simpa [Lx] using this
    have hx' : (ε • v) +ᵥ x ∈ Lx :=
      AffineSubspace.vadd_mem_of_mem_direction (s := Lx) hdir hxLx
    simpa [vadd_eq_add, add_comm] using hx'
  have hxminusLx : x - ε • v ∈ (Lx : Set (EuclideanSpace ℝ (Fin n))) := by
    have hdir : (-ε) • v ∈ Lx.direction := by
      have : (-ε) • v ∈ Submodule.span ℝ ({v} : Set (EuclideanSpace ℝ (Fin n))) :=
        (Submodule.span ℝ ({v} : Set (EuclideanSpace ℝ (Fin n)))).smul_mem (-ε)
          (Submodule.subset_span (by simp))
      simpa [Lx] using this
    have hx' : (-ε) • v +ᵥ x ∈ Lx :=
      AffineSubspace.vadd_mem_of_mem_direction (s := Lx) hdir hxLx
    simpa [vadd_eq_add, add_comm, sub_eq_add_neg] using hx'
  have hxplusK : x + ε • v ∈ K := ⟨hxplusLx, hxplus⟩
  have hxminusK : x - ε • v ∈ K := ⟨hxminusLx, hxminus⟩
  have hty_lt : ty < 0 := by
    have hmin' : f y ≤ f (x - ε • v) := hymin' (x - ε • v) hxminusK
    have hfxminus : f (x - ε • v) = f x - ε * inner ℝ v v := by
      simp [f, inner_add_left, inner_smul_left, inner_smul_right, mul_comm, mul_left_comm,
        mul_assoc, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
    nlinarith [hmin', hfy, hfxminus, hvinner, hεpos]
  have htz_gt : 0 < tz := by
    have hmax' : f (x + ε • v) ≤ f z := hzmax' (x + ε • v) hxplusK
    have hfxplus : f (x + ε • v) = f x + ε * inner ℝ v v := by
      simp [f, inner_add_left, inner_smul_left, inner_smul_right, mul_comm, mul_left_comm,
        mul_assoc, add_comm, add_left_comm, add_assoc]
    nlinarith [hmax', hfz, hfxplus, hvinner, hεpos]
  set lam : ℝ := (-ty) / (tz - ty)
  have hden : 0 < tz - ty := by linarith [hty_lt, htz_gt]
  have hlam0 : 0 ≤ lam := by
    have : 0 ≤ -ty := by linarith [hty_le]
    exact div_nonneg this (le_of_lt hden)
  have hlam1 : lam ≤ 1 := by
    have h : -ty ≤ (1 : ℝ) * (tz - ty) := by linarith [htz_ge]
    have h' : (-ty) / (tz - ty) ≤ (1 : ℝ) := (div_le_iff₀ hden).2 (by simpa using h)
    simpa [lam] using h'
  have hcoeff : (1 - lam) * ty + lam * tz = 0 := by
    have hden_ne : tz - ty ≠ 0 := by linarith [hty_lt, htz_gt]
    have hlam : lam * (tz - ty) = -ty := by
      dsimp [lam]
      field_simp [hden_ne]
    calc
      (1 - lam) * ty + lam * tz = ty + lam * (tz - ty) := by ring
      _ = ty + (-ty) := by simp [hlam]
      _ = 0 := by ring
  have hxseg : x ∈ segment ℝ y z := by
    refine ⟨1 - lam, lam, ?_, ?_, ?_, ?_⟩
    · linarith [hlam1]
    · exact hlam0
    · linarith
    ·
      have hxeq : (1 - lam) • y + lam • z = x + ((1 - lam) * ty + lam * tz) • v := by
        calc
          (1 - lam) • y + lam • z
              = (1 - lam) • (x + ty • v) + lam • (x + tz • v) := by
                  simp [hy_eq, hz_eq]
          _ =
              ((1 - lam) • x + (1 - lam) • (ty • v)) +
                (lam • x + lam • (tz • v)) := by
                  simp [smul_add, add_assoc, add_left_comm, add_comm]
          _ =
              ((1 - lam) • x + lam • x) +
                ((1 - lam) • (ty • v) + lam • (tz • v)) := by
                  abel
          _ = ((1 - lam + lam) • x) + (((1 - lam) * ty + lam * tz) • v) := by
                have hx :
                    (1 - lam) • x + lam • x = (1 - lam + lam) • x := by
                  simpa [add_smul] using (add_smul (1 - lam) lam x).symm
                have hv :
                    (1 - lam) • (ty • v) + lam • (tz • v) =
                      ((1 - lam) * ty + lam * tz) • v := by
                  calc
                    (1 - lam) • (ty • v) + lam • (tz • v)
                        = ((1 - lam) * ty) • v + (lam * tz) • v := by
                            simp [smul_smul, mul_comm, mul_left_comm, mul_assoc]
                    _ = ((1 - lam) * ty + lam * tz) • v := by
                            simpa [add_smul] using
                              (add_smul ((1 - lam) * ty) (lam * tz) v).symm
                simpa [hx, hv]
          _ = x + ((1 - lam) * ty + lam * tz) • v := by
                simp
      calc
        (1 - lam) • y + lam • z
            = x + ((1 - lam) * ty + lam * tz) • v := hxeq
        _ = x := by
            simpa [hcoeff]
  have hyC : y ∈ C := hyK.2
  have hzC : z ∈ C := hzK.2
  have hy_not_ri : y ∉ euclideanRelativeInterior n C := by
    intro hyri
    rcases
        exists_add_sub_mem_of_mem_ri_of_mem_direction (n := n) (C := C)
          (x := y) (v := v) hyri hvA with ⟨ε', hε'pos, hyplus, hyminus⟩
    have hyminusLx : y - ε' • v ∈ (Lx : Set (EuclideanSpace ℝ (Fin n))) := by
      have hdir : (-ε') • v ∈ Lx.direction := by
        have : (-ε') • v ∈ Submodule.span ℝ ({v} : Set (EuclideanSpace ℝ (Fin n))) :=
          (Submodule.span ℝ ({v} : Set (EuclideanSpace ℝ (Fin n)))).smul_mem (-ε')
            (Submodule.subset_span (by simp))
        simpa [Lx] using this
      have hy' : (-ε') • v +ᵥ y ∈ Lx :=
        AffineSubspace.vadd_mem_of_mem_direction (s := Lx) hdir hyLx
      simpa [vadd_eq_add, add_comm, sub_eq_add_neg] using hy'
    have hyminusK : y - ε' • v ∈ K := ⟨hyminusLx, hyminus⟩
    have hmin' : f y ≤ f (y - ε' • v) := hymin' (y - ε' • v) hyminusK
    have hfyminus : f (y - ε' • v) = f y - ε' * inner ℝ v v := by
      simp [f, inner_add_left, inner_smul_left, inner_smul_right, mul_comm, mul_left_comm,
        mul_assoc, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
    nlinarith [hmin', hfyminus, hvinner, hε'pos]
  have hz_not_ri : z ∉ euclideanRelativeInterior n C := by
    intro hzri
    rcases
        exists_add_sub_mem_of_mem_ri_of_mem_direction (n := n) (C := C)
          (x := z) (v := v) hzri hvA with ⟨ε', hε'pos, hzplus, hzminus⟩
    have hzplusLx : z + ε' • v ∈ (Lx : Set (EuclideanSpace ℝ (Fin n))) := by
      have hdir : ε' • v ∈ Lx.direction := by
        have : ε' • v ∈ Submodule.span ℝ ({v} : Set (EuclideanSpace ℝ (Fin n))) :=
          (Submodule.span ℝ ({v} : Set (EuclideanSpace ℝ (Fin n)))).smul_mem ε'
            (Submodule.subset_span (by simp))
        simpa [Lx] using this
      have hz' : ε' • v +ᵥ z ∈ Lx :=
        AffineSubspace.vadd_mem_of_mem_direction (s := Lx) hdir hzLx
      simpa [vadd_eq_add, add_comm] using hz'
    have hzplusK : z + ε' • v ∈ K := ⟨hzplusLx, hzplus⟩
    have hmax' : f (z + ε' • v) ≤ f z := hzmax' (z + ε' • v) hzplusK
    have hfzplus : f (z + ε' • v) = f z + ε' * inner ℝ v v := by
      simp [f, inner_add_left, inner_smul_left, inner_smul_right, mul_comm, mul_left_comm,
        mul_assoc, add_comm, add_left_comm, add_assoc]
    nlinarith [hmax', hfzplus, hvinner, hε'pos]
  have hyrb : y ∈ euclideanRelativeBoundary n C := by
    have : y ∈ C \ euclideanRelativeInterior n C := ⟨hyC, hy_not_ri⟩
    simpa [euclideanRelativeBoundary_eq_diff_of_isClosed (n := n) (C := C) hCclosed] using this
  have hzrb : z ∈ euclideanRelativeBoundary n C := by
    have : z ∈ C \ euclideanRelativeInterior n C := ⟨hzC, hz_not_ri⟩
    simpa [euclideanRelativeBoundary_eq_diff_of_isClosed (n := n) (C := C) hCclosed] using this
  exact ⟨y, z, hyrb, hzrb, hxseg⟩

/-- Theorem 18.4. Let `C` be a closed convex set which is neither an affine set nor a closed half
of an affine set. Then every relative interior point of `C` lies on a line segment `segment ℝ y z`
joining two relative boundary points `y, z ∈ rb C` (here `ri C`/`rb C` are formalized as
`euclideanRelativeInterior`/`euclideanRelativeBoundary`). -/
theorem exists_mem_segment_of_mem_euclideanRelativeInterior
    {n : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))} (hCclosed : IsClosed C) (hCconv : Convex ℝ C)
    (hC_not_affine :
      ¬ ∃ A : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)), (A : Set (EuclideanSpace ℝ (Fin n))) = C)
    (hC_not_closedHalf_affine :
      ¬ ∃ (A : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)))
          (f : (EuclideanSpace ℝ (Fin n)) →ₗ[ℝ] ℝ) (a : ℝ),
          f ≠ 0 ∧ C = (A : Set (EuclideanSpace ℝ (Fin n))) ∩ {x | f x ≤ a}) :
    ∀ ⦃x : EuclideanSpace ℝ (Fin n)⦄,
      x ∈ euclideanRelativeInterior n C →
        ∃ y z : EuclideanSpace ℝ (Fin n),
          y ∈ euclideanRelativeBoundary n C ∧ z ∈ euclideanRelativeBoundary n C ∧ x ∈ segment ℝ y z := by
  intro x hxri
  have hCne : C.Nonempty := by
    exact ⟨x, (euclideanRelativeInterior_subset_closure n C).1 hxri⟩
  have hnotconv :
      ¬ Convex ℝ (euclideanRelativeBoundary n C) :=
    not_convex_euclideanRelativeBoundary_of_not_affine_not_closedHalf (n := n) (C := C)
      hCclosed hCconv hCne hC_not_affine hC_not_closedHalf_affine
  obtain ⟨x₁, x₂, hx₁rb, hx₂rb, hx₁x₂, y, hyri, hyseg⟩ :=
    exists_two_rb_points_with_ri_point_on_openSegment (n := n) (C := C) hCclosed hCconv hnotconv
  let M : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)) :=
    AffineSubspace.mk' x₁ (Submodule.span ℝ {x₂ - x₁})
  have hMbdd :
      Bornology.IsBounded ((M : Set (EuclideanSpace ℝ (Fin n))) ∩ C) := by
    exact
      isBounded_inter_line_of_rb_endpoints_with_ri_point (n := n) (C := C) hCclosed hCconv
        hx₁rb hx₂rb ⟨y, hyri, hyseg⟩
  have hx₁C : x₁ ∈ C := by
    have : x₁ ∈ C \ euclideanRelativeInterior n C := by
      simpa [euclideanRelativeBoundary_eq_diff_of_isClosed (n := n) (C := C) hCclosed] using hx₁rb
    exact this.1
  have hx₂C : x₂ ∈ C := by
    have : x₂ ∈ C \ euclideanRelativeInterior n C := by
      simpa [euclideanRelativeBoundary_eq_diff_of_isClosed (n := n) (C := C) hCclosed] using hx₂rb
    exact this.1
  have hMne : ((M : Set (EuclideanSpace ℝ (Fin n))) ∩ C).Nonempty := by
    have hx₁M : x₁ ∈ (M : Set (EuclideanSpace ℝ (Fin n))) := by
      simp [M]
    exact ⟨x₁, hx₁M, hx₁C⟩
  have hv :
      ∃ v : EuclideanSpace ℝ (Fin n),
        v ≠ 0 ∧ v ∈ M.direction ∧ v ∈ (affineSpan ℝ C).direction := by
    refine ⟨x₂ - x₁, ?_, ?_, ?_⟩
    · intro hzero
      apply hx₁x₂
      exact (sub_eq_zero.mp hzero).symm
    ·
      have : x₂ - x₁ ∈ Submodule.span ℝ ({x₂ - x₁} : Set (EuclideanSpace ℝ (Fin n))) :=
        Submodule.subset_span (by simp)
      simpa [M] using this
    ·
      have hx₁A : x₁ ∈ affineSpan ℝ C := (subset_affineSpan (k := ℝ) (s := C)) hx₁C
      have hx₂A : x₂ ∈ affineSpan ℝ C := (subset_affineSpan (k := ℝ) (s := C)) hx₂C
      have hvsub : x₂ -ᵥ x₁ ∈ (affineSpan ℝ C).direction :=
        (affineSpan ℝ C).vsub_mem_direction hx₂A hx₁A
      simpa [vsub_eq_sub] using hvsub
  exact
    exists_rb_endpoints_for_bounded_parallel_line_slice_through_ri (n := n) (C := C)
      hCclosed hCconv M hMbdd hMne hv hxri

end Section18
end Chap04
