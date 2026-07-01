/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Changyu Zou, Yunxi Duan, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap04.section18_part1

open scoped Pointwise

section Chap04
section Section18

variable {𝕜 E : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [SMul 𝕜 E]

/-- Text 18.0.14 (exposed directions). If `d` is an exposed direction of a closed convex set `C`,
then `d` is an exposed direction of the recession cone `0⁺ C` (formalized as `Set.recessionCone C`). -/
theorem isExposedDirection_recessionCone_of_isExposedDirection {n : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin n))) (hCclosed : IsClosed C)
    {d : EuclideanSpace ℝ (Fin n)} (hd : IsExposedDirection C d) :
    IsExposedDirection (Set.recessionCone C) d := by
  classical
  rcases hd with ⟨C', hhalf, hdir⟩
  rcases hhalf with ⟨hhalf, hExp⟩
  rcases hExp with ⟨hCconv, hC'subset, ⟨h, hC'Eq⟩⟩
  have hExp' : IsExposedFace (C := C) C' := ⟨hCconv, hC'subset, ⟨h, hC'Eq⟩⟩
  rcases hdir with ⟨y0, hdne, hC'Eqdir⟩
  have hdir' : IsDirectionOf (𝕜 := ℝ) C' d := ⟨y0, hdne, hC'Eqdir⟩
  have hy0C' : y0 ∈ C' := by
    have : y0 + (0 : ℝ) • d ∈ (fun t : ℝ => y0 + t • d) '' Set.Ici (0 : ℝ) :=
      ⟨0, by simp, by simp⟩
    simpa [hC'Eqdir] using this
  have hy0C : y0 ∈ C := hC'subset hy0C'
  have hy0max : IsMaxOn (fun x => h x) C y0 := by
    have : y0 ∈ maximizers C h := by simpa [hC'Eq] using hy0C'
    exact this.2
  have hnonpos : ∀ u ∈ Set.recessionCone C, h u ≤ 0 := by
    intro u hu
    have hy0uC : y0 + u ∈ C := by
      have := hu hy0C (t := (1 : ℝ)) (by exact zero_le_one)
      simpa using this
    have hy0max' : ∀ y ∈ C, h y ≤ h y0 := (isMaxOn_iff).1 hy0max
    have hle : h (y0 + u) ≤ h y0 := hy0max' (y0 + u) hy0uC
    have hmap : h (y0 + u) = h y0 + h u := h.map_add y0 u
    linarith [hle, hmap]
  have hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ Set.recessionCone C := by
    intro x hx t ht
    simpa using hx
  have hmax_eq :
      maximizers (Set.recessionCone C) h =
        {u : EuclideanSpace ℝ (Fin n) | u ∈ Set.recessionCone C ∧ h u = 0} := by
    ext u; constructor
    · intro hu
      rcases hu with ⟨hu_rc, hu_max⟩
      have hu_max' : ∀ v ∈ Set.recessionCone C, h v ≤ h u := (isMaxOn_iff).1 hu_max
      have h0_le : h 0 ≤ h u := hu_max' 0 hzero
      have hu_le : h u ≤ 0 := hnonpos u hu_rc
      have h0 : h (0 : EuclideanSpace ℝ (Fin n)) = 0 := h.map_zero
      have hu_eq : h u = 0 := by linarith [h0_le, hu_le, h0]
      exact ⟨hu_rc, hu_eq⟩
    · intro hu
      rcases hu with ⟨hu_rc, hu_eq⟩
      have hu_max' : ∀ v ∈ Set.recessionCone C, h v ≤ h u := by
        intro v hv
        have hv_le : h v ≤ 0 := hnonpos v hv
        linarith [hv_le, hu_eq]
      exact ⟨hu_rc, (isMaxOn_iff).2 hu_max'⟩
  have hdext : IsExtremeDirection (𝕜 := ℝ) C d :=
    isExtremeDirection_of_isExposedDirection (C := C) ⟨C', ⟨hhalf, hExp'⟩, hdir'⟩
  have hdrec : d ∈ Set.recessionCone C :=
    mem_recessionCone_of_isExtremeDirection (hCclosed := hCclosed) hdext
  have hy0dC' : y0 + d ∈ C' := by
    have : y0 + (1 : ℝ) • d ∈ (fun t : ℝ => y0 + t • d) '' Set.Ici (0 : ℝ) :=
      ⟨1, by simp, by simp⟩
    simpa [hC'Eqdir] using this
  have hy0dC : y0 + d ∈ C := hC'subset hy0dC'
  have hy0dmax : IsMaxOn (fun x => h x) C (y0 + d) := by
    have : y0 + d ∈ maximizers C h := by simpa [hC'Eq] using hy0dC'
    exact this.2
  have hy0_le : h y0 ≤ h (y0 + d) := (isMaxOn_iff).1 hy0dmax y0 hy0C
  have hy0d_le : h (y0 + d) ≤ h y0 := (isMaxOn_iff).1 hy0max (y0 + d) hy0dC
  have hy0d_eq : h (y0 + d) = h y0 := le_antisymm hy0d_le hy0_le
  have hd0 : h d = 0 := by
    have hmap : h (y0 + d) = h y0 + h d := h.map_add y0 d
    linarith [hmap, hy0d_eq]
  have hRay :
      {u : EuclideanSpace ℝ (Fin n) | u ∈ Set.recessionCone C ∧ h u = 0} =
        (fun t : ℝ => t • d) '' Set.Ici (0 : ℝ) := by
    ext u
    constructor
    · rintro ⟨hu_rc, hu_eq⟩
      have hy0uC : y0 + u ∈ C := by
        have := hu_rc hy0C (t := (1 : ℝ)) (by exact zero_le_one)
        simpa using this
      have hy0max' : ∀ y ∈ C, h y ≤ h y0 := (isMaxOn_iff).1 hy0max
      have hy0u_max : IsMaxOn (fun x => h x) C (y0 + u) := by
        have hy0u_ineq : ∀ y ∈ C, h y ≤ h (y0 + u) := by
          intro y hyC
          have hy_le : h y ≤ h y0 := hy0max' y hyC
          have hmap : h (y0 + u) = h y0 + h u := h.map_add y0 u
          linarith [hy_le, hmap, hu_eq]
        exact (isMaxOn_iff).2 hy0u_ineq
      have hy0uC' : y0 + u ∈ C' := by
        have : y0 + u ∈ maximizers C h := ⟨hy0uC, hy0u_max⟩
        simpa [hC'Eq] using this
      rcases (by simpa [hC'Eqdir] using hy0uC') with ⟨t, ht, ht_eq⟩
      exact ⟨t, ht, ht_eq⟩
    · rintro ⟨t, ht, rfl⟩
      refine ⟨smul_mem_recessionCone_of_mem hdrec ht, ?_⟩
      have hmap : h (t • d) = t • h d := h.map_smulₛₗ t d
      calc
        h (t • d) = t • h d := hmap
        _ = 0 := by simp [hd0]
  have hEqRay : maximizers (Set.recessionCone C) h = (fun t : ℝ => t • d) '' Set.Ici (0 : ℝ) := by
    simpa [hmax_eq] using hRay
  let R : Set (EuclideanSpace ℝ (Fin n)) := (fun t : ℝ => t • d) '' Set.Ici (0 : ℝ)
  have hdirR : IsDirectionOf (𝕜 := ℝ) R d := by
    refine ⟨0, hdne, ?_⟩
    simp [R]
  have hconvRC : Convex ℝ (Set.recessionCone C) := recessionCone_convex (C := C) hCconv
  have hRsubset : R ⊆ Set.recessionCone C := by
    intro u hu
    rcases hu with ⟨t, ht, rfl⟩
    exact smul_mem_recessionCone_of_mem hdrec ht
  have hface : IsFace (𝕜 := ℝ) (Set.recessionCone C) R := by
    have hface' :
        IsFace (𝕜 := ℝ) (Set.recessionCone C) (maximizers (Set.recessionCone C) h) :=
      isFace_maximizers (C := Set.recessionCone C) (h := h) hconvRC
    simpa [R, hEqRay] using hface'
  have hhalfRC : IsHalfLineFace (𝕜 := ℝ) (Set.recessionCone C) R := by
    exact ⟨hface, ⟨d, hdirR⟩⟩
  have hExpRC : IsExposedFace (C := Set.recessionCone C) R := by
    refine ⟨hconvRC, hRsubset, ⟨h, ?_⟩⟩
    simpa [R] using hEqRay.symm
  exact ⟨R, ⟨hhalfRC, hExpRC⟩, hdirR⟩

/-- Text 18.0.14 (converse fails for exposed directions). There exists a closed convex set `C` and a
vector `d` such that `d` is an exposed direction of `0⁺ C` but not an exposed direction of `C`. -/
theorem exists_isExposedDirection_recessionCone_not_isExposedDirection :
    ∃ (C : Set (EuclideanSpace ℝ (Fin 2))) (d : EuclideanSpace ℝ (Fin 2)),
      IsClosed C ∧ Convex ℝ C ∧
        IsExposedDirection (Set.recessionCone C) d ∧ ¬ IsExposedDirection C d := by
  classical
  let C : Set (EuclideanSpace ℝ (Fin 2)) := parabolaSet
  let d : EuclideanSpace ℝ (Fin 2) := verticalDir
  have hCclosed : IsClosed C := by
    simpa [C, parabolaSet] using isClosed_parabola
  have hCconv : Convex ℝ C := by
    simpa [C, parabolaSet] using convex_parabola_set
  have hdne : d ≠ (0 : EuclideanSpace ℝ (Fin 2)) := by
    intro hd0
    have h := congrArg (fun v => v 1) hd0
    have h' : (1 : ℝ) = 0 := by
      simp [d] at h
    exact one_ne_zero h'
  have hrec_eq' :
      Set.recessionCone C = {z : EuclideanSpace ℝ (Fin 2) | z 0 = 0 ∧ 0 ≤ z 1} := by
    simpa [C, parabolaSet] using recessionCone_parabola_eq
  have hRay :
      {z : EuclideanSpace ℝ (Fin 2) | z 0 = 0 ∧ 0 ≤ z 1} =
        (fun t : ℝ => t • d) '' Set.Ici (0 : ℝ) := by
    ext z
    constructor
    · rintro ⟨hz0, hz1⟩
      refine ⟨z 1, hz1, ?_⟩
      ext i
      fin_cases i
      · simp [d, hz0]
      · simp [d]
    · rintro ⟨t, ht, rfl⟩
      have ht' : 0 ≤ t := by simpa using ht
      simp [d, verticalDir, ht']
  have hrec_eq : Set.recessionCone C = (fun t : ℝ => t • d) '' Set.Ici (0 : ℝ) :=
    hrec_eq'.trans hRay
  have hdir : IsDirectionOf (𝕜 := ℝ) (Set.recessionCone C) d := by
    refine ⟨0, hdne, ?_⟩
    simpa using (hrec_eq : Set.recessionCone C = (fun t : ℝ => t • d) '' Set.Ici (0 : ℝ))
  have hconvRC : Convex ℝ (Set.recessionCone C) := recessionCone_convex (C := C) hCconv
  have hface : IsFace (𝕜 := ℝ) (Set.recessionCone C) (Set.recessionCone C) := by
    exact isFace_self (C := Set.recessionCone C) hconvRC
  have hhalf : IsHalfLineFace (𝕜 := ℝ) (Set.recessionCone C) (Set.recessionCone C) := by
    exact ⟨hface, ⟨d, hdir⟩⟩
  have hmax_zero :
      maximizers (Set.recessionCone C) (0 : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ) =
        Set.recessionCone C := by
    ext x; constructor <;> intro hx <;> simpa [maximizers, isMaxOn_iff] using hx
  have hExpFace : IsExposedFace (C := Set.recessionCone C) (Set.recessionCone C) := by
    refine ⟨hconvRC, subset_rfl, ⟨0, ?_⟩⟩
    symm
    exact hmax_zero
  have hExpDir : IsExposedDirection (Set.recessionCone C) d := by
    exact ⟨Set.recessionCone C, ⟨hhalf, hExpFace⟩, hdir⟩
  have hnotExtreme : ¬ IsExtremeDirection (𝕜 := ℝ) C d := by
    intro hdext
    rcases hdext with ⟨C', hhalf', hdir'⟩
    rcases hdir' with ⟨x0, _hdne, hC'Eq⟩
    exact parabola_no_vertical_halfLineFace (x0 := x0) (C' := C') hC'Eq hhalf'.1
  have hnotExposed : ¬ IsExposedDirection C d := by
    intro hdexp
    exact hnotExtreme (isExtremeDirection_of_isExposedDirection (C := C) hdexp)
  exact ⟨C, d, hCclosed, hCconv, hExpDir, hnotExposed⟩
end Section18
end Chap04
