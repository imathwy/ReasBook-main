/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Changyu Zou, Yunxi Duan, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section09_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section18_part6

open scoped Pointwise

section Chap04
section Section18

noncomputable section

variable {𝕜 E : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [SMul 𝕜 E]

/-- The EuclideanSpace equivalence for `Fin n`. -/
abbrev euclideanEquiv (n : ℕ) :=
  (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ))

/-- Relative boundary in `Fin n → ℝ`, transported via `EuclideanSpace.equiv`. -/
def euclideanRelativeBoundary_fin (n : ℕ) (C : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  let e := euclideanEquiv n
  e '' euclideanRelativeBoundary n (e.symm '' C)

lemma mem_euclideanRelativeBoundary_fin_iff {n : ℕ} {C : Set (Fin n → ℝ)} {x : Fin n → ℝ} :
    x ∈ euclideanRelativeBoundary_fin n C ↔
      (euclideanEquiv n).symm x ∈
        euclideanRelativeBoundary n ((euclideanEquiv n).symm '' C) := by
  classical
  let e := euclideanEquiv n
  change x ∈ e '' euclideanRelativeBoundary n (e.symm '' C) ↔ _
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    refine ⟨e.symm x, hx, ?_⟩
    simp

lemma euclideanRelativeInterior_fin_subset_closure {n : ℕ} {C : Set (Fin n → ℝ)} :
    euclideanRelativeInterior_fin n C ⊆ closure C := by
  classical
  intro x hx
  let e := euclideanEquiv n
  have hx' :
      e.symm x ∈ euclideanRelativeInterior n (e.symm '' C) := by
    exact (mem_euclideanRelativeInterior_fin_iff (n := n) (C := C) (x := x)).1 hx
  have hxC : e.symm x ∈ e.symm '' C :=
    (euclideanRelativeInterior_subset_closure n (e.symm '' C)).1 hx'
  have hxcl : e.symm x ∈ closure (e.symm '' C) := subset_closure hxC
  have hximg : x ∈ e '' closure (e.symm '' C) := by
    refine ⟨e.symm x, hxcl, ?_⟩
    simp
  have hclosure :
      e '' closure (e.symm '' C) = closure (e '' (e.symm '' C)) := by
    simpa using (e.toHomeomorph.image_closure (e.symm '' C))
  have himage : e '' (e.symm '' C) = C := by
    ext y
    constructor
    · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
      simpa using hw
    · intro hy
      exact ⟨e.symm y, ⟨y, hy, rfl⟩, by simp⟩
  simpa [hclosure, himage] using hximg

lemma euclideanRelativeBoundary_fin_eq_diff_of_isClosed {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCclosed : IsClosed C) :
    euclideanRelativeBoundary_fin n C = C \ euclideanRelativeInterior_fin n C := by
  classical
  let e := euclideanEquiv n
  have hCclosedE : IsClosed (e.symm '' C) := by
    exact (e.symm.toHomeomorph.isClosed_image).2 hCclosed
  ext x
  constructor
  · intro hx
    have hxE :
        e.symm x ∈ euclideanRelativeBoundary n (e.symm '' C) :=
      (mem_euclideanRelativeBoundary_fin_iff (n := n) (C := C) (x := x)).1 hx
    have hxE' :
        e.symm x ∈ (e.symm '' C) \ euclideanRelativeInterior n (e.symm '' C) := by
      simpa [euclideanRelativeBoundary_eq_diff_of_isClosed (n := n) (C := e.symm '' C) hCclosedE]
        using hxE
    rcases hxE' with ⟨hxE_C, hxE_notri⟩
    have hxC : x ∈ C := by
      have : x ∈ e '' (e.symm '' C) := ⟨e.symm x, hxE_C, by simp⟩
      simpa using this
    have hxnotri : x ∉ euclideanRelativeInterior_fin n C := by
      intro hxri
      have hxriE :
          e.symm x ∈ euclideanRelativeInterior n (e.symm '' C) := by
        exact (mem_euclideanRelativeInterior_fin_iff (n := n) (C := C) (x := x)).1 hxri
      exact hxE_notri hxriE
    exact ⟨hxC, hxnotri⟩
  · intro hx
    rcases hx with ⟨hxC, hxnotri⟩
    have hxE_C : e.symm x ∈ e.symm '' C := ⟨x, hxC, by simp⟩
    have hxE_notri : e.symm x ∉ euclideanRelativeInterior n (e.symm '' C) := by
      intro hxriE
      have hxri :
          x ∈ euclideanRelativeInterior_fin n C :=
        (mem_euclideanRelativeInterior_fin_iff (n := n) (C := C) (x := x)).2 hxriE
      exact hxnotri hxri
    have hxE :
        e.symm x ∈ euclideanRelativeBoundary n (e.symm '' C) := by
      have hxE' :
          e.symm x ∈ (e.symm '' C) \ euclideanRelativeInterior n (e.symm '' C) :=
        ⟨hxE_C, hxE_notri⟩
      simpa [euclideanRelativeBoundary_eq_diff_of_isClosed (n := n) (C := e.symm '' C) hCclosedE]
        using hxE'
    exact (mem_euclideanRelativeBoundary_fin_iff (n := n) (C := C) (x := x)).2 hxE

/-- Transport a face along `EuclideanSpace.equiv` back to `Fin n → ℝ`. -/
lemma isFace_image_equiv_fin_symm {n : ℕ} {C C' : Set (EuclideanSpace ℝ (Fin n))}
    (hC' : IsFace (𝕜 := ℝ) C C') :
    IsFace (𝕜 := ℝ) ((euclideanEquiv n) '' C) ((euclideanEquiv n) '' C') := by
  classical
  let e := euclideanEquiv n
  refine ⟨?_, ?_⟩
  · exact Convex.affine_image (f := e.toAffineMap) hC'.1
  ·
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases hx with ⟨x', hx', rfl⟩
      exact ⟨x', hC'.2.subset hx', rfl⟩
    ·
      intro x hx y hy z hz hseg
      rcases hx with ⟨x', hx', rfl⟩
      rcases hy with ⟨y', hy', rfl⟩
      rcases hz with ⟨z', hz', rfl⟩
      have hseg' : z' ∈ openSegment ℝ x' y' := by
        have himage :
            (e.toAffineMap) '' openSegment ℝ x' y' =
              openSegment ℝ (e x') (e y') := by
          simpa using
            (image_openSegment (𝕜 := ℝ) (f := e.toAffineMap) (a := x') (b := y'))
        have hz' : e z' ∈ (e.toAffineMap) '' openSegment ℝ x' y' := by
          rw [himage]
          exact hseg
        rcases hz' with ⟨w, hw, hwz⟩
        have hwz' : w = z' := e.injective hwz
        simpa [hwz'] using hw
      have hx'' : x' ∈ C' := hC'.2.left_mem_of_mem_openSegment hx' hy' hz' hseg'
      exact ⟨x', hx'', rfl⟩

lemma isClosed_of_isFace_fin {n : ℕ} {C C' : Set (Fin n → ℝ)} (hC' : IsFace (𝕜 := ℝ) C C')
    (hC'conv : Convex ℝ C') (hCclosed : IsClosed C) : IsClosed C' := by
  classical
  let e := euclideanEquiv n
  have hC'e_face :
      IsFace (𝕜 := ℝ) (e.symm '' C) (e.symm '' C') :=
    isFace_image_equiv_fin (n := n) (C := C) (C' := C') hC'
  have hC'conv' : Convex ℝ (e.symm '' C') := by
    simpa using hC'conv.linear_image e.symm.toLinearMap
  have hCclosed' : IsClosed (e.symm '' C) := by
    exact (e.symm.toHomeomorph.isClosed_image).2 hCclosed
  have hC'closed' : IsClosed (e.symm '' C') :=
    isClosed_of_isFace (C := e.symm '' C) (C' := e.symm '' C') hC'e_face hC'conv' hCclosed'
  have hC'closed : IsClosed (e '' (e.symm '' C')) := by
    exact (e.toHomeomorph.isClosed_image).2 hC'closed'
  have himage : e '' (e.symm '' C') = C' := by
    ext y
    constructor
    · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
      simpa using hw
    · intro hy
      exact ⟨e.symm y, ⟨y, hy, rfl⟩, by simp⟩
  simpa [himage] using hC'closed

/-- Finrank of the affine span direction is invariant under the Euclidean equivalence. -/
lemma finrank_direction_affineSpan_equiv {n : ℕ} (C : Set (Fin n → ℝ)) :
    Module.finrank ℝ (affineSpan ℝ ((euclideanEquiv n).symm '' C)).direction =
      Module.finrank ℝ (affineSpan ℝ C).direction := by
  classical
  let e := euclideanEquiv n
  have hmap :
      (affineSpan ℝ C).map e.symm.toAffineMap = affineSpan ℝ (e.symm '' C) := by
    simpa using (AffineSubspace.map_span (f := e.symm.toAffineMap) (s := C))
  have hdir :
      (affineSpan ℝ C).direction.map (e.symm.toLinearMap) =
        (affineSpan ℝ (e.symm '' C)).direction := by
    have hdir0 :
        (affineSpan ℝ (e.symm '' C)).direction =
          (affineSpan ℝ C).direction.map (e.symm.toLinearMap) := by
      have hdir0' :
          ((affineSpan ℝ C).map e.symm.toAffineMap).direction =
            (affineSpan ℝ C).direction.map (e.symm.toLinearMap) :=
        (AffineSubspace.map_direction (s := affineSpan ℝ C) (f := e.symm.toAffineMap))
      have hdir0'' := hdir0'
      rw [hmap] at hdir0''
      exact hdir0''
    exact hdir0.symm
  have hfin :
      Module.finrank ℝ
          ((affineSpan ℝ C).direction.map (e.symm.toLinearMap)) =
        Module.finrank ℝ (affineSpan ℝ C).direction := by
    exact (LinearEquiv.finrank_map_eq (f := e.symm.toLinearEquiv)
      (p := (affineSpan ℝ C).direction))
  have hdir' :
      Module.finrank ℝ
          ((affineSpan ℝ C).direction.map (e.symm.toLinearMap)) =
        Module.finrank ℝ (affineSpan ℝ (e.symm '' C)).direction :=
    congrArg
      (fun S : Submodule ℝ (EuclideanSpace ℝ (Fin n)) => Module.finrank ℝ (↥S)) hdir
  exact hdir'.symm.trans hfin

/-- No-lineality is preserved under the Euclidean equivalence. -/
lemma noLines_equiv_fin {n : ℕ} {C : Set (Fin n → ℝ)}
    (hNoLines : ¬ ∃ y : Fin n → ℝ, y ≠ 0 ∧
      y ∈ (-Set.recessionCone C) ∩ Set.recessionCone C) :
    ¬ ∃ y : EuclideanSpace ℝ (Fin n), y ≠ 0 ∧
      y ∈ (-Set.recessionCone ((euclideanEquiv n).symm '' C)) ∩
        Set.recessionCone ((euclideanEquiv n).symm '' C) := by
  classical
  intro hlin
  rcases hlin with ⟨y, hyne, hy⟩
  let e := euclideanEquiv n
  have hyrec : y ∈ Set.recessionCone (e.symm '' C) := hy.2
  have hyrec_neg : (-y) ∈ Set.recessionCone (e.symm '' C) := by
    simpa [Set.mem_neg] using hy.1
  have hEq :
      Set.recessionCone (e.symm '' C) = e.symm '' Set.recessionCone C := by
    simpa using (recessionCone_image_linearEquiv (e := e.symm.toLinearEquiv) (C := C))
  rcases (by simpa [hEq] using hyrec) with ⟨y0, hy0rec, hy0eq⟩
  rcases (by simpa [hEq] using hyrec_neg) with ⟨y1, hy1rec, hy1eq⟩
  have hy1eq' : y1 = -y0 := by
    apply e.symm.injective
    calc
      e.symm y1 = -y := by simp [hy1eq]
      _ = -(e.symm y0) := by simp [hy0eq.symm]
      _ = e.symm (-y0) := by simp
  have hy0ne : y0 ≠ 0 := by
    intro hy0
    apply hyne
    calc
      y = e.symm y0 := hy0eq.symm
      _ = e.symm 0 := by simp [hy0]
      _ = 0 := by simp
  have hlin' :
      ∃ y : Fin n → ℝ, y ≠ 0 ∧ y ∈ (-Set.recessionCone C) ∩ Set.recessionCone C := by
    refine ⟨y0, hy0ne, ?_⟩
    refine ⟨?_, hy0rec⟩
    have : (-y0) ∈ Set.recessionCone C := by
      simpa [hy1eq'] using hy1rec
    simpa [Set.mem_neg] using this
  exact hNoLines hlin'

/-- Transfer the recession-cone lemma for extreme directions to `Fin n → ℝ`. -/
lemma mem_recessionCone_of_isExtremeDirection_fin {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCclosed : IsClosed C) {d : Fin n → ℝ} (hd : IsExtremeDirection (𝕜 := ℝ) C d) :
    d ∈ Set.recessionCone C := by
  classical
  let e := euclideanEquiv n
  rcases hd with ⟨C', hhalf, hdir⟩
  have hface : IsFace (𝕜 := ℝ) C C' := hhalf.1
  rcases hdir with ⟨x0, hdne, hC'eq⟩
  have hfaceE :
      IsFace (𝕜 := ℝ) (e.symm '' C) (e.symm '' C') :=
    isFace_image_equiv_fin (n := n) (C := C) (C' := C') hface
  have hdirE : IsDirectionOf (𝕜 := ℝ) (e.symm '' C') (e.symm d) := by
    refine ⟨e.symm x0, ?_, ?_⟩
    · intro hzero
      apply hdne
      apply e.symm.injective
      simpa using hzero
    ·
      have hC'eq' :
          e.symm '' C' =
            (fun t : ℝ => e.symm (x0 + t • d)) '' Set.Ici (0 : ℝ) := by
        ext y
        constructor
        · rintro ⟨z, hz, rfl⟩
          rcases (by simpa [hC'eq] using hz) with ⟨t, ht, rfl⟩
          exact ⟨t, ht, rfl⟩
        · rintro ⟨t, ht, rfl⟩
          refine ⟨x0 + t • d, ?_, rfl⟩
          have : x0 + t • d ∈ (fun t : ℝ => x0 + t • d) '' Set.Ici (0 : ℝ) :=
            ⟨t, ht, rfl⟩
          simpa [hC'eq] using this
      have hlin :
          (fun t : ℝ => e.symm (x0 + t • d)) =
            (fun t : ℝ => e.symm x0 + t • e.symm d) := by
        funext t
        calc
          e.symm (x0 + t • d) = e.symm x0 + e.symm (t • d) := by
            exact
              map_add (e.symm : (Fin n → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) x0 (t • d)
          _ = e.symm x0 + t • e.symm d := by
            exact
              (congrArg (fun z => e.symm x0 + z)
                (map_smul (e.symm : (Fin n → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) t d))
      have hC'eq'' := hC'eq'
      rw [hlin] at hC'eq''
      exact hC'eq''
  have hhalfE : IsHalfLineFace (𝕜 := ℝ) (e.symm '' C) (e.symm '' C') :=
    ⟨hfaceE, ⟨e.symm d, hdirE⟩⟩
  have hdE : IsExtremeDirection (𝕜 := ℝ) (e.symm '' C) (e.symm d) :=
    ⟨e.symm '' C', hhalfE, hdirE⟩
  have hCclosedE : IsClosed (e.symm '' C) := by
    exact (e.symm.toHomeomorph.isClosed_image).2 hCclosed
  have hdrecE :
      e.symm d ∈ Set.recessionCone (e.symm '' C) :=
    mem_recessionCone_of_isExtremeDirection (n := n) (C := e.symm '' C)
      (hCclosed := hCclosedE) hdE
  have hEq :
      Set.recessionCone (e.symm '' C) = e.symm '' Set.recessionCone C := by
    simpa using
      (recessionCone_image_linearEquiv (e := e.symm.toLinearEquiv) (C := C))
  have hdrecE' : e.symm d ∈ e.symm '' Set.recessionCone C := by
    have hdrecE' := hdrecE
    rw [hEq] at hdrecE'
    exact hdrecE'
  rcases hdrecE' with ⟨d', hd'rec, hd'Eq⟩
  have hd' : d' = d := by
    apply e.symm.injective
    simp [hd'Eq]
  simpa [hd'] using hd'rec
/-- Extreme directions of a face are extreme directions of the ambient set. -/
lemma isExtremeDirection_of_isFace {n : ℕ} {C F : Set (Fin n → ℝ)} {d : Fin n → ℝ}
    (hF : IsFace (𝕜 := ℝ) C F) (hd : IsExtremeDirection (𝕜 := ℝ) F d) :
    IsExtremeDirection (𝕜 := ℝ) C d := by
  rcases hd with ⟨F', hhalf, hdir⟩
  rcases hhalf with ⟨hface, hdir'⟩
  refine ⟨F', ?_, hdir⟩
  refine ⟨?_, hdir'⟩
  exact isFace_trans hF hface

/-- A relative boundary point lies in the relative interior of a proper face. -/
lemma exists_proper_face_with_mem_ri_of_mem_euclideanRelativeBoundary {n : ℕ}
    {C : Set (Fin n → ℝ)} (hCclosed : IsClosed C) (hCconv : Convex ℝ C)
    {x : Fin n → ℝ} (hx : x ∈ euclideanRelativeBoundary_fin n C) :
    ∃ F : Set (Fin n → ℝ),
      IsFace (𝕜 := ℝ) C F ∧ F ≠ C ∧ F.Nonempty ∧ Convex ℝ F ∧
        x ∈ euclideanRelativeInterior_fin n F := by
  classical
  let e := euclideanEquiv n
  have hxE :
      e.symm x ∈ euclideanRelativeBoundary n (e.symm '' C) :=
    (mem_euclideanRelativeBoundary_fin_iff (n := n) (C := C) (x := x)).1 hx
  have hxC : x ∈ C := by
    have hxclE : e.symm x ∈ closure (e.symm '' C) := by
      have hx' :
          e.symm x ∈ closure (e.symm '' C) ∧
            e.symm x ∉ euclideanRelativeInterior n (e.symm '' C) := by
        simpa [euclideanRelativeBoundary] using hxE
      exact hx'.1
    have hxcl : x ∈ closure C := by
      have hximg : x ∈ e '' closure (e.symm '' C) := by
        exact ⟨e.symm x, hxclE, by simp⟩
      have hclosure :
          e '' closure (e.symm '' C) = closure (e '' (e.symm '' C)) := by
        simpa using (e.toHomeomorph.image_closure (e.symm '' C))
      have himage : e '' (e.symm '' C) = C := by
        ext y
        constructor
        · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
          simpa using hw
        · intro hy
          exact ⟨e.symm y, ⟨y, hy, rfl⟩, by simp⟩
      simpa [hclosure, himage] using hximg
    simpa [hCclosed.closure_eq] using hxcl
  have hxnotri : x ∉ euclideanRelativeInterior_fin n C := by
    intro hxri
    have hxriE :
        e.symm x ∈ euclideanRelativeInterior n (e.symm '' C) := by
      exact (mem_euclideanRelativeInterior_fin_iff (n := n) (C := C) (x := x)).1 hxri
    have hxE' :
        e.symm x ∉ euclideanRelativeInterior n (e.symm '' C) := by
      have hx' :
          e.symm x ∈ closure (e.symm '' C) ∧
            e.symm x ∉ euclideanRelativeInterior n (e.symm '' C) := by
        simpa [euclideanRelativeBoundary] using hxE
      exact hx'.2
    exact hxE' hxriE
  have hCne : C.Nonempty := ⟨x, hxC⟩
  have hCneE : (e.symm '' C).Nonempty := by
    rcases hCne with ⟨x0, hx0⟩
    exact ⟨e.symm x0, ⟨x0, hx0, rfl⟩⟩
  have hCconvE : Convex ℝ (e.symm '' C) :=
    Convex.affine_image (f := e.symm.toAffineMap) hCconv
  rcases
      faceRelativeInteriors_pairwiseDisjoint_and_sUnion_eq_and_maximal (C := e.symm '' C) hCneE
        hCconvE with
    ⟨_hpair, hsUnion, _hmax, _hmax2⟩
  have hxU : e.symm x ∈ Set.sUnion (faceRelativeInteriors n (e.symm '' C)) := by
    have hxC_E : e.symm x ∈ e.symm '' C := ⟨x, hxC, by simp⟩
    simpa [hsUnion] using hxC_E
  rcases Set.mem_sUnion.1 hxU with ⟨U, hU, hxU⟩
  rcases hU with ⟨F, hFface, hFne, hFconv, rfl⟩
  let F' : Set (Fin n → ℝ) := e '' F
  have hFface' : IsFace (𝕜 := ℝ) C F' := by
    simpa [F', e] using
      (isFace_image_equiv_fin_symm (n := n) (C := e.symm '' C) (C' := F) hFface)
  have hFneC : F' ≠ C := by
    intro hFC
    have hxri : x ∈ euclideanRelativeInterior_fin n F' := by
      have hxriE : e.symm x ∈ euclideanRelativeInterior n F := hxU
      have hpre : e.symm '' F' = F := by
        ext y
        constructor
        · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
          simpa using hw
        · intro hy
          exact ⟨e y, ⟨y, hy, rfl⟩, by simp⟩
      have hxriE' : e.symm x ∈ euclideanRelativeInterior n (e.symm '' F') := by
        simpa [hpre] using hxriE
      exact (mem_euclideanRelativeInterior_fin_iff (n := n) (C := F') (x := x)).2 hxriE'
    have : x ∈ euclideanRelativeInterior_fin n C := by simpa [hFC] using hxri
    exact hxnotri this
  have hFne' : F'.Nonempty := by
    rcases hFne with ⟨y, hy⟩
    exact ⟨e y, ⟨y, hy, rfl⟩⟩
  have hFconv' : Convex ℝ F' := Convex.affine_image (f := e.toAffineMap) hFconv
  have hxri' : x ∈ euclideanRelativeInterior_fin n F' := by
    have hxriE : e.symm x ∈ euclideanRelativeInterior n F := hxU
    have hpre : e.symm '' F' = F := by
      ext y
      constructor
      · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
        simpa using hw
      · intro hy
        exact ⟨e y, ⟨y, hy, rfl⟩, by simp⟩
    have hxriE' : e.symm x ∈ euclideanRelativeInterior n (e.symm '' F') := by
      simpa [hpre] using hxriE
    exact (mem_euclideanRelativeInterior_fin_iff (n := n) (C := F') (x := x)).2 hxriE'
  exact ⟨F', hFface', hFneC, hFne', hFconv', hxri'⟩

/-- A face of a closed convex set with no nonzero lineality direction also has none. -/
lemma noLines_of_isFace {n : ℕ} {C F : Set (Fin n → ℝ)} (hF : IsFace (𝕜 := ℝ) C F)
    (hFne : F.Nonempty) (hCclosed : IsClosed C) (hCconv : Convex ℝ C)
    (hNoLinesC : ¬ ∃ y : Fin n → ℝ, y ≠ 0 ∧
      y ∈ (-Set.recessionCone C) ∩ Set.recessionCone C) :
    ¬ ∃ y : Fin n → ℝ, y ≠ 0 ∧ y ∈ (-Set.recessionCone F) ∩ Set.recessionCone F := by
  classical
  intro hlinF
  let e := euclideanEquiv n
  rcases hlinF with ⟨y, hyne, hy⟩
  have hyrec : y ∈ Set.recessionCone F := hy.2
  have hyrec_neg : (-y) ∈ Set.recessionCone F := by
    simpa [Set.mem_neg] using hy.1
  have hyrecE : e.symm y ∈ Set.recessionCone (e.symm '' F) := by
    have hEq' : Set.recessionCone (e.symm '' F) = e.symm '' Set.recessionCone F := by
      simpa using (recessionCone_image_linearEquiv (e := e.symm.toLinearEquiv) (C := F))
    rw [hEq']
    exact ⟨y, hyrec, by simp⟩
  have hyrecE_neg : (-e.symm y) ∈ Set.recessionCone (e.symm '' F) := by
    have hEq' : Set.recessionCone (e.symm '' F) = e.symm '' Set.recessionCone F := by
      simpa using (recessionCone_image_linearEquiv (e := e.symm.toLinearEquiv) (C := F))
    rw [hEq']
    exact ⟨-y, hyrec_neg, by simp⟩
  have hlinF' :
      ∃ y : EuclideanSpace ℝ (Fin n), y ≠ 0 ∧ y ∈ Set.linealitySpace (e.symm '' F) := by
    refine ⟨e.symm y, ?_, ?_⟩
    · intro h0
      apply hyne
      have : y = 0 := by
        calc
          y = e (e.symm y) := (e.apply_symm_apply y).symm
          _ = e 0 := by simpa using congrArg e h0
          _ = 0 := by simp
      exact this
    ·
      refine ⟨?_, hyrecE⟩
      simpa [Set.mem_neg] using hyrecE_neg
  have hFneE : (e.symm '' F).Nonempty := by
    rcases hFne with ⟨x, hx⟩
    exact ⟨e.symm x, ⟨x, hx, rfl⟩⟩
  have hlineF :
      ∃ L : Set (Fin n → ℝ), IsLine n L ∧
        L ⊆ ((e : EuclideanSpace ℝ (Fin n) → Fin n → ℝ) '' (e.symm '' F)) := by
    exact exists_line_of_nonzero_lineality (C := e.symm '' F) hFneE hlinF'
  have hlineC :
      ∃ L : Set (Fin n → ℝ), IsLine n L ∧
        L ⊆ ((e : EuclideanSpace ℝ (Fin n) → Fin n → ℝ) '' (e.symm '' C)) := by
    rcases hlineF with ⟨L, hLline, hLsub⟩
    refine ⟨L, hLline, ?_⟩
    intro x hx
    rcases hLsub hx with ⟨y', hyF, rfl⟩
    rcases hyF with ⟨y0, hy0, rfl⟩
    exact ⟨e.symm y0, ⟨y0, hF.2.subset hy0, rfl⟩, by simp⟩
  have hCne : C.Nonempty := by
    rcases hFne with ⟨x, hx⟩
    exact ⟨x, hF.2.subset hx⟩
  have hCneE : (e.symm '' C).Nonempty := by
    rcases hCne with ⟨x, hx⟩
    exact ⟨e.symm x, ⟨x, hx, rfl⟩⟩
  have hCclosedE : IsClosed (e.symm '' C) := by
    exact (e.symm.toHomeomorph.isClosed_image).2 hCclosed
  have hCconvE : Convex ℝ (e.symm '' C) :=
    Convex.affine_image (f := e.symm.toAffineMap) hCconv
  have hlinC :
      ∃ y : EuclideanSpace ℝ (Fin n), y ≠ 0 ∧ y ∈ Set.linealitySpace (e.symm '' C) := by
    exact nonzero_lineality_of_line (C := e.symm '' C) hCneE hCclosedE hCconvE hlineC
  rcases hlinC with ⟨yE, hyEne, hyE⟩
  have hyErec : yE ∈ Set.recessionCone (e.symm '' C) := hyE.2
  have hyErec_neg : (-yE) ∈ Set.recessionCone (e.symm '' C) := by
    simpa [Set.mem_neg] using hyE.1
  have hrecC : e yE ∈ Set.recessionCone C := by
    have hEq := recessionCone_image_linearEquiv (e := e.toLinearEquiv) (C := e.symm '' C)
    have hEq' : Set.recessionCone C = e '' Set.recessionCone (e.symm '' C) := by
      have himage : e '' (e.symm '' C) = C := by
        ext z
        constructor
        · rintro ⟨u, ⟨v, hv, rfl⟩, rfl⟩
          simpa using hv
        · intro hz
          exact ⟨e.symm z, ⟨z, hz, rfl⟩, by simp⟩
      simpa [himage] using hEq
    have : e yE ∈ e '' Set.recessionCone (e.symm '' C) := ⟨yE, hyErec, rfl⟩
    simpa [hEq'] using this
  have hrecC_neg : (-e yE) ∈ Set.recessionCone C := by
    have hEq := recessionCone_image_linearEquiv (e := e.toLinearEquiv) (C := e.symm '' C)
    have hEq' : Set.recessionCone C = e '' Set.recessionCone (e.symm '' C) := by
      have himage : e '' (e.symm '' C) = C := by
        ext z
        constructor
        · rintro ⟨u, ⟨v, hv, rfl⟩, rfl⟩
          simpa using hv
        · intro hz
          exact ⟨e.symm z, ⟨z, hz, rfl⟩, by simp⟩
      simpa [himage] using hEq
    have : e (-yE) ∈ e '' Set.recessionCone (e.symm '' C) := ⟨-yE, hyErec_neg, rfl⟩
    have : -e yE ∈ e '' Set.recessionCone (e.symm '' C) := by
      simpa using this
    simpa [hEq'] using this
  have hlinC' :
      ∃ y : Fin n → ℝ, y ≠ 0 ∧ y ∈ (-Set.recessionCone C) ∩ Set.recessionCone C := by
    refine ⟨e yE, ?_, ?_⟩
    · intro h0
      apply hyEne
      have : e.symm (e yE) = e.symm 0 := congrArg e.symm h0
      simpa using this
    ·
      refine ⟨?_, hrecC⟩
      simpa [Set.mem_neg] using hrecC_neg
  exact hNoLinesC hlinC'

/-- Boundary points belong to the mixed convex hull under the finrank induction hypothesis. -/
lemma mem_mixedConvexHull_of_mem_euclideanRelativeBoundary_under_IH {n : ℕ}
    {C : Set (Fin n → ℝ)} (hCclosed : IsClosed C) (hCconv : Convex ℝ C)
    (hNoLines : ¬ ∃ y : Fin n → ℝ, y ≠ 0 ∧
      y ∈ (-Set.recessionCone C) ∩ Set.recessionCone C)
    (IH :
      ∀ ⦃F : Set (Fin n → ℝ)⦄,
        IsClosed F → Convex ℝ F →
        (¬ ∃ y : Fin n → ℝ, y ≠ 0 ∧ y ∈ (-Set.recessionCone F) ∩ Set.recessionCone F) →
        Module.finrank ℝ (affineSpan ℝ F).direction <
        Module.finrank ℝ (affineSpan ℝ C).direction →
          F ⊆ mixedConvexHull (n := n) (F.extremePoints ℝ)
            {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) F d})
    {x : Fin n → ℝ} (hx : x ∈ euclideanRelativeBoundary_fin n C) :
    x ∈ mixedConvexHull (n := n) (C.extremePoints ℝ)
      {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d} := by
  classical
  rcases
      exists_proper_face_with_mem_ri_of_mem_euclideanRelativeBoundary (n := n) (C := C) hCclosed
        hCconv hx with
    ⟨F, hFface, hFneC, hFne, hFconv, hxri⟩
  have hFclosed : IsClosed F :=
    isClosed_of_isFace_fin (n := n) (C := C) (C' := F) hFface hFconv hCclosed
  have hxF : x ∈ F := by
    have hxcl : x ∈ closure F := (euclideanRelativeInterior_fin_subset_closure (n := n) (C := F)) hxri
    simpa [hFclosed.closure_eq] using hxcl
  have hNoLinesF :
      ¬ ∃ y : Fin n → ℝ, y ≠ 0 ∧ y ∈ (-Set.recessionCone F) ∩ Set.recessionCone F := by
    exact noLines_of_isFace (n := n) (C := C) (F := F) hFface hFne hCclosed hCconv hNoLines
  have hCne : C.Nonempty := by
    rcases hFne with ⟨x0, hx0⟩
    exact ⟨x0, hFface.2.subset hx0⟩
  have hfin :
      Module.finrank ℝ (affineSpan ℝ F).direction <
        Module.finrank ℝ (affineSpan ℝ C).direction := by
    let e := euclideanEquiv n
    have hFfaceE : IsFace (𝕜 := ℝ) (e.symm '' C) (e.symm '' F) :=
      isFace_image_equiv_fin (n := n) (C := C) (C' := F) hFface
    have hFconvE : Convex ℝ (e.symm '' F) :=
      Convex.affine_image (f := e.symm.toAffineMap) hFconv
    have hFneE : (e.symm '' F).Nonempty := by
      rcases hFne with ⟨x0, hx0⟩
      exact ⟨e.symm x0, ⟨x0, hx0, rfl⟩⟩
    have hCneE : (e.symm '' C).Nonempty := by
      rcases hCne with ⟨x0, hx0⟩
      exact ⟨e.symm x0, ⟨x0, hx0, rfl⟩⟩
    have hneE : e.symm '' F ≠ e.symm '' C := by
      intro hFC
      apply hFneC
      have himageF : e '' (e.symm '' F) = F := by
        ext y
        constructor
        · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
          simpa using hw
        · intro hy
          exact ⟨e.symm y, ⟨y, hy, rfl⟩, by simp⟩
      have himageC : e '' (e.symm '' C) = C := by
        ext y
        constructor
        · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
          simp [hw]
        · intro hy
          exact ⟨e.symm y, ⟨y, hy, rfl⟩, by simp⟩
      have hFC' : F = C := by
        have h := congrArg (fun s => e '' s) hFC
        simpa [himageF, himageC] using h
      exact hFC'
    have hfinE :
        Module.finrank ℝ (affineSpan ℝ (e.symm '' F)).direction <
          Module.finrank ℝ (affineSpan ℝ (e.symm '' C)).direction :=
      finrank_direction_affineSpan_lt_of_isFace_ne (C := e.symm '' C) (C' := e.symm '' F)
        hFfaceE hneE hFconvE hFneE hCneE
    have hfinF :
        Module.finrank ℝ (affineSpan ℝ (e.symm '' F)).direction =
          Module.finrank ℝ (affineSpan ℝ F).direction :=
      (finrank_direction_affineSpan_equiv (n := n) (C := F))
    have hfinC :
        Module.finrank ℝ (affineSpan ℝ (e.symm '' C)).direction =
          Module.finrank ℝ (affineSpan ℝ C).direction :=
      (finrank_direction_affineSpan_equiv (n := n) (C := C))
    simpa [hfinF, hfinC] using hfinE
  have hxHullF :
      x ∈ mixedConvexHull (n := n) (F.extremePoints ℝ)
        {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) F d} :=
    (IH hFclosed hFconv hNoLinesF hfin) hxF
  have hpoints : F.extremePoints ℝ ⊆ C.extremePoints ℝ := by
    intro y hy
    have hyext : IsExtremePoint (𝕜 := ℝ) F y :=
      (isExtremePoint_iff_mem_extremePoints (𝕜 := ℝ) (C := F) (x := y)).2 hy
    have hyextC : IsExtremePoint (𝕜 := ℝ) C y :=
      isExtremePoint_of_isFace_of_isExtremePoint (𝕜 := ℝ) hFface hyext
    exact (isExtremePoint_iff_mem_extremePoints (𝕜 := ℝ) (C := C) (x := y)).1 hyextC
  have hdirs :
      {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) F d} ⊆
        {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d} := by
    intro d hd
    exact isExtremeDirection_of_isFace (n := n) (C := C) (F := F) (d := d) hFface hd
  have hmono :
      mixedConvexHull (n := n) (F.extremePoints ℝ)
          {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) F d} ⊆
        mixedConvexHull (n := n) (C.extremePoints ℝ)
          {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d} :=
    mixedConvexHull_mono (n := n) hpoints hdirs
  exact hmono hxHullF

/-- Relative interior points belong to the mixed convex hull once boundary points do. -/
lemma mem_mixedConvexHull_of_mem_euclideanRelativeInterior_of_boundary_in_hull {n : ℕ}
    {C : Set (Fin n → ℝ)} (hCclosed : IsClosed C) (hCconv : Convex ℝ C)
    (hC_not_affine :
      ¬ ∃ A : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)),
        (A : Set (EuclideanSpace ℝ (Fin n))) = (euclideanEquiv n).symm '' C)
    (hC_not_closedHalf_affine :
      ¬ ∃ (A : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)))
          (f : (EuclideanSpace ℝ (Fin n)) →ₗ[ℝ] ℝ) (a : ℝ),
          f ≠ 0 ∧ (euclideanEquiv n).symm '' C = (A : Set (EuclideanSpace ℝ (Fin n))) ∩ {x | f x ≤ a})
    (hbdy :
      ∀ y ∈ euclideanRelativeBoundary_fin n C,
        y ∈ mixedConvexHull (n := n) (C.extremePoints ℝ)
          {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d}) :
    ∀ ⦃x : Fin n → ℝ⦄, x ∈ euclideanRelativeInterior_fin n C →
      x ∈ mixedConvexHull (n := n) (C.extremePoints ℝ)
        {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d} := by
  intro x hxri
  classical
  let e := euclideanEquiv n
  have hxriE :
      e.symm x ∈ euclideanRelativeInterior n (e.symm '' C) :=
    (mem_euclideanRelativeInterior_fin_iff (n := n) (C := C) (x := x)).1 hxri
  have hCclosedE : IsClosed (e.symm '' C) := by
    exact (e.symm.toHomeomorph.isClosed_image).2 hCclosed
  have hCconvE : Convex ℝ (e.symm '' C) :=
    Convex.affine_image (f := e.symm.toAffineMap) hCconv
  obtain ⟨yE, zE, hybE, hzbE, hxsegE⟩ :=
    exists_mem_segment_of_mem_euclideanRelativeInterior (n := n) (C := e.symm '' C) hCclosedE
      hCconvE hC_not_affine hC_not_closedHalf_affine hxriE
  have hyb : e yE ∈ euclideanRelativeBoundary_fin n C := by
    refine (mem_euclideanRelativeBoundary_fin_iff (n := n) (C := C) (x := e yE)).2 ?_
    simpa using hybE
  have hzb : e zE ∈ euclideanRelativeBoundary_fin n C := by
    refine (mem_euclideanRelativeBoundary_fin_iff (n := n) (C := C) (x := e zE)).2 ?_
    simpa using hzbE
  have hxseg : x ∈ segment ℝ (e yE) (e zE) := by
    have hxsegE' : e.symm x ∈ segment ℝ yE zE := hxsegE
    have hxsegE'' :
        x ∈ e '' segment ℝ yE zE := by
      refine ⟨e.symm x, hxsegE', by simp⟩
    have himage :
        e '' segment ℝ yE zE = segment ℝ (e yE) (e zE) := by
      simpa using
        (image_segment (𝕜 := ℝ) (f := e.toAffineMap) (a := yE) (b := zE))
    simpa [himage] using hxsegE''
  have hy : e yE ∈ mixedConvexHull (n := n) (C.extremePoints ℝ)
      {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d} := hbdy (e yE) hyb
  have hz : e zE ∈ mixedConvexHull (n := n) (C.extremePoints ℝ)
      {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d} := hbdy (e zE) hzb
  have hconv :
      Convex ℝ
        (mixedConvexHull (n := n) (C.extremePoints ℝ)
          {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d}) :=
    convex_mixedConvexHull (n := n) (C.extremePoints ℝ)
      {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d}
  have hseg :
      segment ℝ (e yE) (e zE) ⊆
        mixedConvexHull (n := n) (C.extremePoints ℝ)
          {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d} :=
    hconv.segment_subset hy hz
  exact hseg hxseg

/-- Base case: if the affine span has direction of finrank `0`, then `C` is a singleton and is
generated by its extreme points/directions. -/
lemma closedConvex_eq_mixedConvexHull_of_finrank_direction_eq_zero {n : ℕ}
    {C : Set (Fin n → ℝ)} (hCclosed : IsClosed C) (hCconv : Convex ℝ C)
    (hfin : Module.finrank ℝ (affineSpan ℝ C).direction = 0) :
    C =
      mixedConvexHull (n := n) (C.extremePoints ℝ)
        {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d} := by
  classical
  refine Set.Subset.antisymm ?_ ?_
  ·
    by_cases hCne : C.Nonempty
    ·
      let x0 : Fin n → ℝ := Classical.choose hCne
      have hx0 : x0 ∈ C := Classical.choose_spec hCne
      have hdir : (affineSpan ℝ C).direction = ⊥ := by
        simpa using
          (Submodule.finrank_eq_zero (R := ℝ) (M := Fin n → ℝ)
              (S := (affineSpan ℝ C).direction)).1 hfin
      have hsubset : C ⊆ {x0} := by
        intro x hx
        have hxA : x ∈ affineSpan ℝ C := subset_affineSpan (k := ℝ) (s := C) hx
        have hx0A : x0 ∈ affineSpan ℝ C := subset_affineSpan (k := ℝ) (s := C) hx0
        have hxv :
            x -ᵥ x0 ∈ (affineSpan ℝ C).direction :=
          (AffineSubspace.vsub_right_mem_direction_iff_mem (s := affineSpan ℝ C) (p := x0) hx0A
              x).2 hxA
        have hxv0 : x -ᵥ x0 = 0 := by
          simpa [hdir] using hxv
        have hxEq : x = x0 := by
          exact (vsub_eq_zero_iff_eq).1 hxv0
        simp [hxEq]
      have hCeq : C = {x0} :=
        Set.Subset.antisymm hsubset (Set.singleton_subset_iff.mpr hx0)
      intro x hx
      have hx' : x = x0 := by
        simpa [hCeq] using hx
      subst x
      have hxext : x0 ∈ C.extremePoints ℝ := by
        apply (isExtremePoint_iff_mem_extremePoints (𝕜 := ℝ) (C := C) (x := x0)).1
        refine ⟨hx0, ?_⟩
        intro y z hy hz _hseg
        have hy' : y = x0 := by
          have : y ∈ ({x0} : Set (Fin n → ℝ)) := hsubset hy
          simpa using this
        have hz' : z = x0 := by
          have : z ∈ ({x0} : Set (Fin n → ℝ)) := hsubset hz
          simpa using this
        exact ⟨hy', hz'⟩
      have hxadd :
          x0 ∈ C.extremePoints ℝ +
            ray n {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d} := by
        refine Set.mem_add.mpr ?_
        refine ⟨x0, hxext, 0, ?_, by simp⟩
        exact (Set.mem_insert_iff).2 (Or.inl rfl)
      exact
        (add_ray_subset_mixedConvexHull (n := n) (S₀ := C.extremePoints ℝ)
          (S₁ := {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d})) hxadd
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

/-- The endpoint of a ray is an extreme point of the ray. -/
lemma mem_extremePoints_endpoint_of_eq_image_add_smul_Ici {n : ℕ}
    {C : Set (Fin n → ℝ)} {x0 d : Fin n → ℝ} (hd : d ≠ 0)
    (hC : C = (fun t : ℝ => x0 + t • d) '' Set.Ici (0 : ℝ)) :
    x0 ∈ C.extremePoints ℝ := by
  classical
  have hx0C : x0 ∈ C := by
    have hx0' : x0 + (0 : ℝ) • d ∈ (fun t : ℝ => x0 + t • d) '' Set.Ici (0 : ℝ) := by
      refine ⟨0, by simp, by simp⟩
    simpa [hC] using hx0'
  refine (isExtremePoint_iff_mem_extremePoints (𝕜 := ℝ) (C := C) (x := x0)).1 ?_
  refine ⟨hx0C, ?_⟩
  intro y z hy hz hxseg
  have hy' : y ∈ (fun t : ℝ => x0 + t • d) '' Set.Ici (0 : ℝ) := by
    simpa [hC] using hy
  have hz' : z ∈ (fun t : ℝ => x0 + t • d) '' Set.Ici (0 : ℝ) := by
    simpa [hC] using hz
  rcases hy' with ⟨ty, hty, rfl⟩
  rcases hz' with ⟨tz, htz, rfl⟩
  rcases hxseg with ⟨a, b, ha, hb, hab, hx⟩
  have hx' :
      (a + b) • x0 + (a * ty + b * tz) • d = x0 := by
    -- Expand the convex combination along the ray.
    simpa [smul_add, add_smul, smul_smul, mul_add, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using hx
  have hx'' : x0 + (a * ty + b * tz) • d = x0 := by
    simpa [hab, one_smul] using hx'
  have hx''' : (a * ty + b * tz) • d = 0 := by
    have : x0 + (a * ty + b * tz) • d = x0 + 0 := by simpa using hx''
    exact add_left_cancel this
  have hcoeff : a * ty + b * tz = 0 := by
    rcases (smul_eq_zero.mp hx''') with hcoeff | hzero
    · exact hcoeff
    · exact (hd hzero).elim
  have hty0 : ty = 0 := by
    have hty0' : 0 ≤ ty := hty
    have htz0' : 0 ≤ tz := htz
    have hmul_le : a * ty ≤ 0 := by
      have hcoeff' : a * ty = -(b * tz) := by linarith [hcoeff]
      have hnonpos : -(b * tz) ≤ 0 := by
        exact neg_nonpos.mpr (mul_nonneg (le_of_lt hb) htz0')
      simpa [hcoeff'] using hnonpos
    have hmul_ge : 0 ≤ a * ty := mul_nonneg (le_of_lt ha) hty0'
    have hmul_eq : a * ty = 0 := le_antisymm hmul_le hmul_ge
    have ha0 : a ≠ 0 := ne_of_gt ha
    exact (mul_eq_zero.mp hmul_eq).resolve_left ha0
  have htz0 : tz = 0 := by
    have hty0' : 0 ≤ ty := hty
    have htz0' : 0 ≤ tz := htz
    have hmul_le : b * tz ≤ 0 := by
      have hcoeff' : b * tz = -(a * ty) := by linarith [hcoeff]
      have hnonpos : -(a * ty) ≤ 0 := by
        exact neg_nonpos.mpr (mul_nonneg (le_of_lt ha) hty0')
      simpa [hcoeff'] using hnonpos
    have hmul_ge : 0 ≤ b * tz := mul_nonneg (le_of_lt hb) htz0'
    have hmul_eq : b * tz = 0 := le_antisymm hmul_le hmul_ge
    have hb0 : b ≠ 0 := ne_of_gt hb
    exact (mul_eq_zero.mp hmul_eq).resolve_left hb0
  subst hty0
  subst htz0
  simp

/-- A ray is an extreme direction of itself. -/
lemma isExtremeDirection_of_eq_image_add_smul_Ici {n : ℕ}
    {C : Set (Fin n → ℝ)} {x0 d : Fin n → ℝ} (hd : d ≠ 0)
    (hC : C = (fun t : ℝ => x0 + t • d) '' Set.Ici (0 : ℝ)) (hCconv : Convex ℝ C) :
    IsExtremeDirection (𝕜 := ℝ) C d := by
  refine ⟨C, ?_, ?_⟩
  · refine ⟨isFace_self (C := C) hCconv, ?_⟩
    exact ⟨d, ⟨x0, hd, hC⟩⟩
  · exact ⟨x0, hd, hC⟩

end
end Section18
end Chap04
