/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Changyu Zou, Yunxi Duan, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section06_part5
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section06_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section06_part8
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section08_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section11_part7
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap04.section17_part11
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap04.section17_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap04.section18_part2

open scoped Pointwise

section Chap04
section Section18

variable {𝕜 E : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [SMul 𝕜 E]

/-- The collection `𝓤` of all relative interiors of nonempty convex faces of a convex set `C`
in `ℝⁿ`. -/
def faceRelativeInteriors (n : ℕ) (C : Set (EuclideanSpace ℝ (Fin n))) :
    Set (Set (EuclideanSpace ℝ (Fin n))) :=
  {U | ∃ F : Set (EuclideanSpace ℝ (Fin n)),
    IsFace (𝕜 := ℝ) C F ∧ F.Nonempty ∧ Convex ℝ F ∧ U = euclideanRelativeInterior n F}

/-- A singleton in `ℝⁿ` is relatively open. -/
lemma euclideanRelativelyOpen_singleton (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    euclideanRelativelyOpen n ({x} : Set (EuclideanSpace ℝ (Fin n))) := by
  classical
  have hset :
      ({x} : Set (EuclideanSpace ℝ (Fin n))) =
        (AffineSubspace.mk' x (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
          Set (EuclideanSpace ℝ (Fin n))) := by
    ext y; constructor
    · intro hy
      have hy' : y = x := by simpa [Set.mem_singleton_iff] using hy
      subst hy'
      simp
    · intro hy
      have hy' : y -ᵥ x ∈ (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin n))) := by
        simpa [AffineSubspace.mem_mk'] using hy
      have hy'' : y -ᵥ x = 0 := by simpa using hy'
      have hyx : y = x := (vsub_eq_zero_iff_eq).1 hy''
      simp [Set.mem_singleton_iff, hyx]
  have hri :
      euclideanRelativeInterior n ({x} : Set (EuclideanSpace ℝ (Fin n))) =
        ({x} : Set (EuclideanSpace ℝ (Fin n))) := by
    simpa [hset] using
      (euclideanRelativeInterior_affineSubspace_eq (n := n)
        (s := AffineSubspace.mk' x (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin n)))))
  simp [euclideanRelativelyOpen, hri]

/-- If two elements of `faceRelativeInteriors` meet, then they are equal. -/
lemma faceRelativeInteriors_eq_of_nonempty_inter {n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin n))} {U V : Set (EuclideanSpace ℝ (Fin n))}
    (hU : U ∈ faceRelativeInteriors n C) (hV : V ∈ faceRelativeInteriors n C)
    (hUV : (U ∩ V).Nonempty) : U = V := by
  rcases hU with ⟨F, hFface, _hFne, _hFconv, rfl⟩
  rcases hV with ⟨G, hGface, _hGne, _hGconv, rfl⟩
  have hri : (euclideanRelativeInterior n F ∩ euclideanRelativeInterior n G).Nonempty := by
    simpa using hUV
  have hFG : F = G :=
    isFace_eq_of_euclideanRelativeInterior_inter (C := C) hFface hGface hri
  simp [hFG]

/-- Membership in `FaceOf.sInf` means lying in `C` and every face in `S`. -/
lemma FaceOf.mem_sInf_iff {C : Set E} (hC : Convex 𝕜 C) (S : Set (FaceOf (𝕜 := 𝕜) C)) {x : E} :
    x ∈ (FaceOf.sInf (𝕜 := 𝕜) C hC S).1 ↔ x ∈ C ∧ ∀ F ∈ S, x ∈ F.1 := by
  classical
  constructor
  · intro hx
    have hx' :
        x ∈ ⋂ i : Option {F // F ∈ S},
          (match i with | none => C | some F => (F.1.1 : Set E)) := by
      simpa [FaceOf.sInf] using hx
    have hxC : x ∈ C := by
      have := Set.mem_iInter.mp hx' none
      simpa using this
    have hxF : ∀ F ∈ S, x ∈ F.1 := by
      intro F hF
      have hxsome := Set.mem_iInter.mp hx' (some ⟨F, hF⟩)
      simpa using hxsome
    exact ⟨hxC, hxF⟩
  · rintro ⟨hxC, hxF⟩
    have hx' :
        x ∈ ⋂ i : Option {F // F ∈ S},
          (match i with | none => C | some F => (F.1.1 : Set E)) := by
      refine Set.mem_iInter.2 ?_
      intro i
      cases i with
      | none =>
          simpa using hxC
      | some F =>
          have hxF' : x ∈ F.1.1 := hxF F.1 F.2
          simpa using hxF'
    simpa [FaceOf.sInf] using hx'

/-- If a linear functional is bounded above by `β` on `C` and attains `β`, then its maximizers are
exactly `C ∩ {x | f x = β}`. -/
lemma maximizers_eq_inter_of_le {n : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))}
    (f : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ) {β : ℝ}
    (h_le : ∀ x ∈ C, f x ≤ β) (h_eq : ∃ x0 ∈ C, f x0 = β) :
    maximizers C f = C ∩ {x | f x = β} := by
  ext x
  constructor
  · intro hx
    rcases (mem_maximizers_iff (C := C) (h := f)).1 hx with ⟨hxC, hxmax⟩
    rcases h_eq with ⟨x0, hx0C, hx0Eq⟩
    have hxle : f x ≤ β := h_le x hxC
    have hβle : β ≤ f x := by
      have hxmax' := hxmax x0 hx0C
      simpa [hx0Eq] using hxmax'
    have hxEq : f x = β := le_antisymm hxle hβle
    exact ⟨hxC, hxEq⟩
  · rintro ⟨hxC, hxEq⟩
    refine (mem_maximizers_iff (C := C) (h := f)).2 ?_
    refine ⟨hxC, ?_⟩
    intro y hyC
    have hy_le : f y ≤ β := h_le y hyC
    rw [hxEq]
    exact hy_le

/-- Any relatively open convex subset of `C` is contained in a member of `faceRelativeInteriors`. -/
lemma exists_faceRelativeInteriors_superset_of_relOpenConvex {n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin n))} (hCne : C.Nonempty) (hC : Convex ℝ C)
    {D : Set (EuclideanSpace ℝ (Fin n))}
    (hDC : D ⊆ C) (hDconv : Convex ℝ D) (hDopen : euclideanRelativelyOpen n D) :
    ∃ U ∈ faceRelativeInteriors n C, D ⊆ U := by
  classical
  by_cases hDempty : D = ∅
  · refine ⟨euclideanRelativeInterior n C, ?_, ?_⟩
    · exact ⟨C, isFace_self (𝕜 := ℝ) C hC, hCne, hC, rfl⟩
    · simp [hDempty]
  have hDne : D.Nonempty := by
    by_contra hDne
    exact hDempty (Set.not_nonempty_iff_eq_empty.mp hDne)
  let S : Set (FaceOf (𝕜 := ℝ) C) := {F | D ⊆ F.1 ∧ Convex ℝ F.1}
  let Fmin : FaceOf (𝕜 := ℝ) C := FaceOf.sInf (𝕜 := ℝ) C hC S
  let Cmin : Set (EuclideanSpace ℝ (Fin n)) := Fmin.1
  have hCminface : IsFace (𝕜 := ℝ) C Cmin := Fmin.2
  have hDCmin : D ⊆ Cmin := by
    intro x hx
    have hxC : x ∈ C := hDC hx
    have hxF : ∀ F ∈ S, x ∈ F.1 := by
      intro F hF
      exact (hF.1) hx
    have hxCmin :
        x ∈ (FaceOf.sInf (𝕜 := ℝ) C hC S).1 :=
      (FaceOf.mem_sInf_iff (𝕜 := ℝ) (C := C) hC S).2 ⟨hxC, hxF⟩
    simpa [Cmin, Fmin] using hxCmin
  have hCminconv : Convex ℝ Cmin := by
    intro x hx y hy a b ha hb hab
    have hx' : x ∈ (FaceOf.sInf (𝕜 := ℝ) C hC S).1 := by
      simpa [Cmin, Fmin] using hx
    have hy' : y ∈ (FaceOf.sInf (𝕜 := ℝ) C hC S).1 := by
      simpa [Cmin, Fmin] using hy
    rcases (FaceOf.mem_sInf_iff (𝕜 := ℝ) (C := C) hC S).1 hx' with ⟨hxC, hxF⟩
    rcases (FaceOf.mem_sInf_iff (𝕜 := ℝ) (C := C) hC S).1 hy' with ⟨hyC, hyF⟩
    have hxyC : a • x + b • y ∈ C := hC hxC hyC ha hb hab
    have hxyF : ∀ F ∈ S, a • x + b • y ∈ F.1 := by
      intro F hF
      have hFconv : Convex ℝ F.1 := hF.2
      exact hFconv (hxF F hF) (hyF F hF) ha hb hab
    have hxy :
        a • x + b • y ∈ (FaceOf.sInf (𝕜 := ℝ) C hC S).1 :=
      (FaceOf.mem_sInf_iff (𝕜 := ℝ) (C := C) hC S).2 ⟨hxyC, hxyF⟩
    simpa [Cmin, Fmin] using hxy
  have hDCmin_closure : D ⊆ closure Cmin := by
    intro x hx
    exact subset_closure (hDCmin hx)
  have hDnot : ¬ D ⊆ euclideanRelativeBoundary n Cmin := by
    intro hDbound
    have hDdisj : Disjoint D (intrinsicInterior ℝ Cmin) := by
      refine Set.disjoint_left.2 ?_
      intro x hxD hxInt
      have hxri : x ∈ euclideanRelativeInterior n Cmin :=
        (intrinsicInterior_subset_euclideanRelativeInterior n Cmin) hxInt
      have hxrb : x ∈ euclideanRelativeBoundary n Cmin := hDbound hxD
      have hxnotri : x ∉ euclideanRelativeInterior n Cmin := by
        have hxrb' : x ∈ closure Cmin ∧ x ∉ euclideanRelativeInterior n Cmin := by
          simpa [euclideanRelativeBoundary] using hxrb
        exact hxrb'.2
      exact hxnotri hxri
    let E := EuclideanSpace ℝ (Fin n)
    let e : E ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)
    let Cfun : Set (Fin n → ℝ) := e '' Cmin
    let Dfun : Set (Fin n → ℝ) := e '' D
    have hCfunconv : Convex ℝ Cfun := hCminconv.linear_image e.toLinearMap
    have hDfunconv : Convex ℝ Dfun := hDconv.linear_image e.toLinearMap
    have hDfunne : Dfun.Nonempty := hDne.image e
    have hDfunsub : Dfun ⊆ Cfun := by
      intro y hy
      rcases hy with ⟨x, hxD, rfl⟩
      exact ⟨x, hDCmin hxD, rfl⟩
    have hriCfun : intrinsicInterior ℝ Cfun = e '' intrinsicInterior ℝ Cmin := by
      simpa [Cfun] using (ContinuousLinearEquiv.image_intrinsicInterior (e := e) (s := Cmin))
    have hDfun_disj : Disjoint Dfun (intrinsicInterior ℝ Cfun) := by
      refine Set.disjoint_left.2 ?_
      intro y hyD hyI
      rcases hyD with ⟨x, hxD, rfl⟩
      have hyI' : e x ∈ e '' intrinsicInterior ℝ Cmin := by
        simpa [hriCfun] using hyI
      rcases hyI' with ⟨x', hx'I, hEq⟩
      have hxEq : x = x' := e.injective (by simpa using hEq.symm)
      have hxI : x ∈ intrinsicInterior ℝ Cmin := by simpa [hxEq] using hx'I
      exact (Set.disjoint_left.1 hDdisj) hxD hxI
    have hsupport :
        ∃ Hfun, IsNontrivialSupportingHyperplane n Cfun Hfun ∧ Dfun ⊆ Hfun := by
      exact
        (exists_nontrivialSupportingHyperplane_containing_iff_disjoint_intrinsicInterior (n := n)
            (C := Cfun) (D := Dfun) hCfunconv hDfunne hDfunconv hDfunsub).2 hDfun_disj
    rcases hsupport with ⟨Hfun, hHnontriv, hDHfun⟩
    rcases hHnontriv with ⟨hHsupport, hCfunnot⟩
    rcases hHsupport with ⟨b, β, _hb0, hHdef, hC_le, hx0⟩
    let f : E →ₗ[ℝ] ℝ := (dotProductLinear n b) ∘ₗ e.toLinearMap
    have hfle : ∀ x ∈ Cmin, f x ≤ β := by
      intro x hxCmin
      have hxCfun : e x ∈ Cfun := ⟨x, hxCmin, rfl⟩
      have hxle : e x ⬝ᵥ b ≤ β := hC_le (e x) hxCfun
      simpa [f, dotProductLinear] using hxle
    have hf_eq : ∃ x0 ∈ Cmin, f x0 = β := by
      rcases hx0 with ⟨x0, hx0Cfun, hx0Eq⟩
      rcases hx0Cfun with ⟨x0', hx0'Cmin, rfl⟩
      refine ⟨x0', hx0'Cmin, ?_⟩
      simpa [f, dotProductLinear] using hx0Eq
    have hmax_eq : maximizers Cmin f = Cmin ∩ {x | f x = β} :=
      maximizers_eq_inter_of_le (C := Cmin) (f := f) hfle hf_eq
    have hDsubset_max : D ⊆ maximizers Cmin f := by
      intro x hxD
      have hxCmin : x ∈ Cmin := hDCmin hxD
      have hxDfun : e x ∈ Dfun := ⟨x, hxD, rfl⟩
      have hxHfun : e x ∈ Hfun := hDHfun hxDfun
      have hxEq : e x ⬝ᵥ b = β := by simpa [hHdef] using hxHfun
      have hxEq' : f x = β := by simpa [f, dotProductLinear] using hxEq
      have hxmem : x ∈ Cmin ∩ {x | f x = β} := ⟨hxCmin, hxEq'⟩
      simpa [hmax_eq] using hxmem
    have hFface : IsFace (𝕜 := ℝ) Cmin (maximizers Cmin f) :=
      isFace_maximizers (C := Cmin) (h := f) hCminconv
    have hFfaceC : IsFace (𝕜 := ℝ) C (maximizers Cmin f) :=
      isFace_trans hCminface hFface
    let F' : FaceOf (𝕜 := ℝ) C := ⟨maximizers Cmin f, hFfaceC⟩
    have hF'conv : Convex ℝ (maximizers Cmin f) :=
      convex_maximizers (C := Cmin) (h := f) hCminconv
    have hF'inS : F' ∈ S := by
      exact ⟨hDsubset_max, hF'conv⟩
    have hCminsubset : Cmin ⊆ maximizers Cmin f := by
      have hGLB := FaceOf.isGLB_sInf (𝕜 := ℝ) (C := C) hC S
      have hle : Fmin ≤ F' := hGLB.1 hF'inS
      exact hle
    have hCfunsub : Cfun ⊆ Hfun := by
      intro y hyCfun
      rcases hyCfun with ⟨x, hxCmin, rfl⟩
      have hxmax : x ∈ maximizers Cmin f := hCminsubset hxCmin
      have hxmem : x ∈ Cmin ∩ {x | f x = β} := by
        simpa [hmax_eq] using hxmax
      have hxEq : f x = β := hxmem.2
      have hxEq' : e x ⬝ᵥ b = β := by simpa [f, dotProductLinear] using hxEq
      simpa [hHdef] using hxEq'
    exact hCfunnot hCfunsub
  have hri_subset :
      euclideanRelativeInterior n D ⊆ euclideanRelativeInterior n Cmin :=
    euclideanRelativeInterior_subset_of_subset_closure_not_subset_relativeBoundary n Cmin D
      hCminconv hDconv hDCmin_closure hDnot
  have hDsubsetri : D ⊆ euclideanRelativeInterior n Cmin := by
    intro x hx
    have hx' : x ∈ euclideanRelativeInterior n D := by
      rw [hDopen]
      exact hx
    exact hri_subset hx'
  have hCminne : Cmin.Nonempty := hDne.mono hDCmin
  refine ⟨euclideanRelativeInterior n Cmin, ?_, ?_⟩
  · exact ⟨Cmin, hCminface, hCminne, hCminconv, rfl⟩
  · exact hDsubsetri

/-- The union of `faceRelativeInteriors` is the ambient convex set. -/
lemma faceRelativeInteriors_sUnion_eq {n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin n))} (hCne : C.Nonempty) (hC : Convex ℝ C) :
    Set.sUnion (faceRelativeInteriors n C) = C := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨U, hU, hxU⟩
    rcases hU with ⟨F, hFface, _hFne, _hFconv, hUeq⟩
    have hxri : x ∈ euclideanRelativeInterior n F := by simpa [hUeq] using hxU
    have hxF : x ∈ F := (euclideanRelativeInterior_subset_closure n F).1 hxri
    exact hFface.2.subset hxF
  · intro x hxC
    have hDsubset : ({x} : Set (EuclideanSpace ℝ (Fin n))) ⊆ C := by
      intro y hy
      have hyx : y = x := by simpa [Set.mem_singleton_iff] using hy
      simpa [hyx] using hxC
    have hDconv : Convex ℝ ({x} : Set (EuclideanSpace ℝ (Fin n))) := by
      exact convex_singleton x
    have hDopen : euclideanRelativelyOpen n ({x} : Set (EuclideanSpace ℝ (Fin n))) :=
      euclideanRelativelyOpen_singleton n x
    rcases
        exists_faceRelativeInteriors_superset_of_relOpenConvex (C := C) hCne hC hDsubset hDconv
          hDopen with ⟨U, hU, hDU⟩
    have hxU : x ∈ U := hDU (by simp)
    exact ⟨U, hU, hxU⟩

/-- Elements of `faceRelativeInteriors` are maximal relatively open convex subsets of `C`. -/
lemma faceRelativeInteriors_maximal_of_absorption {n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin n))} (hCne : C.Nonempty) (hC : Convex ℝ C)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : U ∈ faceRelativeInteriors n C)
    {D : Set (EuclideanSpace ℝ (Fin n))} (hDC : D ⊆ C) (hDconv : Convex ℝ D)
    (hDopen : euclideanRelativelyOpen n D) (hUD : U ⊆ D) : D = U := by
  classical
  have hUne : U.Nonempty := by
    rcases hU with ⟨F, _hFface, hFne, hFconv, rfl⟩
    exact euclideanRelativeInterior_nonempty_of_convex_of_nonempty hFconv hFne
  rcases
      exists_faceRelativeInteriors_superset_of_relOpenConvex (C := C) hCne hC hDC hDconv hDopen with
    ⟨U', hU', hDU'⟩
  have hUsubsetU' : U ⊆ U' := Set.Subset.trans hUD hDU'
  have hnonempty : (U ∩ U').Nonempty := by
    rcases hUne with ⟨x, hxU⟩
    exact ⟨x, hxU, hUsubsetU' hxU⟩
  have hEq : U = U' := faceRelativeInteriors_eq_of_nonempty_inter hU hU' hnonempty
  have hDU : D ⊆ U := by simpa [hEq] using hDU'
  exact Set.Subset.antisymm hDU hUD

/-- Theorem 18.2. Let `C` be a non-empty convex set, and let `𝓤` be the collection of all relative
interiors of non-empty faces of `C`. Then `𝓤` is a partition of `C` (pairwise disjoint with union
equal to `C`). Every relatively open convex subset of `C` is contained in some element of `𝓤`, and
the sets in `𝓤` are the maximal relatively open convex subsets of `C`. -/
theorem faceRelativeInteriors_pairwiseDisjoint_and_sUnion_eq_and_maximal {n : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin n))) (hCne : C.Nonempty) (hC : Convex ℝ C) :
    Set.Pairwise (faceRelativeInteriors n C) Disjoint ∧
      Set.sUnion (faceRelativeInteriors n C) = C ∧
        (∀ D : Set (EuclideanSpace ℝ (Fin n)),
          D ⊆ C → Convex ℝ D → euclideanRelativelyOpen n D →
            ∃ U ∈ faceRelativeInteriors n C, D ⊆ U) ∧
          (∀ U ∈ faceRelativeInteriors n C,
            ∀ D : Set (EuclideanSpace ℝ (Fin n)),
              D ⊆ C → Convex ℝ D → euclideanRelativelyOpen n D → U ⊆ D → D = U) := by
  classical
  refine ⟨?_, ?_⟩
  · intro U hU V hV hUV
    by_contra hdisj
    have hnonempty : (U ∩ V).Nonempty :=
      (Set.not_disjoint_iff_nonempty_inter).1 hdisj
    exact hUV (faceRelativeInteriors_eq_of_nonempty_inter hU hV hnonempty)
  · refine ⟨faceRelativeInteriors_sUnion_eq (C := C) hCne hC, ?_⟩
    refine ⟨?_, ?_⟩
    · intro D hDC hDconv hDopen
      exact
        exists_faceRelativeInteriors_superset_of_relOpenConvex (C := C) hCne hC hDC hDconv hDopen
    · intro U hU D hDC hDconv hDopen hUD
      exact
        faceRelativeInteriors_maximal_of_absorption (C := C) hCne hC hU hDC hDconv hDopen hUD

/-- The affine span of a segment is the line through its endpoints. -/
lemma affineSpan_segment_eq_line {n : ℕ} (u v : EuclideanSpace ℝ (Fin n)) :
    affineSpan ℝ (segment ℝ u v) = line[ℝ, u, v] := by
  apply le_antisymm
  · refine (affineSpan_le (k := ℝ) (s := segment ℝ u v) (Q := line[ℝ, u, v])).2 ?_
    intro x hx
    rcases (segment_eq_image_lineMap (𝕜 := ℝ) u v ▸ hx) with ⟨t, ht, rfl⟩
    exact AffineMap.lineMap_mem_affineSpan_pair (r := t) u v
  ·
    have hsubset : (insert u ({v} : Set (EuclideanSpace ℝ (Fin n)))) ⊆ segment ℝ u v := by
      intro x hx
      rcases Set.mem_insert_iff.mp hx with hx | hxv
      · subst hx
        exact left_mem_segment (𝕜 := ℝ) x v
      ·
        have hxv' : x = v := by simpa [Set.mem_singleton_iff] using hxv
        subst hxv'
        exact right_mem_segment (𝕜 := ℝ) u x
    simpa using (affineSpan_mono (k := ℝ) hsubset)

/-- Points in an open segment lie in the relative interior of the closed segment. -/
lemma openSegment_subset_euclideanRelativeInterior_segment {n : ℕ}
    {u v : EuclideanSpace ℝ (Fin n)} (huv : u ≠ v) :
    openSegment ℝ u v ⊆ euclideanRelativeInterior n (segment ℝ u v) := by
  intro x hx
  rcases (openSegment_eq_image_lineMap (𝕜 := ℝ) u v ▸ hx) with ⟨t, ht, rfl⟩
  have ht0 : 0 < t := ht.1
  have ht1 : t < 1 := ht.2
  let m : ℝ := min t (1 - t)
  have hmpos : 0 < m := by
    have ht1' : 0 < 1 - t := by linarith
    exact (lt_min_iff).2 ⟨ht0, ht1'⟩
  let ε : ℝ := m * dist u v / 2
  have hεpos : 0 < ε := by
    have hdist : 0 < dist u v := (dist_pos.mpr huv)
    have : 0 < m * dist u v := mul_pos hmpos hdist
    have htwo : 0 < (2 : ℝ) := by norm_num
    exact (div_pos this htwo)
  refine ⟨?_, ε, hεpos, ?_⟩
  ·
    have hxseg : AffineMap.lineMap u v t ∈ segment ℝ u v := by
      refine (segment_eq_image_lineMap (𝕜 := ℝ) u v).symm ▸ ?_
      exact ⟨t, Set.mem_Icc_of_Ioo ht, rfl⟩
    exact (subset_affineSpan (k := ℝ) (s := segment ℝ u v)) hxseg
  · intro z hz
    rcases hz with ⟨hzball, hzspan⟩
    have hzball' : z ∈ Metric.closedBall (AffineMap.lineMap u v t) ε := by
      have hball_eq :
          (fun y => AffineMap.lineMap u v t + y) '' (ε • euclideanUnitBall n) =
            Metric.closedBall (AffineMap.lineMap u v t) ε := by
        simpa using
          (translate_smul_unitBall_eq_closedBall (n := n) (a := AffineMap.lineMap u v t) (ε := ε)
            hεpos)
      simpa [hball_eq] using hzball
    have hdist : dist z (AffineMap.lineMap u v t) ≤ ε := by
      simpa [Metric.closedBall] using hzball'
    have hzline : z ∈ line[ℝ, u, v] := by
      simpa [affineSpan_segment_eq_line (u := u) (v := v)] using hzspan
    have hzline' : (z -ᵥ u) +ᵥ u ∈ line[ℝ, u, v] := by
      simpa using hzline
    rcases
        (vadd_left_mem_affineSpan_pair (k := ℝ) (p₁ := u) (p₂ := v) (v := z -ᵥ u)).1 hzline' with
      ⟨r, hr⟩
    have hz_eq : AffineMap.lineMap u v r = z := by
      have hr' : r • (v - u) = z - u := by
        simpa [vsub_eq_sub] using hr
      have hz' : r • (v - u) + u = z := by
        calc
          r • (v - u) + u = (z - u) + u := by simp [hr']
          _ = z := by
            exact sub_add_cancel z u
      simpa [AffineMap.lineMap_apply_module'] using hz'
    have hdist' : dist r t * dist u v ≤ ε := by
      have hdist'' : dist (AffineMap.lineMap u v r) (AffineMap.lineMap u v t) ≤ ε := by
        simpa [hz_eq] using hdist
      simpa [dist_lineMap_lineMap] using hdist''
    have hε' : ε = (m / 2) * dist u v := by
      simp [ε, mul_div_right_comm]
    have hdist' : dist r t * dist u v ≤ (m / 2) * dist u v := by
      simpa [hε'] using hdist'
    have hdist_rt : dist r t ≤ m / 2 := by
      have hdistuv : 0 < dist u v := (dist_pos.mpr huv)
      exact (le_of_mul_le_mul_right hdist' hdistuv)
    have hrIcc : r ∈ Set.Icc (t - m / 2) (t + m / 2) := by
      have hclosed : r ∈ Metric.closedBall t (m / 2) := by
        simpa [Metric.closedBall] using hdist_rt
      simpa [Real.closedBall_eq_Icc] using hclosed
    have hlow : 0 ≤ t - m / 2 := by
      have hm_le : m ≤ t := min_le_left _ _
      nlinarith [hm_le, ht0]
    have hhigh : t + m / 2 ≤ 1 := by
      have hm_le : m ≤ 1 - t := min_le_right _ _
      nlinarith [hm_le, ht1]
    have hrIcc01 : r ∈ Set.Icc (0 : ℝ) 1 := by
      refine ⟨?_, ?_⟩
      · exact le_trans hlow hrIcc.1
      · exact le_trans hrIcc.2 hhigh
    have hzmem : z ∈ AffineMap.lineMap u v '' Set.Icc (0 : ℝ) 1 := by
      exact ⟨r, hrIcc01, hz_eq⟩
    simpa [segment_eq_image_lineMap] using hzmem

/-- The denominator in the two-between computation lies in `(0,1)`. -/
lemma den_two_between {t1 t2 : ℝ} (ht1 : t1 ∈ Set.Ioo (0 : ℝ) 1)
    (ht2 : t2 ∈ Set.Ioo (0 : ℝ) 1) :
    0 < t1 + t2 - t1 * t2 ∧ t1 + t2 - t1 * t2 < 1 := by
  have ht1pos : 0 < t1 := ht1.1
  have ht1lt : t1 < 1 := ht1.2
  have ht2pos : 0 < t2 := ht2.1
  have ht2lt : t2 < 1 := ht2.2
  have h1mt1 : 0 < 1 - t1 := by linarith
  have h1mt2 : 0 < 1 - t2 := by linarith
  have hdenpos' : 0 < t1 + (1 - t1) * t2 := by
    have hpos : 0 < (1 - t1) * t2 := mul_pos h1mt1 ht2pos
    exact add_pos ht1pos hpos
  have hdenpos : 0 < t1 + t2 - t1 * t2 := by
    have hdeneq : t1 + t2 - t1 * t2 = t1 + (1 - t1) * t2 := by ring
    simpa [hdeneq] using hdenpos'
  have hdenlt : t1 + t2 - t1 * t2 < 1 := by
    have hdeneq : 1 - (t1 + t2 - t1 * t2) = (1 - t1) * (1 - t2) := by ring
    have hpos : 0 < (1 - t1) * (1 - t2) := mul_pos h1mt1 h1mt2
    have : 0 < 1 - (t1 + t2 - t1 * t2) := by simpa [hdeneq] using hpos
    linarith
  exact ⟨hdenpos, hdenlt⟩

/-- Solve for `y` from two `lineMap` relations by eliminating the middle point. -/
lemma lineMap_solve_y_of_two_between {n : ℕ}
    {x y u v : EuclideanSpace ℝ (Fin n)} {t1 t2 : ℝ}
    (hx : x = AffineMap.lineMap y u t1) (hy : y = AffineMap.lineMap x v t2)
    (hden : t1 + t2 - t1 * t2 ≠ 0) :
    y = AffineMap.lineMap u v (t2 / (t1 + t2 - t1 * t2)) := by
  set den : ℝ := t1 + t2 - t1 * t2
  have hden' : den ≠ 0 := by
    simpa [den] using hden
  have hx' : x = (1 - t1) • y + t1 • u := by
    simpa [AffineMap.lineMap_apply_module] using hx
  have hy' : y = (1 - t2) • x + t2 • v := by
    simpa [AffineMap.lineMap_apply_module] using hy
  have hy'' :
      y = ((1 - t2) * (1 - t1)) • y + ((1 - t2) * t1) • u + t2 • v := by
    calc
      y = (1 - t2) • x + t2 • v := hy'
      _ = (1 - t2) • ((1 - t1) • y + t1 • u) + t2 • v := by simp [hx']
      _ = ((1 - t2) * (1 - t1)) • y + ((1 - t2) * t1) • u + t2 • v := by
        simp [smul_add, smul_smul, mul_comm, add_assoc]
  have hy_sub :
      y - ((1 - t2) * (1 - t1)) • y = ((1 - t2) * t1) • u + t2 • v := by
    calc
      y - ((1 - t2) * (1 - t1)) • y =
          (((1 - t2) * (1 - t1)) • y + ((1 - t2) * t1) • u + t2 • v) -
            ((1 - t2) * (1 - t1)) • y := by
        nth_rewrite 1 [hy'']
        rfl
      _ = ((1 - t2) * t1) • u + t2 • v := by
        abel
  have hdeneq' : den = 1 - (1 - t2) * (1 - t1) := by
    have : t1 + t2 - t1 * t2 = 1 - (1 - t2) * (1 - t1) := by ring
    simpa [den] using this
  have hdeneq : den • y = ((1 - t2) * t1) • u + t2 • v := by
    calc
      den • y = (1 - (1 - t2) * (1 - t1)) • y := by simp [hdeneq']
      _ = y - ((1 - t2) * (1 - t1)) • y := by
        simpa [one_smul] using
          (sub_smul (1 : ℝ) ((1 - t2) * (1 - t1)) y)
      _ = ((1 - t2) * t1) • u + t2 • v := hy_sub
  have hdeneq2 : den • (y - u) = t2 • (v - u) := by
    calc
      den • (y - u) = den • y - den • u := by simp [smul_sub]
      _ = ((1 - t2) * t1) • u + t2 • v - den • u := by
        simp [hdeneq]
      _ = t2 • (v - u) := by
        have hcoef : (1 - t2) * t1 - den = -t2 := by
          have : (1 - t2) * t1 - (t1 + t2 - t1 * t2) = -t2 := by ring
          simpa [den] using this
        calc
          ((1 - t2) * t1) • u + t2 • v - den • u =
              t2 • v + (((1 - t2) * t1) • u - den • u) := by
            simp [sub_eq_add_neg, add_assoc, add_comm]
          _ = t2 • v + (((1 - t2) * t1 - den) • u) := by
            rw [← sub_smul ((1 - t2) * t1) den u]
          _ = t2 • v + (-t2) • u := by
            simp [hcoef]
          _ = t2 • v - t2 • u := by
            simp [sub_eq_add_neg, neg_smul]
          _ = t2 • (v - u) := by
            simp [sub_eq_add_neg]
  have hyu : y - u = (t2 / den) • (v - u) := by
    calc
      y - u = (1 / den) • (den • (y - u)) := by
        simp [smul_smul, one_div, hden']
      _ = (1 / den) • (t2 • (v - u)) := by simp [hdeneq2]
      _ = (t2 / den) • (v - u) := by
        simp [smul_smul, div_eq_mul_inv, mul_comm]
  have hyu' : y = (t2 / den) • (v - u) + u := (sub_eq_iff_eq_add).1 hyu
  simpa [AffineMap.lineMap_apply_module', den] using hyu'

/-- Solve for `x` from two `lineMap` relations by substituting the computed `y`. -/
lemma lineMap_solve_x_of_two_between {n : ℕ}
    {x y u v : EuclideanSpace ℝ (Fin n)} {t1 t2 : ℝ}
    (hx : x = AffineMap.lineMap y u t1) (hy : y = AffineMap.lineMap x v t2)
    (hden : t1 + t2 - t1 * t2 ≠ 0) :
    x = AffineMap.lineMap u v (((1 - t1) * t2) / (t1 + t2 - t1 * t2)) := by
  set den : ℝ := t1 + t2 - t1 * t2
  have hy' : y = AffineMap.lineMap u v (t2 / den) := by
    have := lineMap_solve_y_of_two_between (hx := hx) (hy := hy) (hden := hden)
    simpa [den] using this
  have hyu : y = (t2 / den) • (v - u) + u := by
    simpa [AffineMap.lineMap_apply_module'] using hy'
  have hx' : x = t1 • (u - y) + y := by
    simpa [AffineMap.lineMap_apply_module'] using hx
  have huy : u - y = - (t2 / den) • (v - u) := by
    calc
      u - y = u - ((t2 / den) • (v - u) + u) := by simp [hyu]
      _ = u - (t2 / den) • (v - u) - u := by
        simp
      _ = - (t2 / den) • (v - u) := by
        simp [sub_eq_add_neg, add_assoc]
        abel_nf
  have hxcalc : x = ((1 - t1) * (t2 / den)) • (v - u) + u := by
    calc
      x = t1 • (u - y) + y := hx'
      _ = t1 • (-(t2 / den) • (v - u)) + ((t2 / den) • (v - u) + u) := by
        rw [huy, hyu]
      _ = (-(t1 * (t2 / den))) • (v - u) + (t2 / den) • (v - u) + u := by
        simp [smul_neg, smul_smul, add_assoc]
      _ = ((t2 / den) - t1 * (t2 / den)) • (v - u) + u := by
        calc
          (-(t1 * (t2 / den))) • (v - u) + (t2 / den) • (v - u) + u =
              (t2 / den) • (v - u) - (t1 * (t2 / den)) • (v - u) + u := by
            simp [sub_eq_add_neg, add_assoc, add_comm]
          _ = ((t2 / den) - t1 * (t2 / den)) • (v - u) + u := by
            rw [← sub_smul (t2 / den) (t1 * (t2 / den)) (v - u)]
      _ = ((1 - t1) * (t2 / den)) • (v - u) + u := by
        have hcoef : (t2 / den) - t1 * (t2 / den) = (1 - t1) * (t2 / den) := by ring
        simp [hcoef]
  have hcoef : (1 - t1) * (t2 / den) = ((1 - t1) * t2) / den := by
    simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  have hxcalc' : x = (((1 - t1) * t2) / den) • (v - u) + u := by
    have hxcalc'': x = ((1 - t1) * (t2 / den)) • (v - u) + u := hxcalc
    simp [hcoef] at hxcalc''
    exact hxcalc''
  simpa [AffineMap.lineMap_apply_module', den] using hxcalc'

/-- If `x` is between `y` and `u`, and `y` is between `x` and `v`, then both lie between `u` and `v`. -/
lemma openSegment_of_two_between_relations {n : ℕ}
    {x y u v : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ openSegment ℝ y u) (hy : y ∈ openSegment ℝ x v) :
    x ∈ openSegment ℝ u v ∧ y ∈ openSegment ℝ u v := by
  have hx' : x ∈ AffineMap.lineMap y u '' Set.Ioo (0 : ℝ) 1 := by
    simpa [openSegment_eq_image_lineMap (𝕜 := ℝ)] using hx
  rcases hx' with ⟨t1, ht1, hxdef⟩
  have hy' : y ∈ AffineMap.lineMap x v '' Set.Ioo (0 : ℝ) 1 := by
    simpa [openSegment_eq_image_lineMap (𝕜 := ℝ)] using hy
  rcases hy' with ⟨t2, ht2, hydef⟩
  have hxdef' : x = AffineMap.lineMap y u t1 := by
    simpa using hxdef.symm
  have hydef' : y = AffineMap.lineMap x v t2 := by
    simpa using hydef.symm
  set den : ℝ := t1 + t2 - t1 * t2
  have hdenpos : 0 < den := (den_two_between ht1 ht2).1
  have hdenne : den ≠ 0 := ne_of_gt hdenpos
  have hyline :
      y = AffineMap.lineMap u v (t2 / den) := by
    have hdenne' : t1 + t2 - t1 * t2 ≠ 0 := by simpa [den] using hdenne
    have := lineMap_solve_y_of_two_between (hx := hxdef') (hy := hydef') (hden := hdenne')
    simpa [den] using this
  have hxline :
      x = AffineMap.lineMap u v (((1 - t1) * t2) / den) := by
    have hdenne' : t1 + t2 - t1 * t2 ≠ 0 := by simpa [den] using hdenne
    have := lineMap_solve_x_of_two_between (hx := hxdef') (hy := hydef') (hden := hdenne')
    simpa [den] using this
  have ht1pos : 0 < t1 := ht1.1
  have ht2pos : 0 < t2 := ht2.1
  have h1mt1 : 0 < 1 - t1 := by linarith [ht1.2]
  have h1mt2 : 0 < 1 - t2 := by linarith [ht2.2]
  have hden_gt_t2 : t2 < den := by
    have hdeneq : den = t2 + t1 * (1 - t2) := by
      have : t1 + t2 - t1 * t2 = t2 + t1 * (1 - t2) := by ring
      simpa [den] using this
    have hpos : 0 < t1 * (1 - t2) := mul_pos ht1pos h1mt2
    linarith [hdeneq, hpos]
  have hnum_lt : (1 - t1) * t2 < den := by
    have hdeneq : den = (1 - t1) * t2 + t1 := by
      have : t1 + t2 - t1 * t2 = (1 - t1) * t2 + t1 := by ring
      simpa [den] using this
    linarith [hdeneq, ht1pos]
  have hyparam : t2 / den ∈ Set.Ioo (0 : ℝ) 1 := by
    refine ⟨div_pos ht2pos hdenpos, ?_⟩
    have : t2 < den := by simpa [one_mul] using hden_gt_t2
    exact (div_lt_one hdenpos).2 this
  have hxparam : ((1 - t1) * t2) / den ∈ Set.Ioo (0 : ℝ) 1 := by
    have hnum_pos : 0 < (1 - t1) * t2 := mul_pos h1mt1 ht2pos
    refine ⟨div_pos hnum_pos hdenpos, ?_⟩
    have : (1 - t1) * t2 < den := by simpa [one_mul] using hnum_lt
    exact (div_lt_one hdenpos).2 this
  have hxmem : x ∈ openSegment ℝ u v := by
    refine (openSegment_eq_image_lineMap (𝕜 := ℝ) u v).symm ▸ ?_
    exact ⟨((1 - t1) * t2) / den, hxparam, hxline.symm⟩
  have hymem : y ∈ openSegment ℝ u v := by
    refine (openSegment_eq_image_lineMap (𝕜 := ℝ) u v).symm ▸ ?_
    exact ⟨t2 / den, hyparam, hyline.symm⟩
  exact ⟨hxmem, hymem⟩

/-- From a segment whose relative interior contains `x,y`, build a relatively open convex subset. -/
lemma dir2_implies_dir1_take_D_eq_ri_segment {n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin n))} {x y u v : EuclideanSpace ℝ (Fin n)}
    (hsegC : segment ℝ u v ⊆ C)
    (hxri : x ∈ euclideanRelativeInterior n (segment ℝ u v))
    (hyri : y ∈ euclideanRelativeInterior n (segment ℝ u v)) :
    ∃ D : Set (EuclideanSpace ℝ (Fin n)),
      D ⊆ C ∧ Convex ℝ D ∧ euclideanRelativelyOpen n D ∧ x ∈ D ∧ y ∈ D := by
  classical
  refine ⟨euclideanRelativeInterior n (segment ℝ u v), ?_, ?_, ?_, ?_, ?_⟩
  · exact Set.Subset.trans (euclideanRelativeInterior_subset_closure n (segment ℝ u v)).1 hsegC
  · exact convex_euclideanRelativeInterior n (segment ℝ u v) (convex_segment (𝕜 := ℝ) u v)
  ·
    have hri :
        euclideanRelativeInterior n (euclideanRelativeInterior n (segment ℝ u v)) =
          euclideanRelativeInterior n (segment ℝ u v) :=
      (euclidean_closure_closure_eq_and_relativeInterior_relativeInterior_eq n (segment ℝ u v)).2
    simp [euclideanRelativelyOpen, hri]
  · exact hxri
  · exact hyri

/-- From a relatively open convex `D`, extend past `x` and `y` to get a segment in `C`. -/
lemma dir1_implies_dir2_extend_past_x_and_y {n : ℕ}
    {C D : Set (EuclideanSpace ℝ (Fin n))} {x y : EuclideanSpace ℝ (Fin n)}
    (hDC : D ⊆ C) (hDconv : Convex ℝ D) (hDopen : euclideanRelativelyOpen n D)
    (hxD : x ∈ D) (hyD : y ∈ D) (hxy : x ≠ y) :
    ∃ u v : EuclideanSpace ℝ (Fin n),
      u ≠ v ∧
        segment ℝ u v ⊆ C ∧
          x ∈ euclideanRelativeInterior n (segment ℝ u v) ∧
            y ∈ euclideanRelativeInterior n (segment ℝ u v) := by
  have hxri : x ∈ euclideanRelativeInterior n D := by
    rw [hDopen]
    exact hxD
  have hyri : y ∈ euclideanRelativeInterior n D := by
    rw [hDopen]
    exact hyD
  rcases
      exists_mem_openSegment_of_mem_euclideanRelativeInterior (z := x) (x := y) hxri hyD
        (by simpa [eq_comm] using hxy) with ⟨u, huD, hxyu⟩
  rcases
      exists_mem_openSegment_of_mem_euclideanRelativeInterior (z := y) (x := x) hyri hxD hxy with
    ⟨v, hvD, hyxv⟩
  rcases openSegment_of_two_between_relations hxyu hyxv with ⟨hxuv, hyuv⟩
  have huv : u ≠ v := by
    intro huv
    subst huv
    rcases (openSegment_eq_image_lineMap (𝕜 := ℝ) u u ▸ hxuv) with ⟨t, ht, htdef⟩
    rcases (openSegment_eq_image_lineMap (𝕜 := ℝ) u u ▸ hyuv) with ⟨s, hs, hsdef⟩
    have hx' : x = u := by
      simpa [AffineMap.lineMap_apply_module] using htdef.symm
    have hy' : y = u := by
      simpa [AffineMap.lineMap_apply_module] using hsdef.symm
    exact hxy (by simp [hx', hy'])
  have hsegD : segment ℝ u v ⊆ D := hDconv.segment_subset huD hvD
  have hsegC : segment ℝ u v ⊆ C := Set.Subset.trans hsegD hDC
  have hxri' : x ∈ euclideanRelativeInterior n (segment ℝ u v) :=
    openSegment_subset_euclideanRelativeInterior_segment (huv := huv) hxuv
  have hyri' : y ∈ euclideanRelativeInterior n (segment ℝ u v) :=
    openSegment_subset_euclideanRelativeInterior_segment (huv := huv) hyuv
  exact ⟨u, v, huv, hsegC, hxri', hyri'⟩

/-- Text 18.2.1. Let `C` be a convex set and let `x, y` be two distinct points in `C`. The
following two conditions are equivalent:

(1) There exists a relatively open convex subset `D ⊆ C` such that `x ∈ D` and `y ∈ D`.

(2) There exists a line segment `S ⊆ C` such that both `x` and `y` belong to the relative
interior of `S` (i.e. `x, y ∈ ri(S)`). -/
theorem exists_relativelyOpenConvex_subset_iff_exists_segment_mem_relativeInterior {n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin n))} {x y : EuclideanSpace ℝ (Fin n)} (hxy : x ≠ y) :
    (∃ D : Set (EuclideanSpace ℝ (Fin n)),
        D ⊆ C ∧ Convex ℝ D ∧ euclideanRelativelyOpen n D ∧ x ∈ D ∧ y ∈ D) ↔
      (∃ u v : EuclideanSpace ℝ (Fin n),
        u ≠ v ∧
          segment ℝ u v ⊆ C ∧
            x ∈ euclideanRelativeInterior n (segment ℝ u v) ∧
              y ∈ euclideanRelativeInterior n (segment ℝ u v)) := by
  constructor
  · rintro ⟨D, hDC, hDconv, hDopen, hxD, hyD⟩
    exact dir1_implies_dir2_extend_past_x_and_y (C := C) (D := D) hDC hDconv hDopen hxD hyD hxy
  · rintro ⟨u, v, _huv, hsegC, hxri, hyri⟩
    exact dir2_implies_dir1_take_D_eq_ri_segment (C := C) (x := x) (y := y) hsegC hxri hyri

/-- A convex set containing `S₀` and receding along `S₁` contains the mixed convex hull. -/
lemma mixedConvexHull_subset_of_convex_of_subset_of_recedes {n : ℕ}
    {S₀ S₁ Ccand : Set (Fin n → ℝ)} (hCconv : Convex ℝ Ccand) (hS₀ : S₀ ⊆ Ccand)
    (hrec :
      ∀ d ∈ S₁, ∀ x ∈ Ccand, ∀ t : ℝ, 0 ≤ t → x + t • d ∈ Ccand) :
    mixedConvexHull (n := n) S₀ S₁ ⊆ Ccand := by
  intro x hx
  have hx' :
      x ∈ ⋂₀ {C : Set (Fin n → ℝ) |
        Convex ℝ C ∧ S₀ ⊆ C ∧
          ∀ ⦃d⦄, d ∈ S₁ → ∀ ⦃x⦄, x ∈ C → ∀ t : ℝ, 0 ≤ t → x + t • d ∈ C} := by
    simpa [mixedConvexHull] using hx
  have hCand :
      Ccand ∈ {C : Set (Fin n → ℝ) |
        Convex ℝ C ∧ S₀ ⊆ C ∧
          ∀ ⦃d⦄, d ∈ S₁ → ∀ ⦃x⦄, x ∈ C → ∀ t : ℝ, 0 ≤ t → x + t • d ∈ C} := by
    refine ⟨hCconv, hS₀, ?_⟩
    intro d hd x hxC t ht
    exact hrec d hd x hxC t ht
  exact (Set.mem_sInter.1 hx') Ccand hCand

/-- Directions in `S₁` are recession directions of the mixed convex hull. -/
lemma mem_recessionCone_mixedConvexHull_of_mem_directions {n : ℕ}
    {S₀ S₁ : Set (Fin n → ℝ)} {d : Fin n → ℝ} (hd : d ∈ S₁) :
    d ∈ Set.recessionCone (mixedConvexHull (n := n) S₀ S₁) := by
  intro x hx t ht
  have hx' :
      x ∈ ⋂₀ {C : Set (Fin n → ℝ) |
        Convex ℝ C ∧ S₀ ⊆ C ∧
          ∀ ⦃d⦄, d ∈ S₁ → ∀ ⦃x⦄, x ∈ C → ∀ t : ℝ, 0 ≤ t → x + t • d ∈ C} := by
    simpa [mixedConvexHull] using hx
  refine (Set.mem_sInter.2 ?_)
  intro C hC
  rcases hC with ⟨_hCconv, _hS₀C, hrec⟩
  have hxC : x ∈ C := (Set.mem_sInter.1 hx') C ⟨_hCconv, _hS₀C, hrec⟩
  exact hrec hd hxC t ht

/-- Transport a face along the EuclideanSpace equivalence. -/
lemma isFace_image_equiv_fin {n : ℕ} {C C' : Set (Fin n → ℝ)}
    (hC' : IsFace (𝕜 := ℝ) C C') :
    IsFace (𝕜 := ℝ)
      ((EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm '' C)
      ((EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm '' C') := by
  classical
  let e := (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ))
  refine ⟨?_, ?_⟩
  · exact Convex.affine_image (f := e.symm.toAffineMap) hC'.1
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
            (e.toAffineMap) '' openSegment ℝ (e.symm x') (e.symm y') =
              openSegment ℝ x' y' := by
          simpa using
            (image_openSegment (𝕜 := ℝ) (f := e.toAffineMap) (a := e.symm x') (b := e.symm y'))
        have hz' : z' ∈ (e.toAffineMap) '' openSegment ℝ (e.symm x') (e.symm y') := by
          refine ⟨e.symm z', hseg, ?_⟩
          simp
        rw [← himage]
        exact hz'
      have hx'' : x' ∈ C' := hC'.2.left_mem_of_mem_openSegment hx' hy' hz' hseg'
      exact ⟨x', hx'', rfl⟩

/-- Faces in `Fin n → ℝ` satisfy `C' = C ∩ closure C'`. -/
lemma isFace_eq_inter_closure_fin {n : ℕ} {C C' : Set (Fin n → ℝ)}
    (hC' : IsFace (𝕜 := ℝ) C C') (hC'conv : Convex ℝ C') :
    C' = C ∩ closure C' := by
  classical
  let e := (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ))
  let Ce : Set (EuclideanSpace ℝ (Fin n)) := e.symm '' C
  let C'e : Set (EuclideanSpace ℝ (Fin n)) := e.symm '' C'
  have hC'e_face : IsFace (𝕜 := ℝ) Ce C'e :=
    isFace_image_equiv_fin (n := n) (C := C) (C' := C') hC'
  have hC'e_conv : Convex ℝ C'e :=
    Convex.affine_image (f := e.symm.toAffineMap) hC'conv
  have hEqE :
      C'e = Ce ∩ closure C'e :=
    isFace_eq_inter_closure (n := n) (C := Ce) (C' := C'e) hC'e_face hC'e_conv
  have himageC' : e '' C'e = C' := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      simpa using hz
    · intro hx
      exact ⟨e.symm x, ⟨x, hx, rfl⟩, by simp⟩
  have himageC : e '' Ce = C := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      simpa using hz
    · intro hx
      exact ⟨e.symm x, ⟨x, hx, rfl⟩, by simp⟩
  have himageCl : e '' closure C'e = closure C' := by
    have := (Homeomorph.image_closure (h := e.toHomeomorph) (s := C'e))
    simpa [himageC'] using this
  have himageInter :
      e '' (Ce ∩ closure C'e) = C ∩ closure C' := by
    simpa [himageC, himageCl] using (Set.image_inter (f := e) (s := Ce) (t := closure C'e) e.injective)
  have hEqE' : e '' C'e = e '' (Ce ∩ closure C'e) := by
    exact congrArg (fun s => e '' s) hEqE
  have hEqE'' : C' = C ∩ closure C' := by
    calc
      C' = e '' C'e := by
        symm
        exact himageC'
      _ = e '' (Ce ∩ closure C'e) := hEqE'
      _ = C ∩ closure C' := himageInter
  exact hEqE''

/-- If a direction recedes in both `C` and `closure C'`, it recedes in the face `C'`. -/
lemma mem_recessionCone_face_of_mem_recessionCone_of_mem_recessionCone_closure {n : ℕ}
    {S₀ S₁ : Set (Fin n → ℝ)} {C' : Set (Fin n → ℝ)}
    (hC' : IsFace (𝕜 := ℝ) (mixedConvexHull (n := n) S₀ S₁) C') (hC'conv : Convex ℝ C')
    {d : Fin n → ℝ}
    (hdC : d ∈ Set.recessionCone (mixedConvexHull (n := n) S₀ S₁))
    (hdCl : d ∈ Set.recessionCone (closure C')) :
    d ∈ Set.recessionCone C' := by
  classical
  intro x hx t ht
  have hxC : x ∈ mixedConvexHull (n := n) S₀ S₁ := hC'.2.subset hx
  have hxCl : x ∈ closure C' := subset_closure hx
  have hxC' : x + t • d ∈ mixedConvexHull (n := n) S₀ S₁ := hdC (x := x) hxC (t := t) ht
  have hxCl' : x + t • d ∈ closure C' := hdCl (x := x) hxCl (t := t) ht
  have hx' : x + t • d ∈ mixedConvexHull (n := n) S₀ S₁ ∩ closure C' := ⟨hxC', hxCl'⟩
  have hC'eq :
      C' = mixedConvexHull (n := n) S₀ S₁ ∩ closure C' :=
    isFace_eq_inter_closure_fin (C := mixedConvexHull (n := n) S₀ S₁) (C' := C') hC' hC'conv
  rw [hC'eq]
  exact hx'

/-- A ray in a convex set gives a recession direction of its closure. -/
lemma mem_recessionCone_closure_of_exists_ray {n : ℕ} {K : Set (Fin n → ℝ)} {d : Fin n → ℝ}
    (hKconv : Convex ℝ K) (hRay : ∃ x0 ∈ K, ∀ t : ℝ, 0 ≤ t → x0 + t • d ∈ K) :
    d ∈ Set.recessionCone (closure K) := by
  classical
  by_cases hd : d = 0
  · subst hd
    intro x hx t ht
    simpa using hx
  · rcases hRay with ⟨x0, hx0K, hRay⟩
    let e := (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ))
    let C : Set (EuclideanSpace ℝ (Fin n)) := e.symm '' closure K
    have hCne : C.Nonempty := ⟨e.symm x0, ⟨x0, subset_closure hx0K, rfl⟩⟩
    have hCclosed : IsClosed C := by
      exact (Homeomorph.isClosed_image (h := e.symm.toHomeomorph) (s := closure K)).2
        isClosed_closure
    have hCconv : Convex ℝ C := by
      exact Convex.affine_image (f := e.symm.toAffineMap) hKconv.closure
    have hdne : e.symm d ≠ 0 := by
      intro hd'
      apply hd
      have : d = 0 := by
        calc
          d = e (e.symm d) := by simp
          _ = e 0 := by simp [hd']
          _ = 0 := by simp
      exact this
    have hRay' : ∃ x, ∀ t : ℝ, 0 ≤ t → x + t • e.symm d ∈ C := by
      refine ⟨e.symm x0, ?_⟩
      intro t ht
      have hx0t : x0 + t • d ∈ K := hRay t ht
      have hx0t' : x0 + t • d ∈ closure K := subset_closure hx0t
      have hmap : e.symm (x0 + t • d) = e.symm x0 + t • e.symm d := by
        calc
          e.symm (x0 + t • d) = e.symm x0 + e.symm (t • d) := by
            exact e.symm.map_add x0 (t • d)
          _ = e.symm x0 + t • e.symm d := by
            simp [e.symm.map_smul]
      have : e.symm (x0 + t • d) ∈ C := ⟨x0 + t • d, hx0t', rfl⟩
      have hmem := this
      simp [hmap] at hmem
      exact hmem
    have hrec :
        e.symm d ∈ Set.recessionCone C :=
      (recessionCone_of_exists_halfline (n := n) (C := C) hCne hCclosed hCconv hdne hRay').1
    intro x hx t ht
    have hxE : e.symm x ∈ C := ⟨x, hx, rfl⟩
    have hxE' : e.symm x + t • e.symm d ∈ C := hrec (x := e.symm x) hxE (t := t) ht
    rcases hxE' with ⟨y, hy, hyEq⟩
    have hyEq' : y = x + t • d := by
      have hEq : e (e.symm y) = e (e.symm x + t • e.symm d) := by
        simp [hyEq]
      simp [e.map_add, e.map_smul] at hEq
      exact hEq
    have hy' : y ∈ closure K := hy
    have hy'' : x + t • d ∈ closure K := by
      simp [hyEq'] at hy'
      exact hy'
    exact hy''

/-- Monotonicity of the mixed convex hull in both arguments. -/
lemma mixedConvexHull_mono {n : ℕ} {S₀ S₁ T₀ T₁ : Set (Fin n → ℝ)}
    (hS₀ : S₀ ⊆ T₀) (hS₁ : S₁ ⊆ T₁) :
    mixedConvexHull (n := n) S₀ S₁ ⊆ mixedConvexHull (n := n) T₀ T₁ := by
  classical
  refine
    mixedConvexHull_subset_of_convex_of_subset_of_recedes (n := n)
      (S₀ := S₀) (S₁ := S₁) (Ccand := mixedConvexHull (n := n) T₀ T₁)
      (convex_mixedConvexHull (n := n) T₀ T₁) ?_ ?_
  ·
    intro x hx
    have hxT : x ∈ T₀ := hS₀ hx
    have hxray : (0 : Fin n → ℝ) ∈ ray n T₁ := by
      exact (Set.mem_insert_iff).2 (Or.inl rfl)
    have hxadd : x + (0 : Fin n → ℝ) ∈ T₀ + ray n T₁ := by
      exact Set.add_mem_add hxT hxray
    have hxadd' : x ∈ T₀ + ray n T₁ := by simpa using hxadd
    exact (add_ray_subset_mixedConvexHull (n := n) T₀ T₁) hxadd'
  · intro d hd x hx t ht
    have hdT : d ∈ T₁ := hS₁ hd
    exact (mem_recessionCone_mixedConvexHull_of_mem_directions (n := n) (S₀ := T₀) (S₁ := T₁)
      (d := d) hdT) hx (t := t) ht


end Section18
end Chap04
