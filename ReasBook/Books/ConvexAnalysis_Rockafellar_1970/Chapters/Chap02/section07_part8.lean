/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Xinyi Guo, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section01_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section06_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section07_part7

noncomputable section
open scoped Topology

section Chap02
section Section07

/-- The effective domain of `f` is contained in the effective domain of its closure. -/
lemma domf_subset_domcl_of_closure_le {n : Nat} (f : (Fin n → Real) → EReal) :
    (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
        effectiveDomain (Set.univ : Set (Fin n → Real)) f ⊆
      (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
        effectiveDomain (Set.univ : Set (Fin n → Real)) (convexFunctionClosure f) := by
  intro x hx
  have hx' :
      (x : Fin n → Real) ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f := by
    simpa using hx
  have hx_lt : f x < (⊤ : EReal) := by
    have hx'' :
        (x : Fin n → Real) ∈
          {x | x ∈ (Set.univ : Set (Fin n → Real)) ∧ f x < (⊤ : EReal)} := by
      simpa [effectiveDomain_eq] using hx'
    exact hx''.2
  have hle : convexFunctionClosure f x ≤ f x :=
    (convexFunctionClosure_le_self (f := f)) x
  have hxcl_lt : convexFunctionClosure f x < (⊤ : EReal) := lt_of_le_of_lt hle hx_lt
  have hxcl :
      (x : Fin n → Real) ∈
        {x |
          x ∈ (Set.univ : Set (Fin n → Real)) ∧
            convexFunctionClosure f x < (⊤ : EReal)} := by
    exact ⟨by simp, hxcl_lt⟩
  have hxcl' :
      (x : Fin n → Real) ∈
        effectiveDomain (Set.univ : Set (Fin n → Real)) (convexFunctionClosure f) := by
    simpa [effectiveDomain_eq] using hxcl
  simpa using hxcl'

/-- The effective domain of the closure lies in the closure of the effective domain. -/
lemma domcl_subset_closure_domf {n : Nat} {f : (Fin n → Real) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
        effectiveDomain (Set.univ : Set (Fin n → Real)) (convexFunctionClosure f) ⊆
      closure
        ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → Real)) f) := by
  classical
  intro x hx
  have hx' :
      (x : Fin n → Real) ∈
        effectiveDomain (Set.univ : Set (Fin n → Real)) (convexFunctionClosure f) := by
    simpa using hx
  have hx'' :
      (x : Fin n → Real) ∈
        (LinearMap.fst ℝ (Fin n → Real) Real) ''
          epigraph (S := (Set.univ : Set (Fin n → Real))) (convexFunctionClosure f) := by
    simpa [effectiveDomain_eq_image_fst] using hx'
  have hbot : ∀ x, f x ≠ (⊥ : EReal) := by
    intro x
    exact hf.2.2 x (by simp)
  have hepi :
      epigraph (S := (Set.univ : Set (Fin n → Real))) (convexFunctionClosure f) =
        closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) :=
    (epigraph_convexFunctionClosure_eq_closure_epigraph (f := f) hbot).1
  have hx''' :
      (x : Fin n → Real) ∈
        (LinearMap.fst ℝ (Fin n → Real) Real) ''
          closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) := by
    simpa [hepi] using hx''
  have hcont :
      Continuous (LinearMap.fst ℝ (Fin n → Real) Real) :=
    (LinearMap.fst ℝ (Fin n → Real) Real).continuous_of_finiteDimensional
  have hsubset :=
    image_closure_subset_closure_image
      (f := LinearMap.fst ℝ (Fin n → Real) Real)
      (s := epigraph (S := (Set.univ : Set (Fin n → Real))) f) hcont
  have hxcl :
      (x : Fin n → Real) ∈
        closure
          ((LinearMap.fst ℝ (Fin n → Real) Real) ''
            epigraph (S := (Set.univ : Set (Fin n → Real))) f) := by
    exact hsubset hx'''
  have hxcl' :
      (x : Fin n → Real) ∈
        closure (effectiveDomain (Set.univ : Set (Fin n → Real)) f) := by
    simpa [effectiveDomain_eq_image_fst] using hxcl
  have hxpre :
      x ∈ (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
        closure (effectiveDomain (Set.univ : Set (Fin n → Real)) f) := by
    simpa using hxcl'
  have hopen :
      IsOpenMap (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) := by
    simpa using (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).isOpenMap
  have hcont' :
      Continuous (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) := by
    simpa using (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).continuous
  have hxcl'' :
      x ∈
        closure
          ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → Real)) f) := by
    simpa [hopen.preimage_closure_eq_closure_preimage hcont'
      (s := effectiveDomain (Set.univ : Set (Fin n → Real)) f)] using hxpre
  exact hxcl''

/-- If `domcl` lies in `closure domf`, then it lies in `domf` or its relative boundary. -/
lemma domcl_subset_domf_union_rbd {n : Nat}
    {domf domcl : Set (EuclideanSpace Real (Fin n))} (hsubset : domcl ⊆ closure domf) :
    domcl ⊆ domf ∪ euclideanRelativeBoundary n domf := by
  intro x hx
  have hxcl : x ∈ closure domf := hsubset hx
  by_cases hxdom : x ∈ domf
  · exact Or.inl hxdom
  · have hri_sub : euclideanRelativeInterior n domf ⊆ domf :=
      (euclideanRelativeInterior_subset_closure n domf).1
    have hxnotri : x ∉ euclideanRelativeInterior n domf := by
      intro hxri
      exact hxdom (hri_sub hxri)
    have hxrbd : x ∈ euclideanRelativeBoundary n domf := by
      exact ⟨hxcl, hxnotri⟩
    exact Or.inr hxrbd

/-- Equal closures for `domf` and `domcl` follow from the two inclusions. -/
lemma closure_domcl_eq_domf {n : Nat}
    {domf domcl : Set (EuclideanSpace Real (Fin n))} (hdomf : domf ⊆ domcl)
    (hdomcl : domcl ⊆ closure domf) :
    closure domcl = closure domf := by
  have h1 : closure domf ⊆ closure domcl := closure_mono hdomf
  have h2 : closure domcl ⊆ closure (closure domf) := closure_mono hdomcl
  have h2' : closure domcl ⊆ closure domf := by
    simpa [closure_closure] using h2
  exact le_antisymm h2' h1

/-- Relative interiors coincide under closure equality for convex sets. -/
lemma ri_domcl_eq_domf {n : Nat}
    {domf domcl : Set (EuclideanSpace Real (Fin n))} (hconvf : Convex Real domf)
    (hconvcl : Convex Real domcl) (hcl : closure domcl = closure domf) :
    euclideanRelativeInterior n domcl = euclideanRelativeInterior n domf := by
  exact (euclideanRelativeInterior_eq_of_closure_eq n domcl domf hconvcl hconvf) hcl

/-- Corollary 7.4.1. If `f` is a proper convex function, then `dom (cl f)` differs from
`dom f` at most by including some additional relative boundary points of `dom f`.
In particular, `dom (cl f)` and `dom f` have the same closure and relative interior, as well
as the same dimension. -/
theorem convexFunctionClosure_effectiveDomain_subset_relativeBoundary_and_same_closure_ri_dim
    {n : Nat} {f : (Fin n → Real) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    let domf : Set (EuclideanSpace Real (Fin n)) :=
      (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
        effectiveDomain (Set.univ : Set (Fin n → Real)) f
    let domcl : Set (EuclideanSpace Real (Fin n)) :=
      (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
        effectiveDomain (Set.univ : Set (Fin n → Real)) (convexFunctionClosure f)
    domf ⊆ domcl ∧
      domcl ⊆ domf ∪ euclideanRelativeBoundary n domf ∧
      closure domcl = closure domf ∧
      euclideanRelativeInterior n domcl = euclideanRelativeInterior n domf ∧
      Module.finrank Real (affineSpan Real domcl).direction =
        Module.finrank Real (affineSpan Real domf).direction := by
  classical
  set domf : Set (EuclideanSpace Real (Fin n)) :=
    (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
      effectiveDomain (Set.univ : Set (Fin n → Real)) f with hdomf
  set domcl : Set (EuclideanSpace Real (Fin n)) :=
    (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
      effectiveDomain (Set.univ : Set (Fin n → Real)) (convexFunctionClosure f) with hdomcl
  have hdomf_sub : domf ⊆ domcl := by
    simpa [hdomf, hdomcl] using (domf_subset_domcl_of_closure_le (f := f))
  have hdomcl_sub : domcl ⊆ closure domf := by
    simpa [hdomf, hdomcl] using (domcl_subset_closure_domf (f := f) hf)
  have hdomcl_union : domcl ⊆ domf ∪ euclideanRelativeBoundary n domf :=
    domcl_subset_domf_union_rbd (domf := domf) (domcl := domcl) hdomcl_sub
  have hclosure : closure domcl = closure domf :=
    closure_domcl_eq_domf (domf := domf) (domcl := domcl) hdomf_sub hdomcl_sub
  have hconv_domf : Convex Real domf := by
    have hconv_eff :
        Convex Real (effectiveDomain (Set.univ : Set (Fin n → Real)) f) :=
      effectiveDomain_convex (S := (Set.univ : Set (Fin n → Real))) (f := f) hf.1
    simpa [hdomf] using
      (Convex.linear_preimage
        (s := effectiveDomain (Set.univ : Set (Fin n → Real)) f) hconv_eff
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).toLinearMap)
  have hproper_cl :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (convexFunctionClosure f) :=
    (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri (f := f) hf).1.2
  have hconv_domcl : Convex Real domcl := by
    have hconv_eff :
        Convex Real
          (effectiveDomain (Set.univ : Set (Fin n → Real)) (convexFunctionClosure f)) :=
      effectiveDomain_convex (S := (Set.univ : Set (Fin n → Real)))
        (f := convexFunctionClosure f) hproper_cl.1
    simpa [hdomcl] using
      (Convex.linear_preimage
        (s := effectiveDomain (Set.univ : Set (Fin n → Real)) (convexFunctionClosure f))
        hconv_eff (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).toLinearMap)
  have hri :
      euclideanRelativeInterior n domcl = euclideanRelativeInterior n domf :=
    ri_domcl_eq_domf (domf := domf) (domcl := domcl) hconv_domf hconv_domcl hclosure
  have hspan : affineSpan Real domcl = affineSpan Real domf := by
    calc
      affineSpan Real domcl = affineSpan Real (closure domcl) := by
        symm
        simp [affineSpan_closure_eq n domcl]
      _ = affineSpan Real (closure domf) := by simp [hclosure]
      _ = affineSpan Real domf := by
        simp [affineSpan_closure_eq n domf]
  refine ⟨hdomf_sub, hdomcl_union, hclosure, hri, ?_⟩
  simpa using congrArg (fun s => Module.finrank Real s.direction) hspan

/-- Affine sets have full relative interior and empty relative boundary. -/
lemma ri_eq_and_boundary_empty_of_isAffineSet {n : Nat}
    {C : Set (EuclideanSpace Real (Fin n))}
    (hC :
      IsAffineSet n
        ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) '' C)) :
    euclideanRelativeInterior n C = C ∧ euclideanRelativeBoundary n C = ∅ := by
  classical
  let e : (Fin n → Real) →ᵃ[Real] EuclideanSpace Real (Fin n) :=
    (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm.toLinearMap.toAffineMap
  rcases
      (isAffineSet_iff_affineSubspace n
            ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) '' C)).1 hC with
    ⟨s, hs⟩
  let s' : AffineSubspace Real (EuclideanSpace Real (Fin n)) := s.map e
  have hs' : (s' : Set (EuclideanSpace Real (Fin n))) = C := by
    ext x; constructor
    · intro hx
      rcases hx with ⟨y, hy, rfl⟩
      have hy' :
          y ∈ (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) '' C := by
        simpa [hs] using hy
      rcases hy' with ⟨z, hz, rfl⟩
      simpa [e] using hz
    · intro hx
      have hx' :
          (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) x ∈
            (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) '' C := by
        exact ⟨x, hx, rfl⟩
      have hx'' :
          (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) x ∈ s := by
        simpa [hs.symm] using hx'
      refine ⟨(fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) x, hx'', ?_⟩
      simp [e]
  have hrel :
      euclideanRelativelyOpen n (s' : Set (EuclideanSpace Real (Fin n))) ∧
        IsClosed (s' : Set (EuclideanSpace Real (Fin n))) :=
    affineSubspace_relativelyOpen_closed n s'
  have hri : euclideanRelativeInterior n C = C := by
    simpa [hs'] using hrel.1
  have hcl : closure C = C := by
    simpa [hs'] using hrel.2.closure_eq
  have hrbd : euclideanRelativeBoundary n C = ∅ := by
    simp [euclideanRelativeBoundary, hri, hcl]
  exact ⟨hri, hrbd⟩

/-- For affine effective domain, the effective domain of the closure coincides. -/
lemma domcl_eq_domf_of_affine_effectiveDomain {n : Nat} {f : (Fin n → Real) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    (haff : IsAffineSet n (effectiveDomain (Set.univ : Set (Fin n → Real)) f)) :
    let domf : Set (EuclideanSpace Real (Fin n)) :=
      (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
        effectiveDomain (Set.univ : Set (Fin n → Real)) f
    let domcl : Set (EuclideanSpace Real (Fin n)) :=
      (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
        effectiveDomain (Set.univ : Set (Fin n → Real)) (convexFunctionClosure f)
    domcl = domf := by
  classical
  set domf : Set (EuclideanSpace Real (Fin n)) :=
    (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
      effectiveDomain (Set.univ : Set (Fin n → Real)) f with hdomf
  set domcl : Set (EuclideanSpace Real (Fin n)) :=
    (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
      effectiveDomain (Set.univ : Set (Fin n → Real)) (convexFunctionClosure f) with hdomcl
  rcases
      (by
          simpa [hdomf.symm, hdomcl.symm] using
            (convexFunctionClosure_effectiveDomain_subset_relativeBoundary_and_same_closure_ri_dim
              (f := f) hf)) with
    ⟨hdomf_sub, hdomcl_sub, -, -, -⟩
  have himage_domf :
      (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) '' domf =
        effectiveDomain (Set.univ : Set (Fin n → Real)) f := by
    ext x; constructor
    · intro hx
      rcases hx with ⟨y, hy, rfl⟩
      simpa [hdomf] using hy
    · intro hx
      refine ⟨(EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x, ?_, ?_⟩
      · simpa [hdomf] using
          (show (fun y : EuclideanSpace Real (Fin n) => (y : Fin n → Real))
              ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x) ∈
              effectiveDomain (Set.univ : Set (Fin n → Real)) f from
            by simpa using hx)
      · simp
  have haff_domf :
      IsAffineSet n
        ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) '' domf) := by
    simpa [himage_domf] using haff
  have hrbd : euclideanRelativeBoundary n domf = ∅ :=
    (ri_eq_and_boundary_empty_of_isAffineSet (n := n) (C := domf) haff_domf).2
  have hdomcl_sub' : domcl ⊆ domf := by
    simpa [hrbd] using hdomcl_sub
  exact subset_antisymm hdomcl_sub' hdomf_sub

/-- For affine effective domain, the closure agrees with the function everywhere. -/
lemma convexFunctionClosure_eq_of_affine_effectiveDomain {n : Nat} {f : (Fin n → Real) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    (haff : IsAffineSet n (effectiveDomain (Set.univ : Set (Fin n → Real)) f)) :
    convexFunctionClosure f = f := by
  classical
  set domf : Set (EuclideanSpace Real (Fin n)) :=
    (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
      effectiveDomain (Set.univ : Set (Fin n → Real)) f with hdomf
  set domcl : Set (EuclideanSpace Real (Fin n)) :=
    (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
      effectiveDomain (Set.univ : Set (Fin n → Real)) (convexFunctionClosure f) with hdomcl
  have hdomcl_eq : domcl = domf := by
    simpa [hdomf, hdomcl] using
      (domcl_eq_domf_of_affine_effectiveDomain (f := f) hf haff)
  have himage_domf :
      (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) '' domf =
        effectiveDomain (Set.univ : Set (Fin n → Real)) f := by
    ext x; constructor
    · intro hx
      rcases hx with ⟨y, hy, rfl⟩
      simpa [hdomf] using hy
    · intro hx
      refine ⟨(EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x, ?_, ?_⟩
      · simpa [hdomf] using
          (show (fun y : EuclideanSpace Real (Fin n) => (y : Fin n → Real))
              ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x) ∈
              effectiveDomain (Set.univ : Set (Fin n → Real)) f from
            by simpa using hx)
      · simp
  have haff_domf :
      IsAffineSet n
        ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) '' domf) := by
    simpa [himage_domf] using haff
  have hri : euclideanRelativeInterior n domf = domf :=
    (ri_eq_and_boundary_empty_of_isAffineSet (n := n) (C := domf) haff_domf).1
  funext x
  let x' : EuclideanSpace Real (Fin n) :=
    (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x
  have hx'coe : (x' : Fin n → Real) = x := by
    simp [x']
  by_cases hx' : x' ∈ domf
  · have hxri : x' ∈ euclideanRelativeInterior n domf := by
      simpa [hri] using hx'
    have hxri' :
        x' ∈ euclideanRelativeInterior n
          ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → Real)) f) := by
      simpa [hdomf] using hxri
    have hEq := (convexFunctionClosure_eq_on_ri (f := f) hf) x' hxri'
    simpa [hx'coe] using hEq
  · have hxnot' : ¬ f (x' : Fin n → Real) < (⊤ : EReal) := by
      simpa [hdomf, effectiveDomain_eq] using hx'
    have hxnot : ¬ f x < (⊤ : EReal) := by
      simpa [hx'coe] using hxnot'
    have hfx_top : f x = (⊤ : EReal) := by
      by_contra hne
      exact hxnot ((lt_top_iff_ne_top).2 hne)
    have hxcl : x' ∉ domcl := by
      simpa [hdomcl_eq] using hx'
    have hxcl_not' : ¬ convexFunctionClosure f (x' : Fin n → Real) < (⊤ : EReal) := by
      simpa [hdomcl, effectiveDomain_eq] using hxcl
    have hxcl_not : ¬ convexFunctionClosure f x < (⊤ : EReal) := by
      simpa [hx'coe] using hxcl_not'
    have hcl_top : convexFunctionClosure f x = (⊤ : EReal) := by
      by_contra hne
      exact hxcl_not ((lt_top_iff_ne_top).2 hne)
    exact hcl_top.trans hfx_top.symm

/-- Corollary 7.4.2. If `f` is a proper convex function such that `dom f` is an affine set
(which holds in particular if `f` is finite throughout `ℝ^n`), then `f` is closed. -/
theorem properConvexFunction_closed_of_affine_effectiveDomain {n : Nat}
    {f : (Fin n → Real) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    (haff : IsAffineSet n (effectiveDomain (Set.univ : Set (Fin n → Real)) f)) :
    ClosedConvexFunction f := by
  have hclosed_cl : ClosedConvexFunction (convexFunctionClosure f) :=
    (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri (f := f) hf).1.1
  have hcl_eq : convexFunctionClosure f = f :=
    convexFunctionClosure_eq_of_affine_effectiveDomain (f := f) hf haff
  simpa [hcl_eq] using hclosed_cl

/- Remark 7.0.24: Theorems 7.2 and 7.4 imply that a convex function `f` is always lower
semicontinuous except perhaps at relative boundary points of `dom f`. In fact, `f` is
continuous relative to `ri (dom f)` (see §10). -/
/-- A lower semicontinuous minorant that agrees at a point transfers lsc. -/
lemma lowerSemicontinuousAt_of_le_of_eq {α β : Type*} [TopologicalSpace α] [Preorder β]
    {f g : α → β} {x : α} (hg : LowerSemicontinuousAt g x) (hle : g ≤ f)
    (hxeq : g x = f x) : LowerSemicontinuousAt f x := by
  intro y hy
  have hy' : y < g x := by
    simpa [hxeq] using hy
  have h := hg y hy'
  refine h.mono ?_
  intro x' hx'
  exact lt_of_lt_of_le hx' (hle x')

theorem convexFunction_lowerSemicontinuousAt_on_ri_effectiveDomain {n : Nat}
    {f : (Fin n → Real) → EReal} (hf : ConvexFunction f) :
    ∀ x ∈
      euclideanRelativeInterior n
        ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → Real)) f),
      LowerSemicontinuousAt f x := by
  classical
  intro x hxri
  by_cases hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f
  · have hclosed :
        ClosedConvexFunction (convexFunctionClosure f) :=
      (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri
          (f := f) hproper).1.1
    have hagree :
        convexFunctionClosure f x = f x :=
      (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri
          (f := f) hproper).2 x hxri
    have hle : convexFunctionClosure f ≤ f := convexFunctionClosure_le_self (f := f)
    have hlscl : LowerSemicontinuousAt (convexFunctionClosure f) x := (hclosed.2 x)
    exact lowerSemicontinuousAt_of_le_of_eq hlscl hle hagree
  · have hconv : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) f := by
      simpa [ConvexFunction] using hf
    have himproper :
        ImproperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f := ⟨hconv, hproper⟩
    have hbot :
        f x = (⊥ : EReal) :=
      improperConvexFunctionOn_eq_bot_on_ri_effectiveDomain (f := f) himproper x hxri
    have hlscl :
        LowerSemicontinuousAt (fun _ : (Fin n → Real) => (⊥ : EReal)) x :=
      (closed_improper_const_bot (n := n)).1.2 x
    have hle : (fun _ : (Fin n → Real) => (⊥ : EReal)) ≤ f := by
      intro x
      exact bot_le
    exact
      lowerSemicontinuousAt_of_le_of_eq hlscl hle (by simpa using hbot.symm)

/- Proper convex functions are continuous on the relative interior of their effective domain. -/
/-- Proper convex functions are finite on the relative interior of their effective domain. -/
lemma properConvexFunctionOn_ne_top_on_ri_effectiveDomain {n : Nat}
    {f : (Fin n → Real) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    ∀ x ∈
      euclideanRelativeInterior n
        ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → Real)) f),
      f x ≠ (⊥ : EReal) ∧ f x ≠ (⊤ : EReal) := by
  intro x hxri
  have hx' :
      x ∈
        ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → Real)) f) :=
    (euclideanRelativeInterior_subset_closure n
        ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → Real)) f)).1 hxri
  have hxdom :
      (x : Fin n → Real) ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f := by
    simpa using hx'
  have hbot : f x ≠ (⊥ : EReal) := hf.2.2 x (by simp)
  have htop : f x ≠ (⊤ : EReal) :=
    mem_effectiveDomain_imp_ne_top (S := Set.univ) (f := f) hxdom
  exact ⟨hbot, htop⟩

/-- The `toReal` of a proper convex function is convex on its effective domain. -/
lemma convexOn_toReal_on_effectiveDomain {n : Nat} {f : (Fin n → Real) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    ConvexOn ℝ (effectiveDomain (Set.univ : Set (Fin n → Real)) f) (fun x => (f x).toReal) := by
  classical
  set C : Set (Fin n → Real) := effectiveDomain (Set.univ : Set (Fin n → Real)) f
  have hconvC : Convex ℝ C := by
    simpa [C] using
      (effectiveDomain_convex (S := (Set.univ : Set (Fin n → Real))) (f := f) hf.1)
  have hconvf : ConvexFunctionOn C f := by
    simpa [C] using
      (convexFunctionOn_iff_convexFunctionOn_effectiveDomain
        (S := (Set.univ : Set (Fin n → Real))) (f := f)).1 hf.1
  have hnotbot : ∀ x ∈ C, f x ≠ (⊥ : EReal) := by
    intro x hx
    exact hf.2.2 x (by simp)
  have hseg :=
    (convexFunctionOn_iff_segment_inequality (C := C) (f := f) hconvC hnotbot).1 hconvf
  refine (convexOn_iff_forall_pos).2 ?_
  refine ⟨hconvC, ?_⟩
  intro x hx y hy a b ha hb hab
  have hb_lt : b < 1 := by linarith
  have ha_eq : a = 1 - b := by linarith
  have hseg' :
      f ((1 - b) • x + b • y) ≤
        ((1 - b : Real) : EReal) * f x + ((b : Real) : EReal) * f y :=
    hseg x (by simpa [C] using hx) y (by simpa [C] using hy) b hb hb_lt
  have hbot :
      f ((1 - b) • x + b • y) ≠ (⊥ : EReal) := by
    exact hf.2.2 _ (by simp)
  have hfx_bot : f x ≠ (⊥ : EReal) := hf.2.2 x (by simp)
  have hfy_bot : f y ≠ (⊥ : EReal) := hf.2.2 y (by simp)
  have hfx_top : f x ≠ (⊤ : EReal) :=
    mem_effectiveDomain_imp_ne_top (S := Set.univ) (f := f) (by simpa [C] using hx)
  have hfy_top : f y ≠ (⊤ : EReal) :=
    mem_effectiveDomain_imp_ne_top (S := Set.univ) (f := f) (by simpa [C] using hy)
  have hfx_coe : ((f x).toReal : EReal) = f x :=
    EReal.coe_toReal hfx_top hfx_bot
  have hfy_coe : ((f y).toReal : EReal) = f y :=
    EReal.coe_toReal hfy_top hfy_bot
  have hsum :
      ((1 - b : Real) : EReal) * f x + ((b : Real) : EReal) * f y =
        (( (1 - b) * (f x).toReal + b * (f y).toReal : Real) : EReal) := by
    calc
      ((1 - b : Real) : EReal) * f x + ((b : Real) : EReal) * f y =
          ((1 - b : Real) : EReal) * ((f x).toReal : EReal) +
            ((b : Real) : EReal) * ((f y).toReal : EReal) := by
            simp [hfx_coe, hfy_coe]
      _ = (( (1 - b) * (f x).toReal : Real) : EReal) +
            ((b * (f y).toReal : Real) : EReal) := by
            simp [EReal.coe_mul]
      _ = (( (1 - b) * (f x).toReal + b * (f y).toReal : Real) : EReal) := by
            simp
  have hsum_not_top :
      ((1 - b : Real) : EReal) * f x + ((b : Real) : EReal) * f y ≠ (⊤ : EReal) := by
    rw [hsum]
    exact EReal.coe_ne_top _
  have hsum_toReal :
      (((1 - b : Real) : EReal) * f x + ((b : Real) : EReal) * f y).toReal =
        (1 - b) * (f x).toReal + b * (f y).toReal := by
    have hsum' := congrArg EReal.toReal hsum
    simpa using hsum'
  have hineq :
      (f ((1 - b) • x + b • y)).toReal ≤
        ( (1 - b) * (f x).toReal + b * (f y).toReal ) := by
    have hsum_toReal' :
        (((1 - (b : EReal)) * f x + (b : EReal) * f y).toReal =
          (1 - b) * (f x).toReal + b * (f y).toReal) := by
      simpa [EReal.coe_sub] using hsum_toReal
    have h := EReal.toReal_le_toReal hseg' hbot hsum_not_top
    simpa [hsum_toReal'] using h
  simpa [ha_eq] using hineq

/-- Lift continuity of `toReal ∘ f` to continuity of `f` on finite-valued sets. -/
lemma continuousOn_ereal_of_toReal {α : Type*} [TopologicalSpace α] {f : α → EReal}
    {s : Set α} (hcont : ContinuousOn (fun x => (f x).toReal) s)
    (hfinite : ∀ x ∈ s, f x ≠ (⊥ : EReal) ∧ f x ≠ (⊤ : EReal)) :
    ContinuousOn f s := by
  have hcont' :
      ContinuousOn (fun x => ((f x).toReal : EReal)) s := by
    exact continuous_coe_real_ereal.comp_continuousOn hcont
  have hEq :
      Set.EqOn (fun x => f x) (fun x => ((f x).toReal : EReal)) s := by
    intro x hx
    have hne_bot : f x ≠ (⊥ : EReal) := (hfinite x hx).1
    have hne_top : f x ≠ (⊤ : EReal) := (hfinite x hx).2
    exact (EReal.coe_toReal hne_top hne_bot).symm
  exact hcont'.congr hEq

/- Relative interior continuity for real-valued convex functions (Section 10 placeholder). -/
/-- In full dimension, relative interior equals interior, giving continuity for convex maps. -/
lemma convexOn_continuousOn_ri_of_affineSpan_eq_univ {n : Nat}
    {C : Set (EuclideanSpace Real (Fin n))} {g : EuclideanSpace Real (Fin n) → ℝ}
    (hg : ConvexOn ℝ C g)
    (hspan : (affineSpan Real C : Set (EuclideanSpace Real (Fin n))) = Set.univ) :
    ContinuousOn g (euclideanRelativeInterior n C) := by
  have hri :
      euclideanRelativeInterior n C = interior C :=
    euclideanRelativeInterior_eq_interior_of_affineSpan_eq_univ n C hspan
  simpa [hri] using (ConvexOn.continuousOn_interior (C := C) (f := g) hg)

/-- Affine equivalences transport continuity on relative interiors. -/
lemma continuousOn_ri_of_affineEquiv {n : Nat}
    {C : Set (EuclideanSpace Real (Fin n))} {g : EuclideanSpace Real (Fin n) → ℝ}
    (e : EuclideanSpace Real (Fin n) ≃ᵃ[Real] EuclideanSpace Real (Fin n))
    (hcont :
      ContinuousOn (fun x => g (e.symm x)) (euclideanRelativeInterior n (e '' C))) :
    ContinuousOn g (euclideanRelativeInterior n C) := by
  have hcont_e :
      ContinuousOn (fun x => e x) (euclideanRelativeInterior n C) :=
    (AffineEquiv.continuous_of_finiteDimensional (f := e)).continuousOn
  have hmap :
      Set.MapsTo (fun x => e x) (euclideanRelativeInterior n C)
        (euclideanRelativeInterior n (e '' C)) := by
    intro x hx
    have hx' : e x ∈ e '' euclideanRelativeInterior n C := ⟨x, hx, rfl⟩
    simpa [euclideanRelativeInterior_image_affineEquiv (n := n) (C := C) (e := e)] using hx'
  have hcomp :
      ContinuousOn (fun x => g (e.symm (e x))) (euclideanRelativeInterior n C) :=
    hcont.comp (s := euclideanRelativeInterior n C) hcont_e hmap
  simpa using hcomp

/-- The coordinate subspace as a submodule. -/
def coordinateSubmodule (n m : Nat) : Submodule Real (EuclideanSpace Real (Fin n)) :=
  { carrier := coordinateSubspace n m
    zero_mem' := by
      intro i hi
      simp
    add_mem' := by
      intro x y hx hy i hi
      have hx' := hx i hi
      have hy' := hy i hi
      simp [hx', hy']
    smul_mem' := by
      intro r x hx i hi
      have hx' := hx i hi
      simp [hx'] }

/-- Coordinate-subspace affine equivalence using extend-by-zero and restriction. -/
noncomputable def coordinateSubspace_affineEquiv {n m : Nat} (hmn : m ≤ n) :
    EuclideanSpace Real (Fin m) ≃ᵃ[Real] (coordinateSubmodule n m) := by
  classical
  let e_m : EuclideanSpace Real (Fin m) ≃L[Real] (Fin m → Real) :=
    EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)
  let e_n : EuclideanSpace Real (Fin n) ≃L[Real] (Fin n → Real) :=
    EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)
  let A' : (Fin m → Real) →ₗ[Real] (Fin n → Real) :=
    Function.ExtendByZero.linearMap Real (Fin.castLE hmn)
  let g' : (Fin n → Real) →ₗ[Real] (Fin m → Real) :=
    LinearMap.funLeft Real Real (Fin.castLE hmn)
  let A : EuclideanSpace Real (Fin m) →ₗ[Real] EuclideanSpace Real (Fin n) :=
    e_n.symm.toLinearMap.comp (A'.comp e_m.toLinearMap)
  let g : EuclideanSpace Real (Fin n) →ₗ[Real] EuclideanSpace Real (Fin m) :=
    e_m.symm.toLinearMap.comp (g'.comp e_n.toLinearMap)
  have hleft' : Function.LeftInverse g' A' := by
    intro x
    ext i
    have hcomp :=
      Function.extend_comp (f := Fin.castLE hmn) (g := x) (e' := fun _ => (0 : Real))
        (hf := Fin.castLE_injective hmn)
    have hcomp' := congrArg (fun h => h i) hcomp
    simpa [A', g', LinearMap.funLeft_apply] using hcomp'
  have hleft : Function.LeftInverse g A := by
    intro x
    apply e_m.injective
    have hcomp : e_m (g (A x)) = g' (A' (e_m x)) := by
      have h1 : e_m (g (A x)) = g' (e_n (A x)) := by
        simp [g, LinearMap.comp_apply]
      have h2 : e_n (A x) = A' (e_m x) := by
        simp [A, LinearMap.comp_apply]
      simpa [h2] using h1
    simpa [hcomp] using (hleft' (e_m x))
  have hrange : LinearMap.range A = coordinateSubmodule n m := by
    ext x; constructor
    · rintro ⟨y, rfl⟩
      intro i hi
      have hi' : ¬ ∃ j : Fin m, Fin.castLE hmn j = i := by
        intro h
        rcases h with ⟨j, hj⟩
        have hval : (j : Nat) = (i : Nat) := by
          simpa using congrArg Fin.val hj
        have hjlt : (i : Nat) < m := by
          simpa [hval] using j.is_lt
        exact (not_lt_of_ge hi) hjlt
      have hAy :
          (e_n (A y)) i = 0 := by
        have hAy' : e_n (A y) = A' (e_m y) := by
          simp [A, LinearMap.comp_apply]
        have hAy'' := congrArg (fun f => f i) hAy'
        simpa [A', Function.extend_apply', hi'] using hAy''
      simpa [e_n, EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv] using hAy
    · intro hx
      refine ⟨g x, ?_⟩
      apply e_n.injective
      have hAg : e_n (A (g x)) = A' (g' (e_n x)) := by
        have h1 : e_n (A (g x)) = A' (e_m (g x)) := by
          simp [A, LinearMap.comp_apply]
        have h2 : e_m (g x) = g' (e_n x) := by
          simp [g, LinearMap.comp_apply]
        simpa [h2] using h1
      apply funext
      intro i
      by_cases hi : (i : Nat) < m
      · let j : Fin m := ⟨i, hi⟩
        have hij : Fin.castLE hmn j = i := by
          ext
          rfl
        have hA' :
            (A' (g' (e_n x))) i = (e_n x) i := by
          have hA'' :
              (A' (g' (e_n x))) (Fin.castLE hmn j) =
                (e_n x) (Fin.castLE hmn j) := by
            simp [A', g', LinearMap.funLeft_apply, Fin.castLE_injective hmn]
          simpa [hij] using hA''
        simpa [hAg] using hA'
      · have hi' : m ≤ (i : Nat) := le_of_not_gt hi
        have hnot : ¬ ∃ j : Fin m, Fin.castLE hmn j = i := by
          intro h
          rcases h with ⟨j, hj⟩
          have hval : (j : Nat) = (i : Nat) := by
            simpa using congrArg Fin.val hj
          have hjlt : (i : Nat) < m := by
            simpa [hval] using j.is_lt
          exact hi hjlt
        have hx' : (e_n x) i = 0 := by
          have hx'' : x i = 0 := hx i hi'
          simpa [e_n, EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv] using hx''
        have hA' :
            (A' (g' (e_n x))) i = 0 := by
          simp [A', g', Function.extend_apply', hnot]
        simpa [hAg, hx'] using hA'
  let e0 : EuclideanSpace Real (Fin m) ≃ₗ[Real] LinearMap.range A :=
    LinearEquiv.ofLeftInverse (f := A) (g := g) hleft
  let e1 : LinearMap.range A ≃ₗ[Real] coordinateSubmodule n m :=
    LinearEquiv.ofEq _ _ hrange
  exact (e0.trans e1).toAffineEquiv

/-- Pulling back a full-dimensional set from the coordinate subspace gives full affine span. -/
lemma affineSpan_preimage_eq_univ {n m : Nat} (hmn : m ≤ n)
    {C : Set (EuclideanSpace Real (Fin n))}
    (hspan :
      (affineSpan Real C : Set (EuclideanSpace Real (Fin n))) = coordinateSubspace n m) :
    (affineSpan Real
        ((coordinateSubspace_affineEquiv (n := n) (m := m) hmn).symm ''
          (Subtype.val ⁻¹' C)) : Set (EuclideanSpace Real (Fin m))) = Set.univ := by
  classical
  let e := coordinateSubspace_affineEquiv (n := n) (m := m) hmn
  let Csub : Set (coordinateSubmodule n m) := Subtype.val ⁻¹' C
  have hCsub : C ⊆ coordinateSubspace n m := by
    intro x hx
    have hx' : x ∈ (affineSpan Real C : Set (EuclideanSpace Real (Fin n))) :=
      subset_affineSpan (k := Real) (s := C) hx
    simpa [hspan] using hx'
  have himage :
      (fun x : coordinateSubmodule n m => (x : EuclideanSpace Real (Fin n))) '' Csub = C := by
    ext x; constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hCsub hx⟩, hx, rfl⟩
  have hmap :
      (affineSpan Real Csub).map ((coordinateSubmodule n m).subtype.toAffineMap) =
        affineSpan Real C := by
    simpa [himage] using
      (AffineSubspace.map_span (k := Real)
        (f := (coordinateSubmodule n m).subtype.toAffineMap) (s := Csub))
  have hmap_set :
      (fun x : coordinateSubmodule n m => (x : EuclideanSpace Real (Fin n))) ''
        (affineSpan Real Csub : Set (coordinateSubmodule n m)) =
        coordinateSubspace n m := by
    have hmap_set' :
        (fun x : coordinateSubmodule n m => (x : EuclideanSpace Real (Fin n))) ''
          (affineSpan Real Csub : Set (coordinateSubmodule n m)) =
          (affineSpan Real C : Set (EuclideanSpace Real (Fin n))) := by
      simpa [AffineSubspace.coe_map] using
        congrArg (fun (S : AffineSubspace Real (EuclideanSpace Real (Fin n))) =>
          (S : Set (EuclideanSpace Real (Fin n)))) hmap
    simpa [hspan] using hmap_set'
  have hspan_sub :
      (affineSpan Real Csub : Set (coordinateSubmodule n m)) = Set.univ := by
    ext x; constructor
    · intro _; exact Set.mem_univ _
    · intro _
      have hxval : (x : EuclideanSpace Real (Fin n)) ∈ coordinateSubspace n m := x.property
      have hximage :
          (x : EuclideanSpace Real (Fin n)) ∈
            (fun y : coordinateSubmodule n m => (y : EuclideanSpace Real (Fin n))) ''
              (affineSpan Real Csub : Set (coordinateSubmodule n m)) := by
        simp [hmap_set, hxval]
      rcases hximage with ⟨y, hy, hyval⟩
      have hyx : y = x := by
        apply Subtype.ext
        simpa using hyval
      simpa [hyx] using hy
  have hspan_sub' :
      affineSpan Real Csub = (⊤ : AffineSubspace Real (coordinateSubmodule n m)) := by
    ext x; constructor
    · intro _; exact Set.mem_univ _
    · intro _
      change x ∈ (affineSpan Real Csub : Set (coordinateSubmodule n m))
      simp [hspan_sub]
  have hspan_e :
      affineSpan Real (e.symm '' Csub) =
        (⊤ : AffineSubspace Real (EuclideanSpace Real (Fin m))) :=
    (AffineEquiv.span_eq_top_iff (e := e.symm) (s := Csub)).1 hspan_sub'
  have hspan_e_set :
      (affineSpan Real (e.symm '' Csub) : Set (EuclideanSpace Real (Fin m))) = Set.univ := by
    simpa using
      congrArg
        (fun (S : AffineSubspace Real (EuclideanSpace Real (Fin m))) =>
          (S : Set (EuclideanSpace Real (Fin m)))) hspan_e
  simpa using hspan_e_set

/-- If `A` has a right inverse on `s`, then `A '' (A ⁻¹' s) = s`. -/
lemma image_preimage_eq_of_rightInverse {α β : Type*} {A : α → β} {g : β → α} {s : Set β}
    (hright : ∀ y ∈ s, A (g y) = y) : A '' (A ⁻¹' s) = s := by
  ext y; constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    refine ⟨g y, ?_, hright y hy⟩
    simpa [hright y hy] using hy

/-- For linear affine maps, the value equals the linear part. -/
lemma affineMap_apply_eq_linear {n m : Nat}
    (A : EuclideanSpace Real (Fin m) →ᵃ[Real] EuclideanSpace Real (Fin n))
    (hA0 : A 0 = 0) : ∀ x, A x = A.linear x := by
  intro x
  have h := A.map_vadd 0 x
  simpa [hA0] using h

/-- The relative interior of a linear affine image is the image of the relative interior. -/
lemma ri_image_linearMap_eq {n m : Nat}
    {D : Set (EuclideanSpace Real (Fin m))} (hconvD : Convex Real D)
    (A : EuclideanSpace Real (Fin m) →ᵃ[Real] EuclideanSpace Real (Fin n))
    (hA0 : A 0 = 0) :
    euclideanRelativeInterior n (A '' D) = A '' euclideanRelativeInterior m D := by
  have hAeq : ∀ x, A x = A.linear x := affineMap_apply_eq_linear (A := A) hA0
  have himage :
      ((A.linear : EuclideanSpace Real (Fin m) → EuclideanSpace Real (Fin n)) '' D) =
        A '' D := by
    ext y; constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, hAeq x⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (hAeq x).symm⟩
  have himage_ri :
      ((A.linear : EuclideanSpace Real (Fin m) → EuclideanSpace Real (Fin n)) ''
          euclideanRelativeInterior m D) =
        A '' euclideanRelativeInterior m D := by
    ext y; constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, hAeq x⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (hAeq x).symm⟩
  have hri :=
    (euclideanRelativeInterior_image_linearMap_eq_and_image_closure_subset m n D hconvD
        A.linear).1
  simpa [himage, himage_ri] using hri

/-- The coordinate-subspace embedding is surjective onto subsets of the subspace. -/
lemma A_image_eq_C' {n m : Nat} {C' : Set (EuclideanSpace Real (Fin n))}
    (e : EuclideanSpace Real (Fin m) ≃ᵃ[Real] coordinateSubmodule n m)
    (A : EuclideanSpace Real (Fin m) →ᵃ[Real] EuclideanSpace Real (Fin n))
    (hA : A = ((coordinateSubmodule n m).subtype.toAffineMap).comp e.toAffineMap)
    (hC' : C' ⊆ coordinateSubspace n m) :
    A '' (A ⁻¹' C') = C' := by
  classical
  ext y; constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    have hy' : (⟨y, hC' hy⟩ : coordinateSubmodule n m) ∈ (Subtype.val ⁻¹' C') := by
      simpa using hy
    refine ⟨e.symm ⟨y, hC' hy⟩, ?_, ?_⟩
    · have : A (e.symm ⟨y, hC' hy⟩) = y := by
        simp [hA, AffineMap.comp_apply]
      simpa [this] using hy
    · simp [hA, AffineMap.comp_apply]

/-- Transfer continuity along a left inverse on an image. -/
lemma continuousOn_of_leftInverse_on_range {α β γ : Type*} [TopologicalSpace α]
    [TopologicalSpace β] [TopologicalSpace γ]
    {A : α → β} {g : β → α} {f : β → γ} {s : Set α} {t : Set β}
    (hcont : ContinuousOn (fun x => f (A x)) s)
    (hleft : Function.LeftInverse g A)
    (ht : t = A '' s)
    (hg : Continuous g) :
    ContinuousOn f t := by
  have hmaps : Set.MapsTo g t s := by
    intro y hy
    rcases (by simpa [ht] using hy) with ⟨x, hx, rfl⟩
    simpa [hleft x] using hx
  have hcomp :
      ContinuousOn (fun y => f (A (g y))) t :=
    hcont.comp (s := t) hg.continuousOn hmaps
  have hEq : Set.EqOn (fun y => f (A (g y))) f t := by
    intro y hy
    rcases (by simpa [ht] using hy) with ⟨x, hx, rfl⟩
    simp [hleft x]
  exact hcomp.congr hEq.symm

/-- Reduce continuity on relative interior via an affine coordinate subspace model. -/
lemma convexOn_continuousOn_ri_via_coordinateSubspace {n : Nat}
    {C : Set (EuclideanSpace Real (Fin n))} {g : EuclideanSpace Real (Fin n) → ℝ}
    (hg : ConvexOn ℝ C g) : ContinuousOn g (euclideanRelativeInterior n C) := by
  classical
  by_cases hri : (euclideanRelativeInterior n C).Nonempty
  · have hri_sub : euclideanRelativeInterior n C ⊆ C :=
      (euclideanRelativeInterior_subset_closure n C).1
    have hCnonempty : C.Nonempty := by
      rcases hri with ⟨x, hx⟩
      exact ⟨x, hri_sub hx⟩
    let m := Module.finrank Real (affineSpan Real C).direction
    obtain ⟨T, hT⟩ :=
      exists_affineEquiv_affineSpan_eq_coordinateSubspace n m C hCnonempty (by simp [m])
    have hspanT :
        (affineSpan Real (T '' C) : Set (EuclideanSpace Real (Fin n))) =
          coordinateSubspace n m := by
      have hspan' := affineSpan_image_affineEquiv (n := n) (C := C) (e := T)
      simpa [hspan'] using hT
    have hmn :
        m ≤ n := by
      have hle :
          Module.finrank Real (affineSpan Real C).direction ≤
            Module.finrank Real (EuclideanSpace Real (Fin n)) :=
        Submodule.finrank_le (affineSpan Real C).direction
      simpa [m, finrank_euclideanSpace_fin] using hle
    let e := coordinateSubspace_affineEquiv (n := n) (m := m) hmn
    let C' : Set (EuclideanSpace Real (Fin n)) := T '' C
    let A : EuclideanSpace Real (Fin m) →ᵃ[Real] EuclideanSpace Real (Fin n) :=
      ((coordinateSubmodule n m).subtype.toAffineMap).comp e.toAffineMap
    let D : Set (EuclideanSpace Real (Fin m)) :=
      e.symm '' (Subtype.val ⁻¹' C')
    have hpre : T.symm ⁻¹' C = C' := by
      ext x; constructor
      · intro hx
        exact ⟨T.symm x, hx, by simp⟩
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
    have hconvT : ConvexOn ℝ C' (fun x => g (T.symm x)) := by
      simpa [hpre, C', Function.comp] using
        (ConvexOn.comp_affineMap (g := T.symm.toAffineMap) (s := C) hg)
    have hD : D = A ⁻¹' C' := by
      ext x; constructor
      · rintro ⟨y, hy, rfl⟩
        simpa [A, C', AffineMap.comp_apply] using hy
      · intro hx
        refine ⟨e x, ?_, by simp⟩
        simpa [A, C', AffineMap.comp_apply] using hx
    have hconvD : ConvexOn ℝ D (fun x => g (T.symm (A x))) := by
      simpa [D, hD, Function.comp, A] using
        (ConvexOn.comp_affineMap (g := A) (s := C') hconvT)
    have hspanD :
        (affineSpan Real D : Set (EuclideanSpace Real (Fin m))) = Set.univ := by
      simpa [D, C'] using
        (affineSpan_preimage_eq_univ (n := n) (m := m) hmn
          (C := C') hspanT)
    have hcontD :
        ContinuousOn (fun x => g (T.symm (A x))) (euclideanRelativeInterior m D) := by
      exact convexOn_continuousOn_ri_of_affineSpan_eq_univ
        (C := D) (g := fun x => g (T.symm (A x))) hconvD hspanD
    -- TODO: transport continuity back to `C'` using the linear map image lemma for `A`.
    have hcontC' :
        ContinuousOn (fun x => g (T.symm x)) (euclideanRelativeInterior n C') := by
      have hC'sub : C' ⊆ coordinateSubspace n m := by
        intro x hx
        have hx' :
            x ∈ (affineSpan Real C' : Set (EuclideanSpace Real (Fin n))) :=
          subset_affineSpan (k := Real) (s := C') hx
        simpa [C', hspanT] using hx'
      have hA_image : A '' D = C' := by
        have hA_image' :
            A '' (A ⁻¹' C') = C' :=
          A_image_eq_C' (e := e) (A := A) rfl hC'sub
        simpa [hD] using hA_image'
      let e_m' : EuclideanSpace Real (Fin m) ≃L[Real] (Fin m → Real) :=
        EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)
      let e_n' : EuclideanSpace Real (Fin n) ≃L[Real] (Fin n → Real) :=
        EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)
      let A0' : (Fin m → Real) →ₗ[Real] (Fin n → Real) :=
        Function.ExtendByZero.linearMap Real (Fin.castLE hmn)
      let A0 : EuclideanSpace Real (Fin m) →ₗ[Real] EuclideanSpace Real (Fin n) :=
        e_n'.symm.toLinearMap.comp (A0'.comp e_m'.toLinearMap)
      have hAeq : ∀ x, A x = A0 x := by
        intro x
        simp [A, A0, A0', AffineMap.comp_apply, e, coordinateSubspace_affineEquiv, e_m', e_n']
      have hA0 : A 0 = 0 := by
        simp [hAeq 0]
      have hri_eq :
          euclideanRelativeInterior n C' = A '' euclideanRelativeInterior m D := by
        have hri := ri_image_linearMap_eq (n := n) (m := m) (D := D) hconvD.1 A hA0
        simpa [hA_image] using hri
      let p' : (Fin n → Real) →ₗ[Real] (Fin m → Real) :=
        LinearMap.funLeft Real Real (Fin.castLE hmn)
      let p : EuclideanSpace Real (Fin n) →ₗ[Real] EuclideanSpace Real (Fin m) :=
        e_m'.symm.toLinearMap.comp (p'.comp e_n'.toLinearMap)
      have hleft0' : Function.LeftInverse p' A0' := by
        intro x
        ext i
        have hcomp :=
          Function.extend_comp (f := Fin.castLE hmn) (g := x) (e' := fun _ => (0 : Real))
            (hf := Fin.castLE_injective hmn)
        have hcomp' := congrArg (fun h => h i) hcomp
        simpa [A0', p', LinearMap.funLeft_apply] using hcomp'
      have hleft0 : Function.LeftInverse p A0 := by
        intro x
        apply e_m'.injective
        have hcomp : e_m' (p (A0 x)) = p' (A0' (e_m' x)) := by
          have h1 : e_m' (p (A0 x)) = p' (e_n' (A0 x)) := by
            simp [p, LinearMap.comp_apply]
          have h2 : e_n' (A0 x) = A0' (e_m' x) := by
            simp [A0, LinearMap.comp_apply]
          simpa [h2] using h1
        simpa [hcomp] using (hleft0' (e_m' x))
      have hleft : Function.LeftInverse p A := by
        intro x
        simpa [hAeq x] using hleft0 x
      have hpcont : Continuous p :=
        (LinearMap.continuous_of_finiteDimensional (f := p))
      exact
        continuousOn_of_leftInverse_on_range (A := A) (g := p)
          (f := fun x => g (T.symm x)) (s := euclideanRelativeInterior m D)
          (t := euclideanRelativeInterior n C') hcontD hleft hri_eq hpcont
    exact continuousOn_ri_of_affineEquiv (n := n) (C := C) (g := g) (e := T) hcontC'
  · have hri' : euclideanRelativeInterior n C = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro x hx
      exact hri ⟨x, hx⟩
    simp [hri']
end Section07
end Chap02
