/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Weiran Shi, Yunxi Duan, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section07_part7
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section12_part3
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section12_part7
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section16_part2

section Chap03
section Section16

open scoped BigOperators
open scoped Pointwise

/-- Diagonal points in the relative interior of a block-sum domain. -/
lemma section16_diag_mem_ri_effectiveDomain_blockSum_iff {n m : Nat}
    (f : Fin m → (Fin n → ℝ) → EReal)
    (hf : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i)) :
    let g : (Fin (m * n) → ℝ) → EReal :=
      fun x => ∑ i, f i (section16_blockLinearMap (n := n) (m := m) i x)
    (∃ x : EuclideanSpace ℝ (Fin n),
        section16_diagLinearMapE (n := n) (m := m) x ∈
          euclideanRelativeInterior (m * n)
            ((fun z : EuclideanSpace ℝ (Fin (m * n)) => (z : Fin (m * n) → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin (m * n) → ℝ)) g)) ↔
      Set.Nonempty
        (⋂ i : Fin m,
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))) := by
  classical
  intro g
  let domg : Set (EuclideanSpace ℝ (Fin (m * n))) :=
    ((fun z : EuclideanSpace ℝ (Fin (m * n)) => (z : Fin (m * n) → ℝ)) ⁻¹'
      effectiveDomain (Set.univ : Set (Fin (m * n) → ℝ)) g)
  let domi : Fin m → Set (EuclideanSpace ℝ (Fin n)) := fun i =>
    ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
      effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))
  have hconv_domi : ∀ i : Fin m, Convex ℝ (domi i) := by
    intro i
    have hconv :
        Convex ℝ (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)) :=
      effectiveDomain_convex
        (S := (Set.univ : Set (Fin n → ℝ))) (f := f i) (hf i).1
    simpa [domi] using
      (hconv.linear_preimage
        ((EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).toLinearMap))
  have hg : ProperConvexFunctionOn (Set.univ : Set (Fin (m * n) → ℝ)) g := by
    simpa [g] using
      (section16_properConvexFunctionOn_blockSum (n := n) (m := m) (f := f) hf)
  have hconv_domg : Convex ℝ domg := by
    have hconv :
        Convex ℝ (effectiveDomain (Set.univ : Set (Fin (m * n) → ℝ)) g) :=
      effectiveDomain_convex
        (S := (Set.univ : Set (Fin (m * n) → ℝ))) (f := g) hg.1
    simpa [domg] using
      (hconv.linear_preimage
        ((EuclideanSpace.equiv (ι := Fin (m * n)) (𝕜 := ℝ)).toLinearMap))
  have hdomg_eq :
      domg =
        ⋂ i : Fin m, (section16_blockLinearMapE (n := n) (m := m) i) ⁻¹' domi i := by
    ext z
    constructor
    · intro hz
      have hz' :
          (z : Fin (m * n) → ℝ) ∈
            effectiveDomain (Set.univ : Set (Fin (m * n) → ℝ)) g := by
        simpa [domg] using hz
      have hnotbot : ∀ i : Fin m, ∀ x, f i x ≠ (⊥ : EReal) := by
        intro i x
        exact (hf i).2.2 x (by simp)
      have hdom :
          effectiveDomain (Set.univ : Set (Fin (m * n) → ℝ)) g =
            ⋂ i : Fin m,
              (section16_blockLinearMap (n := n) (m := m) i) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i) := by
        simpa [g] using
          (section16_effectiveDomain_blockSum_eq_iInter_preimage_blocks
            (n := n) (m := m) (f := f) hnotbot)
      have hz'' : (z : Fin (m * n) → ℝ) ∈
          ⋂ i : Fin m,
            (section16_blockLinearMap (n := n) (m := m) i) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i) := by
        simpa [hdom] using hz'
      refine Set.mem_iInter.2 ?_
      intro i
      have hz_i := (Set.mem_iInter.mp hz'' i)
      have hz_i' :
          (section16_blockLinearMapE (n := n) (m := m) i z : Fin n → ℝ) ∈
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i) := by
        simpa [section16_blockLinearMapE_apply, Set.mem_preimage] using hz_i
      simpa [domi, Set.mem_preimage] using hz_i'
    · intro hz
      have hz' :
          (z : Fin (m * n) → ℝ) ∈
            ⋂ i : Fin m,
              (section16_blockLinearMap (n := n) (m := m) i) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i) := by
        refine Set.mem_iInter.2 ?_
        intro i
        have hz_i := (Set.mem_iInter.mp hz i)
        have hz_i' :
            (section16_blockLinearMap (n := n) (m := m) i (z : Fin (m * n) → ℝ)) ∈
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i) := by
          simpa [domi, section16_blockLinearMapE_apply, Set.mem_preimage] using hz_i
        simpa [Set.mem_preimage] using hz_i'
      have hnotbot : ∀ i : Fin m, ∀ x, f i x ≠ (⊥ : EReal) := by
        intro i x
        exact (hf i).2.2 x (by simp)
      have hdom :
          effectiveDomain (Set.univ : Set (Fin (m * n) → ℝ)) g =
            ⋂ i : Fin m,
              (section16_blockLinearMap (n := n) (m := m) i) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i) := by
        simpa [g] using
          (section16_effectiveDomain_blockSum_eq_iInter_preimage_blocks
            (n := n) (m := m) (f := f) hnotbot)
      have hz'' :
          (z : Fin (m * n) → ℝ) ∈
            effectiveDomain (Set.univ : Set (Fin (m * n) → ℝ)) g := by
        simpa [hdom] using hz'
      simpa [domg] using hz''
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    refine Set.mem_iInter.2 ?_
    intro i
    have himage :
        euclideanRelativeInterior n
            ((section16_blockLinearMapE (n := n) (m := m) i) '' domg) =
          (section16_blockLinearMapE (n := n) (m := m) i) ''
            euclideanRelativeInterior (m * n) domg := by
      exact
        (euclideanRelativeInterior_image_linearMap_eq_and_image_closure_subset
            (n := m * n) (m := n) (C := domg) hconv_domg
            (A := section16_blockLinearMapE (n := n) (m := m) i)).1
    have hx' :
        section16_blockLinearMapE (n := n) (m := m) i
            (section16_diagLinearMapE (n := n) (m := m) x) ∈
          (section16_blockLinearMapE (n := n) (m := m) i) ''
            euclideanRelativeInterior (m * n) domg := by
      refine ⟨section16_diagLinearMapE (n := n) (m := m) x, hx, rfl⟩
    have hx'' :
        section16_blockLinearMapE (n := n) (m := m) i
            (section16_diagLinearMapE (n := n) (m := m) x) ∈
          euclideanRelativeInterior n
            ((section16_blockLinearMapE (n := n) (m := m) i) '' domg) := by
      simpa [himage] using hx'
    have himage_dom :
        (section16_blockLinearMapE (n := n) (m := m) i) '' domg = domi i := by
      simpa [domg, domi] using
        (section16_blockLinearMapE_image_effectiveDomain_blockSum_eq
          (n := n) (m := m) (f := f) (hf := hf) (i := i))
    have hx''' :
        section16_blockLinearMapE (n := n) (m := m) i
            (section16_diagLinearMapE (n := n) (m := m) x) ∈
          euclideanRelativeInterior n (domi i) := by
      simpa [himage_dom] using hx''
    simpa [section16_blockLinearMapE_diag] using hx'''
  · rintro ⟨x, hx⟩
    have hx' : ∀ i : Fin m, x ∈ euclideanRelativeInterior n (domi i) := by
      intro i
      exact (Set.mem_iInter.mp hx i)
    have hpre_nonempty :
        ∀ i : Fin m,
          ((section16_blockLinearMapE (n := n) (m := m) i) ⁻¹'
              euclideanRelativeInterior n (domi i)).Nonempty := by
      intro i
      refine ⟨section16_diagLinearMapE (n := n) (m := m) x, ?_⟩
      simpa [section16_blockLinearMapE_diag] using (hx' i)
    have hpre_ri :
        ∀ i : Fin m,
          euclideanRelativeInterior (m * n)
              ((section16_blockLinearMapE (n := n) (m := m) i) ⁻¹' (domi i)) =
            (section16_blockLinearMapE (n := n) (m := m) i) ⁻¹'
              euclideanRelativeInterior n (domi i) := by
      intro i
      exact
        (euclideanRelativeInterior_preimage_linearMap_eq_and_closure_preimage
            (n := m * n) (m := n)
            (A := section16_blockLinearMapE (n := n) (m := m) i)
            (C := domi i) (hC := hconv_domi i) (hri := hpre_nonempty i)).1
    have hri_nonempty :
        (⋂ i : Fin m,
            euclideanRelativeInterior (m * n)
              ((section16_blockLinearMapE (n := n) (m := m) i) ⁻¹' (domi i))).Nonempty := by
      refine ⟨section16_diagLinearMapE (n := n) (m := m) x, ?_⟩
      refine Set.mem_iInter.2 ?_
      intro i
      have hxri : x ∈ euclideanRelativeInterior n (domi i) := hx' i
      have hxpre :
          section16_diagLinearMapE (n := n) (m := m) x ∈
            (section16_blockLinearMapE (n := n) (m := m) i) ⁻¹'
              euclideanRelativeInterior n (domi i) := by
        simpa [section16_blockLinearMapE_diag] using hxri
      simpa [hpre_ri i] using hxpre
    have hri_eq :
        euclideanRelativeInterior (m * n)
            (⋂ i : Fin m,
              (section16_blockLinearMapE (n := n) (m := m) i) ⁻¹' (domi i)) =
          ⋂ i : Fin m,
            euclideanRelativeInterior (m * n)
              ((section16_blockLinearMapE (n := n) (m := m) i) ⁻¹' (domi i)) := by
      have hconv_pre :
          ∀ i : Fin m, Convex ℝ
            ((section16_blockLinearMapE (n := n) (m := m) i) ⁻¹' (domi i)) := by
        intro i
        exact (hconv_domi i).linear_preimage
          (section16_blockLinearMapE (n := n) (m := m) i)
      exact
        (euclideanRelativeInterior_iInter_eq_iInter_relativeInterior_of_finite (n := m * n)
            (C := fun i : Fin m =>
              (section16_blockLinearMapE (n := n) (m := m) i) ⁻¹' (domi i))
            (hC := hconv_pre) (hri := hri_nonempty))
    have hxri_domg :
        section16_diagLinearMapE (n := n) (m := m) x ∈
          euclideanRelativeInterior (m * n)
            (⋂ i : Fin m,
              (section16_blockLinearMapE (n := n) (m := m) i) ⁻¹' (domi i)) := by
      have hx_mem :
          section16_diagLinearMapE (n := n) (m := m) x ∈
            ⋂ i : Fin m,
              euclideanRelativeInterior (m * n)
                ((section16_blockLinearMapE (n := n) (m := m) i) ⁻¹' (domi i)) := by
        refine Set.mem_iInter.2 ?_
        intro i
        have hxri : x ∈ euclideanRelativeInterior n (domi i) := hx' i
        have hxpre :
            section16_diagLinearMapE (n := n) (m := m) x ∈
              (section16_blockLinearMapE (n := n) (m := m) i) ⁻¹'
                euclideanRelativeInterior n (domi i) := by
          simpa [section16_blockLinearMapE_diag] using hxri
        simpa [hpre_ri i] using hxpre
      simpa [hri_eq] using hx_mem
    refine ⟨x, ?_⟩
    simpa [hdomg_eq.symm, domg] using hxri_domg

/-- Corollary 16.2.2. Let `f₁, …, fₘ` be proper convex functions on `ℝⁿ`. Then there do not exist
vectors `x₁⋆, …, xₘ⋆` such that

- `x₁⋆ + ⋯ + xₘ⋆ = 0`,
- `(f₁⋆0⁺)(x₁⋆) + ⋯ + (fₘ⋆0⁺)(xₘ⋆) ≤ 0`,
- `(f₁⋆0⁺)(-x₁⋆) + ⋯ + (fₘ⋆0⁺)(-xₘ⋆) > 0`,

if and only if `ri (dom f₁) ∩ ⋯ ∩ ri (dom fₘ) ≠ ∅`.

Here `dom fᵢ` is the effective domain `effectiveDomain univ (f i)`, `ri` is
`euclideanRelativeInterior`, and `(fᵢ⋆0⁺)` is represented as
`recessionFunction (fenchelConjugate n (f i))`. -/
theorem section16_nonempty_iInter_ri_effectiveDomain_iff_not_exists_sum_eq_zero_recession_ineq
    {n m : Nat} (f : Fin m → (Fin n → ℝ) → EReal)
    (hf : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i)) :
    (¬ ∃ xStar : Fin m → Fin n → ℝ,
        (∑ i, xStar i) = 0 ∧
          (∑ i, recessionFunction (fenchelConjugate n (f i)) (xStar i)) ≤ (0 : EReal) ∧
            (∑ i, recessionFunction (fenchelConjugate n (f i)) (-xStar i)) > (0 : EReal)) ↔
      Set.Nonempty
        (⋂ i : Fin m,
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))) := by
  classical
  let g : (Fin (m * n) → ℝ) → EReal :=
    fun x => ∑ i, f i (section16_blockLinearMap (n := n) (m := m) i x)
  have hg : ProperConvexFunctionOn (Set.univ : Set (Fin (m * n) → ℝ)) g := by
    simpa [g] using
      (section16_properConvexFunctionOn_blockSum (n := n) (m := m) (f := f) hf)
  have hleft :
      (∃ yStar : EuclideanSpace ℝ (Fin (m * n)),
          (LinearMap.adjoint (section16_diagLinearMapE (n := n) (m := m)) yStar = 0) ∧
            recessionFunction (fenchelConjugate (m * n) g) (yStar : Fin (m * n) → ℝ) ≤ (0 : EReal) ∧
              recessionFunction (fenchelConjugate (m * n) g) (-yStar : Fin (m * n) → ℝ) >
                (0 : EReal)) ↔
        ∃ xStar : Fin m → Fin n → ℝ,
          (∑ i, xStar i) = 0 ∧
            (∑ i, recessionFunction (fenchelConjugate n (f i)) (xStar i)) ≤ (0 : EReal) ∧
              (∑ i, recessionFunction (fenchelConjugate n (f i)) (-xStar i)) > (0 : EReal) := by
    constructor
    · rintro ⟨yStar, hy0, hy1, hy2⟩
      let xStar : Fin m → Fin n → ℝ :=
        fun i => (section16_blockLinearMapE (n := n) (m := m) i yStar : Fin n → ℝ)
      have hy0' :
          (∑ i : Fin m, section16_blockLinearMapE (n := n) (m := m) i yStar) = 0 := by
        simpa [section16_diagLinearMapE_adjoint_eq_sum_blockLinearMapE] using hy0
      have hsum0 : (∑ i : Fin m, xStar i) = 0 := by
        ext j
        have := congrArg (fun z : EuclideanSpace ℝ (Fin n) => z j) hy0'
        simpa [xStar] using this
      have h_unblock :
          section16_unblock (n := n) (m := m) xStar = (yStar : Fin (m * n) → ℝ) := by
        simpa [xStar, section16_blockLinearMapE_apply] using
          (section16_unblock_blockLinearMap (n := n) (m := m)
            (x := (yStar : Fin (m * n) → ℝ)))
      have hrecession :
          recessionFunction (fenchelConjugate (m * n) g) (yStar : Fin (m * n) → ℝ) =
            ∑ i : Fin m, recessionFunction (fenchelConjugate n (f i)) (xStar i) := by
        simpa [h_unblock] using
          (section16_recession_blockSum_unblock_eq_sum (n := n) (m := m)
            (f := f) (xStar := xStar) (hf := hf))
      have hrecession_neg :
          recessionFunction (fenchelConjugate (m * n) g) (-yStar : Fin (m * n) → ℝ) =
            ∑ i : Fin m, recessionFunction (fenchelConjugate n (f i)) (-xStar i) := by
        have hneg' :
            section16_unblock (n := n) (m := m) (fun i => -xStar i) =
              -(section16_unblock (n := n) (m := m) xStar) := by
          exact (map_neg (section16_unblock (n := n) (m := m)) xStar)
        have hneg :
            section16_unblock (n := n) (m := m) (fun i => -xStar i) =
              -(yStar : Fin (m * n) → ℝ) := by
          calc
            section16_unblock (n := n) (m := m) (fun i => -xStar i) =
                -(section16_unblock (n := n) (m := m) xStar) := hneg'
            _ = -(yStar : Fin (m * n) → ℝ) := by simp [h_unblock]
        simpa [hneg] using
          (section16_recession_blockSum_unblock_eq_sum (n := n) (m := m)
            (f := f) (xStar := fun i => -xStar i) (hf := hf))
      refine ⟨xStar, hsum0, ?_, ?_⟩
      · simpa [hrecession] using hy1
      · simpa [hrecession_neg] using hy2
    · rintro ⟨xStar, hx0, hx1, hx2⟩
      let yStar : EuclideanSpace ℝ (Fin (m * n)) :=
        WithLp.toLp 2 (section16_unblock (n := n) (m := m) xStar)
      have hblock :
          ∀ i : Fin m,
            (section16_blockLinearMapE (n := n) (m := m) i yStar : Fin n → ℝ) = xStar i := by
        intro i
        simp [yStar, section16_blockLinearMapE_apply, section16_blockLinearMap_unblock]
      have hsum0 :
          (∑ i : Fin m, section16_blockLinearMapE (n := n) (m := m) i yStar) = 0 := by
        ext j
        have hx0' : (∑ i : Fin m, xStar i) j = 0 := by
          simpa using congrArg (fun z : Fin n → ℝ => z j) hx0
        simpa [hblock] using hx0'
      have hy0 :
          (LinearMap.adjoint (section16_diagLinearMapE (n := n) (m := m)) yStar) = 0 := by
        simpa [section16_diagLinearMapE_adjoint_eq_sum_blockLinearMapE] using hsum0
      have hrecession :
          recessionFunction (fenchelConjugate (m * n) g) (yStar : Fin (m * n) → ℝ) =
            ∑ i : Fin m, recessionFunction (fenchelConjugate n (f i)) (xStar i) := by
        simpa [yStar] using
          (section16_recession_blockSum_unblock_eq_sum (n := n) (m := m)
            (f := f) (xStar := xStar) (hf := hf))
      have hrecession_neg :
          recessionFunction (fenchelConjugate (m * n) g) (-yStar : Fin (m * n) → ℝ) =
            ∑ i : Fin m, recessionFunction (fenchelConjugate n (f i)) (-xStar i) := by
        have hneg :
            section16_unblock (n := n) (m := m) (fun i => -xStar i) =
              -(section16_unblock (n := n) (m := m) xStar) := by
          exact (map_neg (section16_unblock (n := n) (m := m)) xStar)
        simpa [yStar, hneg] using
          (section16_recession_blockSum_unblock_eq_sum (n := n) (m := m)
            (f := f) (xStar := fun i => -xStar i) (hf := hf))
      refine ⟨yStar, hy0, ?_, ?_⟩
      · simpa [hrecession] using hx1
      · simpa [hrecession_neg] using hx2
  have hri :
      (∃ x : EuclideanSpace ℝ (Fin n),
          section16_diagLinearMapE (n := n) (m := m) x ∈
            euclideanRelativeInterior (m * n)
              ((fun z : EuclideanSpace ℝ (Fin (m * n)) => (z : Fin (m * n) → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin (m * n) → ℝ)) g)) ↔
        Set.Nonempty
          (⋂ i : Fin m,
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))) := by
    simpa [g] using
      (section16_diag_mem_ri_effectiveDomain_blockSum_iff
        (n := n) (m := m) (f := f) (hf := hf))
  have hmain :=
    section16_exists_image_mem_ri_effectiveDomain_iff_not_exists_adjoint_eq_zero_recession_ineq
      (A := section16_diagLinearMapE (n := n) (m := m)) (g := g) hg
  have hmain' :
      (¬ ∃ yStar : EuclideanSpace ℝ (Fin (m * n)),
          (LinearMap.adjoint (section16_diagLinearMapE (n := n) (m := m)) yStar = 0) ∧
            recessionFunction (fenchelConjugate (m * n) g) (yStar : Fin (m * n) → ℝ) ≤ (0 : EReal) ∧
              recessionFunction (fenchelConjugate (m * n) g) (-yStar : Fin (m * n) → ℝ) >
                (0 : EReal)) ↔
        Set.Nonempty
          (⋂ i : Fin m,
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))) := by
    simpa [hri] using hmain
  exact (not_congr hleft).symm.trans hmain'

/-- If `(a : EReal) - x = ⊥` with `a` real, then `x = ⊤`. -/
lemma section16_coe_sub_eq_bot_iff_eq_top {a : ℝ} {x : EReal} :
    (a : EReal) - x = (⊥ : EReal) → x = ⊤ := by
  intro hEq
  cases hx : x with
  | bot =>
      have : False := by
        simp [hx] at hEq
      exact this.elim
  | coe r =>
      have : False := by
        simp [hx] at hEq
        exact (EReal.coe_ne_bot _ hEq)
      exact this.elim
  | top =>
      simp

/-- Subtracting an infimum equals the supremum of the translated values. -/
lemma section16_coeReal_sub_sInf_image_eq_sSup_image {α : Type*}
    (S : Set α) (φ : α → EReal) (a : ℝ) :
    ((a : EReal) - sInf (φ '' S)) =
      sSup ((fun x => (a : EReal) - φ x) '' S) := by
  classical
  by_cases hS : S = ∅
  · subst hS
    simp
  apply le_antisymm
  · refine (le_sSup_iff).2 ?_
    intro b hb
    by_cases hbtop : b = ⊤
    · subst hbtop
      exact le_top
    by_cases hbbot : b = ⊥
    · subst hbbot
      have htop : sInf (φ '' S) = (⊤ : EReal) := by
        refine (sInf_eq_top).2 ?_
        intro z hz
        rcases hz with ⟨x, hxS, rfl⟩
        have hle_bot : (a : EReal) - φ x ≤ (⊥ : EReal) := hb ⟨x, hxS, rfl⟩
        have hEq : (a : EReal) - φ x = (⊥ : EReal) := le_antisymm hle_bot bot_le
        exact section16_coe_sub_eq_bot_iff_eq_top hEq
      simp [htop]
    have hbtop' : b ≠ ⊤ := hbtop
    have hbbot' : b ≠ ⊥ := hbbot
    have hle_inf : (a : EReal) - b ≤ sInf (φ '' S) := by
      refine le_sInf ?_
      rintro z ⟨x, hxS, rfl⟩
      have hle : (a : EReal) - φ x ≤ b := hb ⟨x, hxS, rfl⟩
      have hle_add : (a : EReal) ≤ b + φ x := by
        have h1 : φ x ≠ (⊥ : EReal) ∨ b ≠ ⊤ := Or.inr hbtop'
        have h2 : φ x ≠ (⊤ : EReal) ∨ b ≠ ⊥ := Or.inr hbbot'
        exact (EReal.sub_le_iff_le_add h1 h2).1 hle
      exact EReal.sub_le_of_le_add' (by simpa [add_comm] using hle_add)
    have hA_le : (a : EReal) ≤ sInf (φ '' S) + b := by
      have h1 : b ≠ (⊥ : EReal) ∨ sInf (φ '' S) ≠ ⊤ := Or.inl hbbot'
      have h2 : b ≠ (⊤ : EReal) ∨ sInf (φ '' S) ≠ ⊥ := Or.inl hbtop'
      exact (EReal.sub_le_iff_le_add h1 h2).1 hle_inf
    have h1 : sInf (φ '' S) ≠ (⊥ : EReal) ∨ b ≠ ⊤ := Or.inr hbtop'
    have h2 : sInf (φ '' S) ≠ (⊤ : EReal) ∨ b ≠ ⊥ := Or.inr hbbot'
    exact (EReal.sub_le_iff_le_add h1 h2).2 (by simpa [add_comm] using hA_le)
  · refine sSup_le ?_
    rintro z ⟨x, hxS, rfl⟩
    have hle_inf : sInf (φ '' S) ≤ φ x := sInf_le ⟨x, hxS, rfl⟩
    have hsub_le : sInf (φ '' S) - φ x ≤ (0 : EReal) := by
      have h1 : φ x ≠ (⊥ : EReal) ∨ (0 : EReal) ≠ ⊤ := Or.inr (by simp)
      have h2 : φ x ≠ (⊤ : EReal) ∨ (0 : EReal) ≠ ⊥ := Or.inr (by simp)
      exact (EReal.sub_le_iff_le_add h1 h2).2 (by simp [hle_inf])
    have hle_add : (a : EReal) + (sInf (φ '' S) - φ x) ≤ (a : EReal) := by
      have hle_add' := add_le_add_left hsub_le (a : EReal)
      simpa [add_comm] using hle_add'
    have hle_add' : (a : EReal) - φ x + sInf (φ '' S) ≤ (a : EReal) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hle_add
    have h1 : sInf (φ '' S) ≠ (⊥ : EReal) ∨ (a : EReal) ≠ ⊥ := Or.inr (by simp)
    have h2 : sInf (φ '' S) ≠ (⊤ : EReal) ∨ (a : EReal) ≠ ⊤ := Or.inr (by simp)
    exact (EReal.le_sub_iff_add_le h1 h2).2 hle_add'

/-- Collapsing the sup over fibers to a sup over the total space. -/
lemma section16_sSup_range_sSup_fiber_image_eq_sSup_range_total
    {α β : Type*} (A : α → β) (g : α → EReal) :
    sSup (Set.range fun y : β => sSup (g '' {x | A x = y})) = sSup (Set.range g) := by
  classical
  apply le_antisymm
  · refine sSup_le ?_
    rintro z ⟨y, rfl⟩
    refine sSup_le ?_
    rintro z' ⟨x, hx, rfl⟩
    exact le_sSup ⟨x, rfl⟩
  · refine sSup_le ?_
    rintro z ⟨x, rfl⟩
    have hxmem : g x ∈ g '' {x' | A x' = A x} := by
      exact ⟨x, by simp, rfl⟩
    have hle1 : g x ≤ sSup (g '' {x' | A x' = A x}) := le_sSup hxmem
    have hle2 :
        sSup (g '' {x' | A x' = A x}) ≤
          sSup (Set.range fun y : β => sSup (g '' {x | A x = y})) :=
      le_sSup ⟨A x, rfl⟩
    exact le_trans hle1 hle2

/-- Dot product with a linear map equals dot product with the adjoint. -/
lemma section16_dotProduct_map_eq_dotProduct_adjoint {n m : Nat}
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (x : Fin n → ℝ) (yStar : Fin m → ℝ) :
    dotProduct (A (WithLp.toLp 2 x) : Fin m → ℝ) yStar =
      dotProduct x
        ((LinearMap.adjoint A) (WithLp.toLp 2 yStar) : Fin n → ℝ) := by
  have hinner :=
    LinearMap.adjoint_inner_right (A := A) (x := WithLp.toLp 2 x) (y := WithLp.toLp 2 yStar)
  simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using hinner.symm

/-- Dot-product identity with swapped arguments, to match support-function conventions. -/
lemma section16_dotProduct_adjoint_map_comm {n m : Nat}
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (x : Fin n → ℝ) (yStar : Fin m → ℝ) :
    dotProduct yStar (A (WithLp.toLp 2 x) : Fin m → ℝ) =
      dotProduct ((LinearMap.adjoint A) (WithLp.toLp 2 yStar) : Fin n → ℝ) x := by
  simpa [dotProduct_comm] using
    (section16_dotProduct_map_eq_dotProduct_adjoint (A := A) (x := x) (yStar := yStar))

/-- The dot-product image of a linear image is reindexed by the adjoint. -/
lemma section16_image_dotProduct_linearImage_eq_image_dotProduct_adjoint {n m : Nat}
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (C : Set (Fin n → ℝ)) (yStar : Fin m → ℝ) :
    Set.image (fun y : Fin m → ℝ => dotProduct yStar y)
        (Set.image (fun x : Fin n → ℝ => (A (WithLp.toLp 2 x) : Fin m → ℝ)) C) =
      Set.image (fun x : Fin n → ℝ =>
        dotProduct ((LinearMap.adjoint A) (WithLp.toLp 2 yStar) : Fin n → ℝ) x) C := by
  classical
  ext z
  constructor
  · rintro ⟨y, ⟨x, hxC, rfl⟩, rfl⟩
    refine ⟨x, hxC, ?_⟩
    simpa using (section16_dotProduct_adjoint_map_comm (A := A) (x := x) (yStar := yStar)).symm
  · rintro ⟨x, hxC, rfl⟩
    refine ⟨(A (WithLp.toLp 2 x) : Fin m → ℝ), ?_, ?_⟩
    · exact ⟨x, hxC, rfl⟩
    · simpa using (section16_dotProduct_adjoint_map_comm (A := A) (x := x) (yStar := yStar))

/-- Reindexing a `Set.range` along `WithLp.toLp` does not change the range. -/
lemma section16_range_euclideanSpace_toLp_eq_range {n : Nat}
    (g : EuclideanSpace ℝ (Fin n) → EReal) :
    Set.range g = Set.range (fun x : Fin n → ℝ => g (WithLp.toLp 2 x)) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨(x : Fin n → ℝ), ?_⟩
    simp
  · rintro ⟨x, rfl⟩
    exact ⟨WithLp.toLp 2 x, rfl⟩

/-- Theorem 16.3.1: Let `A : ℝ^n →ₗ[ℝ] ℝ^m` be a linear transformation. For any convex function
`f` on `ℝ^n`, the Fenchel conjugate of the direct image `A f` satisfies

`(A f)^* = f^* ∘ A^*`,

where `(A f) y = inf {f x | A x = y}` and `A^*` is the adjoint of `A`. -/
theorem section16_fenchelConjugate_linearImage {n m : Nat}
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (f : (Fin n → ℝ) → EReal) :
    fenchelConjugate m
        (fun y =>
          sInf
            ((fun x : EuclideanSpace ℝ (Fin n) => f (x : Fin n → ℝ)) '' {x | (A x : _ ) = y})) =
      fun yStar : Fin m → ℝ =>
        fenchelConjugate n f
          (((LinearMap.adjoint :
                  (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ≃ₗ⋆[ℝ]
                    (EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))
                A)
            (WithLp.toLp 2 yStar) : Fin n → ℝ) := by
  classical
  funext yStar
  let g : EuclideanSpace ℝ (Fin n) → EReal :=
    fun x => ((dotProduct (A x : Fin m → ℝ) yStar : ℝ) : EReal) - f (x : Fin n → ℝ)
  let xStar' : Fin n → ℝ :=
    (((LinearMap.adjoint :
            (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ≃ₗ⋆[ℝ]
              (EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))
          A)
        (WithLp.toLp 2 yStar) : Fin n → ℝ)
  have hrewrite :
      (fun y : Fin m → ℝ =>
          ((dotProduct y yStar : ℝ) : EReal) -
            sInf
              ((fun x : EuclideanSpace ℝ (Fin n) => f (x : Fin n → ℝ)) ''
                {x | (A x : Fin m → ℝ) = y})) =
        (fun y : Fin m → ℝ =>
          sSup (g '' {x | (A x : Fin m → ℝ) = y})) := by
    funext y
    have h :=
      section16_coeReal_sub_sInf_image_eq_sSup_image
        (S := {x : EuclideanSpace ℝ (Fin n) | (A x : Fin m → ℝ) = y})
        (φ := fun x : EuclideanSpace ℝ (Fin n) => f (x : Fin n → ℝ))
        (a := dotProduct y yStar)
    have himage :
        (fun x : EuclideanSpace ℝ (Fin n) =>
            ((dotProduct y yStar : ℝ) : EReal) - f (x : Fin n → ℝ)) ''
          {x : EuclideanSpace ℝ (Fin n) | (A x : Fin m → ℝ) = y} =
          g '' {x : EuclideanSpace ℝ (Fin n) | (A x : Fin m → ℝ) = y} := by
      refine Set.image_congr ?_
      intro x hx
      simp [g, hx.symm]
    simpa [himage, g] using h
  have hsup :
      sSup (Set.range fun y : Fin m → ℝ =>
          sSup (g '' {x : EuclideanSpace ℝ (Fin n) | (A x : Fin m → ℝ) = y})) =
        sSup (Set.range g) := by
    simpa [g] using
      (section16_sSup_range_sSup_fiber_image_eq_sSup_range_total
        (A := fun x : EuclideanSpace ℝ (Fin n) => (A x : Fin m → ℝ))
        (g := g))
  have hleft :
      fenchelConjugate m
          (fun y =>
            sInf
              ((fun x : EuclideanSpace ℝ (Fin n) => f (x : Fin n → ℝ)) '' {x | (A x : _ ) = y}))
          yStar =
        sSup (Set.range g) := by
    simp [fenchelConjugate, hrewrite, hsup]
  have hrange :
      Set.range g =
        Set.range (fun x : Fin n → ℝ =>
          ((dotProduct (A (WithLp.toLp 2 x) : Fin m → ℝ) yStar : ℝ) : EReal) - f x) := by
    simpa [g] using (section16_range_euclideanSpace_toLp_eq_range (g := g))
  have hdot :
      (fun x : Fin n → ℝ =>
          ((dotProduct (A (WithLp.toLp 2 x) : Fin m → ℝ) yStar : ℝ) : EReal) - f x) =
        (fun x : Fin n → ℝ => ((dotProduct x xStar' : ℝ) : EReal) - f x) := by
    funext x
    have h := section16_dotProduct_map_eq_dotProduct_adjoint (A := A) (x := x) (yStar := yStar)
    simp [xStar', h]
  have hright :
      sSup (Set.range g) =
        sSup (Set.range (fun x : Fin n → ℝ => ((dotProduct x xStar' : ℝ) : EReal) - f x)) := by
    simp [hrange, hdot]
  have hfinal :
      fenchelConjugate m
          (fun y =>
            sInf
              ((fun x : EuclideanSpace ℝ (Fin n) => f (x : Fin n → ℝ)) '' {x | (A x : _ ) = y}))
          yStar =
        sSup (Set.range (fun x : Fin n → ℝ => ((dotProduct x xStar' : ℝ) : EReal) - f x)) := by
    exact hleft.trans hright
  simpa [fenchelConjugate, xStar'] using hfinal

/-- The first-coordinate projection `ℝ² → ℝ` as a linear map. -/
def section16_projFirstLinearMap :
    EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 1) :=
  { toFun := fun x => WithLp.toLp 2 ![(x : Fin 2 → ℝ) 0]
    map_add' := by
      intro x y
      ext i
      fin_cases i
      rfl
    map_smul' := by
      intro c x
      ext i
      fin_cases i
      rfl }

/-- The fiber image of the first-coordinate projection equals the range over the second coordinate. -/
lemma section16_image_fiber_projFirst_eq_range (f : (Fin 2 → ℝ) → EReal) (ξ1 : Fin 1 → ℝ) :
    (fun x : EuclideanSpace ℝ (Fin 2) => f (x : Fin 2 → ℝ)) ''
        {x | (section16_projFirstLinearMap x : Fin 1 → ℝ) = ξ1} =
      Set.range (fun ξ2 : ℝ => f ![ξ1 0, ξ2]) := by
  classical
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx0 : (x : Fin 2 → ℝ) 0 = ξ1 0 := by
      have hx' := congrArg (fun y : Fin 1 → ℝ => y 0) hx
      simpa [section16_projFirstLinearMap] using hx'
    let ξ2 : ℝ := (x : Fin 2 → ℝ) 1
    refine ⟨ξ2, ?_⟩
    have hx' : (x : Fin 2 → ℝ) = ![ξ1 0, ξ2] := by
      ext i
      fin_cases i <;> simp [hx0, ξ2]
    simp [hx']
  · rintro ⟨ξ2, rfl⟩
    refine ⟨WithLp.toLp 2 ![ξ1 0, ξ2], ?_, rfl⟩
    ext i
    fin_cases i
    simp [section16_projFirstLinearMap]

/-- The adjoint of the first-coordinate projection sends `ξ1Star` to `(ξ1Star, 0)`. -/
lemma section16_adjoint_projFirst_to_pair (ξ1Star : Fin 1 → ℝ) :
    (((LinearMap.adjoint :
            (EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 1)) ≃ₗ⋆[ℝ]
              (EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)))
          section16_projFirstLinearMap)
        (WithLp.toLp 2 ξ1Star) : Fin 2 → ℝ) = ![ξ1Star 0, (0 : ℝ)] := by
  classical
  let v :
      Fin 2 → ℝ :=
    (((LinearMap.adjoint :
            (EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 1)) ≃ₗ⋆[ℝ]
              (EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)))
          section16_projFirstLinearMap)
        (WithLp.toLp 2 ξ1Star) : Fin 2 → ℝ)
  ext i
  fin_cases i
  · have h :=
      section16_dotProduct_map_eq_dotProduct_adjoint
        (A := section16_projFirstLinearMap)
        (x := Pi.single (M := fun _ : Fin 2 => ℝ) 0 (1 : ℝ))
        (yStar := ξ1Star)
    have h' : ξ1Star 0 = v 0 := by
      simpa [section16_projFirstLinearMap, v, single_one_dotProduct] using h
    simpa [v] using h'.symm
  · have h :=
      section16_dotProduct_map_eq_dotProduct_adjoint
        (A := section16_projFirstLinearMap)
        (x := Pi.single (M := fun _ : Fin 2 => ℝ) 1 (1 : ℝ))
        (yStar := ξ1Star)
    have h' : (0 : ℝ) = v 1 := by
      simpa [section16_projFirstLinearMap, v, single_one_dotProduct] using h
    simpa [v] using h'.symm

/-- Text 16.0.3: As an illustration of Theorem 16.3.1, let `f` be a convex function on `ℝ²` and
define `h : ℝ → ℝ ∪ {±∞}` by

`h(ξ₁) = inf_{ξ₂} f(ξ₁, ξ₂)`.

Equivalently, `h` is the direct image `A f` for the projection `A : (ξ₁, ξ₂) ↦ ξ₁`. The adjoint
map `A^*` sends `ξ₁^*` to `(ξ₁^*, 0)`, hence

`h^*(ξ₁^*) = f^*(ξ₁^*, 0)`. -/
theorem section16_fenchelConjugate_inf_over_second_coordinate
    (f : (Fin 2 → ℝ) → EReal) :
    let h : (Fin 1 → ℝ) → EReal := fun ξ1 => sInf (Set.range fun ξ2 : ℝ => f ![ξ1 0, ξ2])
    fenchelConjugate 1 h = fun ξ1Star : Fin 1 → ℝ => fenchelConjugate 2 f ![ξ1Star 0, (0 : ℝ)] := by
  classical
  dsimp
  simpa [section16_image_fiber_projFirst_eq_range, section16_adjoint_projFirst_to_pair] using
    (section16_fenchelConjugate_linearImage (A := section16_projFirstLinearMap) (f := f))

/-- Corollary 16.3.1.1: Let `A` be a linear transformation from `ℝ^n` to `ℝ^m`. For any convex set
`C ⊆ ℝ^n`, one has `δ^*(y^* | A C) = δ^*(A^* y^* | C)` for all `y^* ∈ ℝ^m`. -/
theorem section16_deltaStar_linearImage {n m : Nat}
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (C : Set (Fin n → ℝ)) :
    deltaStar (Set.image (fun x : Fin n → ℝ => (A (WithLp.toLp 2 x) : Fin m → ℝ)) C) =
      fun yStar : Fin m → ℝ =>
        deltaStar C
          (((LinearMap.adjoint :
                  (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ≃ₗ⋆[ℝ]
                    (EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))
                A)
            (WithLp.toLp 2 yStar) : Fin n → ℝ) := by
  classical
  funext yStar
  have himage :=
    section16_image_dotProduct_linearImage_eq_image_dotProduct_adjoint
      (A := A) (C := C) (yStar := yStar)
  calc
    deltaStar (Set.image (fun x : Fin n → ℝ => (A (WithLp.toLp 2 x) : Fin m → ℝ)) C) yStar =
        sSup
          (Set.image (fun y : Fin m → ℝ => dotProduct yStar y)
            (Set.image (fun x : Fin n → ℝ => (A (WithLp.toLp 2 x) : Fin m → ℝ)) C)) := by
      simp [deltaStar, supportFunction_eq_sSup_image_dotProduct]
    _ =
        sSup
          (Set.image (fun x : Fin n → ℝ =>
            dotProduct ((LinearMap.adjoint A) (WithLp.toLp 2 yStar) : Fin n → ℝ) x) C) := by
      rw [himage]
    _ =
        deltaStar C
          (((LinearMap.adjoint :
                  (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ≃ₗ⋆[ℝ]
                    (EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))
                A)
            (WithLp.toLp 2 yStar) : Fin n → ℝ) := by
      simp [deltaStar, supportFunction_eq_sSup_image_dotProduct]

/-- The conjugate of the support function is the indicator of the closure. -/
lemma section16_fenchelConjugate_supportFunctionEReal_eq_indicatorFunction_closure {m : Nat}
    (D : Set (Fin m → ℝ)) (hD : Convex ℝ D) :
    fenchelConjugate m (supportFunctionEReal D) = indicatorFunction (closure D) := by
  classical
  by_cases hDempty : D = ∅
  · subst hDempty
    funext xStar
    simp [supportFunctionEReal, indicatorFunction, fenchelConjugate]
  · have hDne : Set.Nonempty D := Set.nonempty_iff_ne_empty.2 hDempty
    have hsupport :
        supportFunctionEReal D = fenchelConjugate m (indicatorFunction D) := by
      simpa using
        (section13_fenchelConjugate_indicatorFunction_eq_supportFunctionEReal (C := D)).symm
    have hclConv :
        fenchelConjugate m (supportFunctionEReal D) = clConv m (indicatorFunction D) := by
      simpa [hsupport] using
        (fenchelConjugate_biconjugate_eq_clConv (n := m) (f := indicatorFunction D))
    have hcl :
        clConv m (indicatorFunction D) = indicatorFunction (closure D) :=
      section13_clConv_indicatorFunction_eq_indicatorFunction_closure (C := D) hD hDne
    exact hclConv.trans hcl

/-- Rewriting the adjoint fiber using `WithLp.toLp`. -/
lemma section16_fiber_set_eq_toLp_fiber_set {n m : Nat}
    (Aadj : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (xStar : Fin n → ℝ) :
    {yStar : EuclideanSpace ℝ (Fin m) | Aadj yStar = WithLp.toLp 2 xStar} =
      {yStar | (Aadj yStar : Fin n → ℝ) = xStar} := by
  ext yStar
  constructor
  · intro hy
    have hy' := congrArg (fun z : EuclideanSpace ℝ (Fin n) => (z : Fin n → ℝ)) hy
    simpa using hy'
  · intro hy
    ext i
    simpa using congrArg (fun z => z i) hy

/-- Linear images of convex functions via fiberwise `sInf` are convex. -/
lemma section16_convexFunction_linearImage_sInf_part3 {n m : Nat}
    (Aadj : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (f : (Fin m → ℝ) → EReal) (hf : ConvexFunction f) :
    ConvexFunction
      (fun xStar : Fin n → ℝ =>
        sInf
          ((fun yStar : EuclideanSpace ℝ (Fin m) => f (yStar : Fin m → ℝ)) ''
            {yStar | (Aadj yStar : Fin n → ℝ) = xStar})) := by
  classical
  let h : (Fin n → ℝ) → EReal :=
    fun xStar : Fin n → ℝ =>
      sInf
        ((fun yStar : EuclideanSpace ℝ (Fin m) => f (yStar : Fin m → ℝ)) ''
          {yStar | (Aadj yStar : Fin n → ℝ) = xStar})
  have hstrict_f :
      ∀ x y : Fin m → ℝ, ∀ α β t : Real,
        f x < (α : EReal) → f y < (β : EReal) →
        0 < t → t < 1 →
          f ((1 - t) • x + t • y) <
            ((1 - t : Real) : EReal) * (α : EReal) + ((t : Real) : EReal) * (β : EReal) := by
    have hf' : ConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) f := by
      simpa [ConvexFunction] using hf
    exact (convexFunctionOn_univ_iff_strict_inequality (f := f)).1 hf'
  have hstrict :
      ∀ y1 y2 : Fin n → ℝ, ∀ α β t : Real,
        h y1 < (α : EReal) → h y2 < (β : EReal) →
        0 < t → t < 1 →
          h ((1 - t) • y1 + t • y2) <
            ((1 - t : Real) : EReal) * (α : EReal) + ((t : Real) : EReal) * (β : EReal) := by
    intro y1 y2 α β t hy1 hy2 ht0 ht1
    rcases (sInf_lt_iff).1 hy1 with ⟨z1, hz1, hz1_lt⟩
    rcases hz1 with ⟨x1, hx1, rfl⟩
    rcases (sInf_lt_iff).1 hy2 with ⟨z2, hz2, hz2_lt⟩
    rcases hz2 with ⟨x2, hx2, rfl⟩
    have hx1_lt : f (x1 : Fin m → ℝ) < (α : EReal) := by
      simpa using hz1_lt
    have hx2_lt : f (x2 : Fin m → ℝ) < (β : EReal) := by
      simpa using hz2_lt
    have hcomb :
        f ((1 - t) • (x1 : Fin m → ℝ) + t • (x2 : Fin m → ℝ)) <
          ((1 - t : Real) : EReal) * (α : EReal) + ((t : Real) : EReal) * (β : EReal) :=
      hstrict_f (x := (x1 : Fin m → ℝ)) (y := (x2 : Fin m → ℝ)) (α := α) (β := β) (t := t)
        hx1_lt hx2_lt ht0 ht1
    have hx1' : (Aadj x1 : Fin n → ℝ) = y1 := by
      simpa using hx1
    have hx2' : (Aadj x2 : Fin n → ℝ) = y2 := by
      simpa using hx2
    have hx_t :
        (Aadj ((1 - t) • x1 + t • x2) : Fin n → ℝ) = (1 - t) • y1 + t • y2 := by
      calc
        (Aadj ((1 - t) • x1 + t • x2) : Fin n → ℝ) =
            (1 - t) • (Aadj x1 : Fin n → ℝ) + t • (Aadj x2 : Fin n → ℝ) := by
          simp [map_add, map_smul]
        _ = (1 - t) • y1 + t • y2 := by
          simp [hx1', hx2']
    have hmem :
        f ((1 - t) • (x1 : Fin m → ℝ) + t • (x2 : Fin m → ℝ)) ∈
          (fun yStar : EuclideanSpace ℝ (Fin m) => f (yStar : Fin m → ℝ)) ''
            {yStar | (Aadj yStar : Fin n → ℝ) = (1 - t) • y1 + t • y2} := by
      refine ⟨(1 - t) • x1 + t • x2, ?_, rfl⟩
      simpa using hx_t
    have hle :
        h ((1 - t) • y1 + t • y2) ≤
          f ((1 - t) • (x1 : Fin m → ℝ) + t • (x2 : Fin m → ℝ)) := by
      simpa [h] using (sInf_le hmem)
    exact lt_of_le_of_lt hle hcomb
  have hconv : ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h :=
    (convexFunctionOn_univ_iff_strict_inequality (f := h)).2 hstrict
  simpa [ConvexFunction, h] using hconv

/-- The Fenchel biconjugate of a convex function agrees with its convex-function closure. -/
lemma section16_fenchelConjugate_biconjugate_eq_convexFunctionClosure_part3 {n : Nat}
    {f : (Fin n → ℝ) → EReal} (hf : ConvexFunction f) :
    fenchelConjugate n (fenchelConjugate n f) = convexFunctionClosure f := by
  classical
  have hconj_bot :
      fenchelConjugate n (fun _ : Fin n → ℝ => (⊥ : EReal)) = fun _ => (⊤ : EReal) := by
    funext x
    simp [fenchelConjugate]
  have hconj_top :
      fenchelConjugate n (fun _ : Fin n → ℝ => (⊤ : EReal)) = fun _ => (⊥ : EReal) := by
    funext x
    simp [fenchelConjugate]
  by_cases hbot : ∃ x, f x = (⊥ : EReal)
  · have hcl : convexFunctionClosure f = fun _ => (⊥ : EReal) :=
      convexFunctionClosure_eq_bot_of_exists_bot (f := f) hbot
    calc
      fenchelConjugate n (fenchelConjugate n f) =
          fenchelConjugate n (fenchelConjugate n (convexFunctionClosure f)) := by
            rw [← fenchelConjugate_eq_of_convexFunctionClosure (n := n) (f := f)]
      _ = fun _ => (⊥ : EReal) := by
            simp [hcl, hconj_bot, hconj_top]
      _ = convexFunctionClosure f := by
            simp [hcl]
  · by_cases hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f
    · have hcl :=
        convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri (f := f) hproper
      have hclosed : ClosedConvexFunction (convexFunctionClosure f) := hcl.1.1
      have hne_bot : ∀ x : Fin n → ℝ, convexFunctionClosure f x ≠ (⊥ : EReal) := by
        intro x
        exact hcl.1.2.2.2 x (by simp)
      have hbiconj :
          fenchelConjugate n (fenchelConjugate n (convexFunctionClosure f)) =
            convexFunctionClosure f :=
        fenchelConjugate_biconjugate_eq_of_closedConvex (n := n)
          (f := convexFunctionClosure f) (hf_closed := hclosed.2) (hf_convex := hclosed.1)
          (hf_ne_bot := hne_bot)
      calc
        fenchelConjugate n (fenchelConjugate n f) =
            fenchelConjugate n (fenchelConjugate n (convexFunctionClosure f)) := by
              rw [← fenchelConjugate_eq_of_convexFunctionClosure (n := n) (f := f)]
        _ = convexFunctionClosure f := hbiconj
    · have hconv_on : ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f := by
        simpa [ConvexFunction] using hf
      have himproper : ImproperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f :=
        ⟨hconv_on, hproper⟩
      have hcase :=
        improperConvexFunctionOn_cases_epigraph_empty_or_bot
          (S := (Set.univ : Set (Fin n → ℝ))) (f := f) himproper
      have hne_epi :
          ¬ Set.Nonempty (epigraph (Set.univ : Set (Fin n → ℝ)) f) := by
        rcases hcase with hcase | hcase
        · exact hcase
        · rcases hcase with ⟨x, -, hx⟩
          exact (hbot ⟨x, hx⟩).elim
      have htop : f = fun _ => (⊤ : EReal) := by
        funext x
        exact epigraph_empty_imp_forall_top (f := f) hne_epi x (by simp)
      have hcl : convexFunctionClosure f = fun _ => (⊤ : EReal) := by
        simpa [htop] using (convexFunctionClosure_const_top (n := n))
      calc
        fenchelConjugate n (fenchelConjugate n f) =
            fenchelConjugate n (fenchelConjugate n (convexFunctionClosure f)) := by
              rw [← fenchelConjugate_eq_of_convexFunctionClosure (n := n) (f := f)]
        _ = fun _ => (⊤ : EReal) := by
              simp [hcl, hconj_bot, hconj_top]
        _ = convexFunctionClosure f := by
              simp [hcl]

/-- Corollary 16.3.1.2: Let `A` be a linear transformation from `ℝ^n` to `ℝ^m`. For any convex set
`D ⊆ ℝ^m`, one has

`δ^*(· | A⁻¹ (cl D)) = cl (A^* δ^*(· | D))`.

Here `δ^*(·|D)` is the support function, `cl D` is the topological closure of the set `D`, and
`A^*` is the adjoint of `A`. In this development, the closure `cl` of a function is represented
by `convexFunctionClosure`, and `A^* δ^*(·|D)` is modeled via an `sInf` over the affine fiber
`{yStar | A^* yStar = xStar}`. -/
theorem section16_supportFunctionEReal_preimage_closure_eq_convexFunctionClosure_adjoint_image
    {n m : Nat} (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (D : Set (Fin m → ℝ)) (hD : Convex ℝ D) :
    supportFunctionEReal
        (Set.preimage (fun x : Fin n → ℝ => (A (WithLp.toLp 2 x) : Fin m → ℝ)) (closure D)) =
      convexFunctionClosure
        (fun xStar : Fin n → ℝ =>
          sInf
            ((fun yStar : EuclideanSpace ℝ (Fin m) =>
                  supportFunctionEReal D (yStar : Fin m → ℝ)) ''
              {yStar |
                ((LinearMap.adjoint :
                        (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ≃ₗ⋆[ℝ]
                          (EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))
                      A)
                    yStar =
                  WithLp.toLp 2 xStar})) := by
  classical
  let Aadj :
      EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    ((LinearMap.adjoint :
            (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ≃ₗ⋆[ℝ]
              (EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))
          A)
  let h : (Fin n → ℝ) → EReal :=
    fun xStar : Fin n → ℝ =>
      sInf
        ((fun yStar : EuclideanSpace ℝ (Fin m) => supportFunctionEReal D (yStar : Fin m → ℝ)) ''
          {yStar | Aadj yStar = WithLp.toLp 2 xStar})
  have h_eq :
      h =
        fun xStar : Fin n → ℝ =>
          sInf
            ((fun yStar : EuclideanSpace ℝ (Fin m) => supportFunctionEReal D (yStar : Fin m → ℝ)) ''
              {yStar | (Aadj yStar : Fin n → ℝ) = xStar}) := by
    funext xStar
    simp [h, section16_fiber_set_eq_toLp_fiber_set (Aadj := Aadj) (xStar := xStar)]
  have hconv_support : ConvexFunction (supportFunctionEReal D) := by
    have h := fenchelConjugate_closedConvex (n := m) (f := indicatorFunction D)
    simpa [section13_fenchelConjugate_indicatorFunction_eq_supportFunctionEReal (C := D)] using h.2
  have hconv : ConvexFunction h := by
    simpa [h_eq] using
      (section16_convexFunction_linearImage_sInf_part3 (Aadj := Aadj)
        (f := supportFunctionEReal D) hconv_support)
  have hbiconj :
      fenchelConjugate n (fenchelConjugate n h) = convexFunctionClosure h :=
    section16_fenchelConjugate_biconjugate_eq_convexFunctionClosure_part3 (n := n) (f := h) hconv
  have hfench' :
      fenchelConjugate n h =
        fun xStar : Fin n → ℝ =>
          fenchelConjugate m (supportFunctionEReal D)
            ((LinearMap.adjoint Aadj) (WithLp.toLp 2 xStar) : Fin m → ℝ) := by
    simpa [h_eq] using
      (section16_fenchelConjugate_linearImage (A := Aadj) (f := supportFunctionEReal D))
  have hfench :
      fenchelConjugate n h =
        fun xStar : Fin n → ℝ =>
          indicatorFunction (closure D) (A (WithLp.toLp 2 xStar) : Fin m → ℝ) := by
    simpa [Aadj, LinearMap.adjoint_adjoint,
      section16_fenchelConjugate_supportFunctionEReal_eq_indicatorFunction_closure
        (D := D) hD] using hfench'
  have hfench_pre :
      fenchelConjugate n h =
        indicatorFunction
          (Set.preimage (fun x : Fin n → ℝ => (A (WithLp.toLp 2 x) : Fin m → ℝ)) (closure D)) := by
    funext xStar
    have hx := congrArg (fun g => g xStar) hfench
    simpa [indicatorFunction, Set.mem_preimage] using hx
  have hfinal :
      supportFunctionEReal
          (Set.preimage (fun x : Fin n → ℝ => (A (WithLp.toLp 2 x) : Fin m → ℝ)) (closure D)) =
        convexFunctionClosure h := by
    calc
      supportFunctionEReal
          (Set.preimage (fun x : Fin n → ℝ => (A (WithLp.toLp 2 x) : Fin m → ℝ)) (closure D)) =
          fenchelConjugate n
            (indicatorFunction
              (Set.preimage (fun x : Fin n → ℝ => (A (WithLp.toLp 2 x) : Fin m → ℝ))
                (closure D))) := by
          simpa using
            (section13_fenchelConjugate_indicatorFunction_eq_supportFunctionEReal
              (C :=
                Set.preimage (fun x : Fin n → ℝ => (A (WithLp.toLp 2 x) : Fin m → ℝ))
                  (closure D))).symm
      _ = fenchelConjugate n (fenchelConjugate n h) := by
          simp [hfench_pre]
      _ = convexFunctionClosure h := hbiconj
  simpa [h, Aadj] using hfinal

end Section16
end Chap03
