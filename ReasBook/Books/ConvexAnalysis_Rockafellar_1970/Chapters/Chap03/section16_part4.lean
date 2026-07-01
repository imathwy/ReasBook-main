/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Weiran Shi, Yunxi Duan, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section04_part6
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section07_part3
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section07_part10
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section09_part10
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section09_part15
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section12_part3
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section13_part5
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section13_part7
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section16_part3

section Chap03
section Section16

open scoped BigOperators
open scoped Pointwise

/-- The Fenchel biconjugate of a convex function agrees with its convex-function closure. -/
lemma section16_fenchelConjugate_biconjugate_eq_convexFunctionClosure {n : Nat}
    {f : (Fin n → ℝ) → EReal} (hf : ConvexFunction f) :
    fenchelConjugate n (fenchelConjugate n f) = convexFunctionClosure f := by
  classical
  by_cases hbot : ∃ x, f x = (⊥ : EReal)
  · have hcl : convexFunctionClosure f = constNegInf n := by
      simpa [constNegInf] using (convexFunctionClosure_eq_bot_of_exists_bot (f := f) hbot)
    calc
      fenchelConjugate n (fenchelConjugate n f) =
          fenchelConjugate n (fenchelConjugate n (convexFunctionClosure f)) := by
            rw [← fenchelConjugate_eq_of_convexFunctionClosure (n := n) (f := f)]
      _ = constNegInf n := by
            simp [hcl, fenchelConjugate_constNegInf, fenchelConjugate_constPosInf]
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
      have htop : f = (fun _ => (⊤ : EReal)) := by
        funext x
        exact epigraph_empty_imp_forall_top (f := f) hne_epi x (by simp)
      have hcl : convexFunctionClosure f = constPosInf n := by
        simpa [constPosInf, htop] using (convexFunctionClosure_const_top (n := n))
      calc
        fenchelConjugate n (fenchelConjugate n f) =
            fenchelConjugate n (fenchelConjugate n (convexFunctionClosure f)) := by
              rw [← fenchelConjugate_eq_of_convexFunctionClosure (n := n) (f := f)]
        _ = constPosInf n := by
              simp [hcl, fenchelConjugate_constNegInf, fenchelConjugate_constPosInf]
        _ = convexFunctionClosure f := by
              simp [hcl]

/-- Linear images of convex functions via fiberwise `sInf` are convex. -/
lemma section16_convexFunction_linearImage_sInf {n m : Nat}
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) (f : (Fin n → ℝ) → EReal)
    (hf : ConvexFunction f) :
    ConvexFunction
      (fun y : Fin m → ℝ =>
        sInf
          ((fun x : EuclideanSpace ℝ (Fin n) => f (x : Fin n → ℝ)) '' {x | (A x : _) = y})) := by
  classical
  let h : (Fin m → ℝ) → EReal :=
    fun y : Fin m → ℝ =>
      sInf
        ((fun x : EuclideanSpace ℝ (Fin n) => f (x : Fin n → ℝ)) '' {x | (A x : _) = y})
  have hstrict_f :
      ∀ x y : Fin n → ℝ, ∀ α β t : Real,
        f x < (α : EReal) → f y < (β : EReal) →
        0 < t → t < 1 →
          f ((1 - t) • x + t • y) <
            ((1 - t : Real) : EReal) * (α : EReal) + ((t : Real) : EReal) * (β : EReal) := by
    have hf' : ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f := by
      simpa [ConvexFunction] using hf
    exact (convexFunctionOn_univ_iff_strict_inequality (f := f)).1 hf'
  have hstrict :
      ∀ y1 y2 : Fin m → ℝ, ∀ α β t : Real,
        h y1 < (α : EReal) → h y2 < (β : EReal) →
        0 < t → t < 1 →
          h ((1 - t) • y1 + t • y2) <
            ((1 - t : Real) : EReal) * (α : EReal) + ((t : Real) : EReal) * (β : EReal) := by
    intro y1 y2 α β t hy1 hy2 ht0 ht1
    rcases (sInf_lt_iff).1 hy1 with ⟨z1, hz1, hz1_lt⟩
    rcases hz1 with ⟨x1, hx1, rfl⟩
    rcases (sInf_lt_iff).1 hy2 with ⟨z2, hz2, hz2_lt⟩
    rcases hz2 with ⟨x2, hx2, rfl⟩
    have hx1_lt : f (x1 : Fin n → ℝ) < (α : EReal) := by
      simpa using hz1_lt
    have hx2_lt : f (x2 : Fin n → ℝ) < (β : EReal) := by
      simpa using hz2_lt
    have hcomb :
        f ((1 - t) • (x1 : Fin n → ℝ) + t • (x2 : Fin n → ℝ)) <
          ((1 - t : Real) : EReal) * (α : EReal) + ((t : Real) : EReal) * (β : EReal) :=
      hstrict_f (x := (x1 : Fin n → ℝ)) (y := (x2 : Fin n → ℝ)) (α := α) (β := β) (t := t)
        hx1_lt hx2_lt ht0 ht1
    have hx1' : (A x1 : Fin m → ℝ) = y1 := by
      simpa using hx1
    have hx2' : (A x2 : Fin m → ℝ) = y2 := by
      simpa using hx2
    have hx_t :
        (A ((1 - t) • x1 + t • x2) : Fin m → ℝ) = (1 - t) • y1 + t • y2 := by
      calc
        (A ((1 - t) • x1 + t • x2) : Fin m → ℝ) =
            (1 - t) • (A x1 : Fin m → ℝ) + t • (A x2 : Fin m → ℝ) := by
          simp [map_add, map_smul]
        _ = (1 - t) • y1 + t • y2 := by
          simp [hx1', hx2']
    have hmem :
        f ((1 - t) • (x1 : Fin n → ℝ) + t • (x2 : Fin n → ℝ)) ∈
          (fun x : EuclideanSpace ℝ (Fin n) => f (x : Fin n → ℝ)) ''
            {x | (A x : _) = (1 - t) • y1 + t • y2} := by
      refine ⟨(1 - t) • x1 + t • x2, ?_, rfl⟩
      simpa using hx_t
    have hle :
        h ((1 - t) • y1 + t • y2) ≤
          f ((1 - t) • (x1 : Fin n → ℝ) + t • (x2 : Fin n → ℝ)) := by
      simpa [h] using (sInf_le hmem)
    exact lt_of_le_of_lt hle hcomb
  have hconv : ConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) h :=
    (convexFunctionOn_univ_iff_strict_inequality (f := h)).2 hstrict
  simpa [ConvexFunction, h] using hconv

/-- Applying Theorem 16.3.1 to the adjoint gives a biconjugate identity. -/
lemma section16_fenchelConjugate_adjoint_image_eq_precomp_biconjugate {n m : Nat}
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (g : (Fin m → ℝ) → EReal) :
    let gStar : (Fin m → ℝ) → EReal := fenchelConjugate m g
    let h : (Fin n → ℝ) → EReal :=
      fun xStar : Fin n → ℝ =>
        sInf
          ((fun yStar : EuclideanSpace ℝ (Fin m) => gStar (yStar : Fin m → ℝ)) ''
            {yStar |
              ((LinearMap.adjoint :
                      (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ≃ₗ⋆[ℝ]
                        (EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))
                    A)
                  yStar =
                WithLp.toLp 2 xStar})
    fenchelConjugate n h =
      fun x : Fin n → ℝ =>
        fenchelConjugate m gStar (A (WithLp.toLp 2 x) : Fin m → ℝ) := by
  classical
  let Aadj :
      EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    ((LinearMap.adjoint :
            (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ≃ₗ⋆[ℝ]
              (EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))
          A)
  let gStar : (Fin m → ℝ) → EReal := fenchelConjugate m g
  have hset :
      ∀ xStar : Fin n → ℝ,
        {yStar : EuclideanSpace ℝ (Fin m) | Aadj yStar = WithLp.toLp 2 xStar} =
          {yStar : EuclideanSpace ℝ (Fin m) | (Aadj yStar : Fin n → ℝ) = xStar} := by
    intro xStar
    ext yStar
    constructor
    · intro hy
      have hy' := congrArg (fun z : EuclideanSpace ℝ (Fin n) => (z : Fin n → ℝ)) hy
      simpa [WithLp.ofLp_toLp] using hy'
    · intro hy
      have hy' :=
        congrArg (fun z : Fin n → ℝ => (WithLp.toLp 2 z : EuclideanSpace ℝ (Fin n))) hy
      simpa [WithLp.toLp_ofLp] using hy'
  simpa [Aadj, gStar, hset, LinearMap.adjoint_adjoint] using
    (section16_fenchelConjugate_linearImage (A := Aadj) (f := gStar))

/-- The adjoint-image conjugate equals precomposition by `A` of the convex-function closure. -/
lemma section16_fenchelConjugate_adjoint_image_eq_precomp_convexFunctionClosure {n m : Nat}
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (g : (Fin m → ℝ) → EReal) (hg : ConvexFunction g) :
    let gStar : (Fin m → ℝ) → EReal := fenchelConjugate m g
    let h : (Fin n → ℝ) → EReal :=
      fun xStar : Fin n → ℝ =>
        sInf
          ((fun yStar : EuclideanSpace ℝ (Fin m) => gStar (yStar : Fin m → ℝ)) ''
            {yStar |
              ((LinearMap.adjoint :
                      (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ≃ₗ⋆[ℝ]
                        (EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))
                    A)
                  yStar =
                WithLp.toLp 2 xStar})
    fenchelConjugate n h =
      fun x : Fin n → ℝ => convexFunctionClosure g (A (WithLp.toLp 2 x) : Fin m → ℝ) := by
  classical
  let gStar : (Fin m → ℝ) → EReal := fenchelConjugate m g
  have hbiconj :
      fenchelConjugate m gStar = convexFunctionClosure g :=
    section16_fenchelConjugate_biconjugate_eq_convexFunctionClosure (n := m) (f := g) hg
  simpa [gStar, hbiconj] using
    (section16_fenchelConjugate_adjoint_image_eq_precomp_biconjugate (A := A) (g := g))

/-- Theorem 16.3.2: Let `A : ℝ^n →ₗ[ℝ] ℝ^m` be a linear transformation. For any convex function
`g` on `ℝ^m`, one has

`((cl g)A)^* = cl (A^* g^*)`.

Here `cl` denotes the convex-function closure (modeled as `convexFunctionClosure`), `g^*` is the
Fenchel conjugate `fenchelConjugate m g`, and `A^* g^*` is the direct image of `g^*` under the
adjoint of `A` (modeled by an `sInf` over the affine fiber `{yStar | A^* yStar = xStar}`). -/
theorem section16_fenchelConjugate_precomp_convexFunctionClosure_eq_convexFunctionClosure_adjoint_image
    {n m : Nat} (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (g : (Fin m → ℝ) → EReal) (hg : ConvexFunction g) :
    fenchelConjugate n (fun x => convexFunctionClosure g (A (WithLp.toLp 2 x) : Fin m → ℝ)) =
      convexFunctionClosure
        (fun xStar : Fin n → ℝ =>
          sInf
            ((fun yStar : EuclideanSpace ℝ (Fin m) =>
                  fenchelConjugate m g (yStar : Fin m → ℝ)) ''
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
  let gStar : (Fin m → ℝ) → EReal := fenchelConjugate m g
  let h : (Fin n → ℝ) → EReal :=
    fun xStar : Fin n → ℝ =>
      sInf
        ((fun yStar : EuclideanSpace ℝ (Fin m) => gStar (yStar : Fin m → ℝ)) ''
          {yStar |
            Aadj yStar =
              WithLp.toLp 2 xStar})
  have hprecomp :
      fenchelConjugate n h =
        fun x : Fin n → ℝ => convexFunctionClosure g (A (WithLp.toLp 2 x) : Fin m → ℝ) := by
    simpa [Aadj, gStar, h] using
      (section16_fenchelConjugate_adjoint_image_eq_precomp_convexFunctionClosure
        (A := A) (g := g) hg)
  have hconv : ConvexFunction h := by
    have hgStar : ConvexFunction gStar :=
      (fenchelConjugate_closedConvex (n := m) (f := g)).2
    have hset :
        ∀ xStar : Fin n → ℝ,
          {yStar : EuclideanSpace ℝ (Fin m) | Aadj yStar = WithLp.toLp 2 xStar} =
            {yStar : EuclideanSpace ℝ (Fin m) | (Aadj yStar : Fin n → ℝ) = xStar} := by
      intro xStar
      ext yStar
      constructor
      · intro hy
        have hy' := congrArg (fun z : EuclideanSpace ℝ (Fin n) => (z : Fin n → ℝ)) hy
        simpa [WithLp.ofLp_toLp] using hy'
      · intro hy
        have hy' :=
          congrArg (fun z : Fin n → ℝ => (WithLp.toLp 2 z : EuclideanSpace ℝ (Fin n))) hy
        simpa [WithLp.toLp_ofLp] using hy'
    simpa [Aadj, gStar, h, hset] using
      (section16_convexFunction_linearImage_sInf (A := Aadj) (f := gStar) hgStar)
  have hbiconj_h :
      fenchelConjugate n (fenchelConjugate n h) = convexFunctionClosure h :=
    section16_fenchelConjugate_biconjugate_eq_convexFunctionClosure (n := n) (f := h) hconv
  have hprecomp' :
      fenchelConjugate n
          (fun x => convexFunctionClosure g (A (WithLp.toLp 2 x) : Fin m → ℝ)) =
        fenchelConjugate n (fenchelConjugate n h) := by
    simpa using (congrArg (fun f => fenchelConjugate n f) hprecomp.symm)
  calc
    fenchelConjugate n
        (fun x => convexFunctionClosure g (A (WithLp.toLp 2 x) : Fin m → ℝ)) =
        fenchelConjugate n (fenchelConjugate n h) := hprecomp'
    _ = convexFunctionClosure h := hbiconj_h
    _ = _ := by
        simp [Aadj, h, gStar]

/-- Corollary 16.3.2.1. Let `A : ℝ^n →ₗ[ℝ] ℝ^m` be a linear transformation. For any convex set
`C ⊆ ℝ^n`, one has

`(A C)^* = A^{*-1} (C^*)`,

where `C^*` denotes the polar set and `A^{*-1}` denotes the preimage under the adjoint `A^*`. -/
theorem section16_polar_linearImage {n m : Nat}
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (C : Set (Fin n → ℝ)) :
    {yStar : Fin m → ℝ |
        ∀ y ∈ Set.image (fun x : Fin n → ℝ => (A (WithLp.toLp 2 x) : Fin m → ℝ)) C,
          (dotProduct y yStar : ℝ) ≤ 1} =
      Set.preimage
        (fun yStar : Fin m → ℝ =>
          (((LinearMap.adjoint :
                    (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ≃ₗ⋆[ℝ]
                      (EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))
                  A)
              (WithLp.toLp 2 yStar) : Fin n → ℝ))
        {xStar : Fin n → ℝ | ∀ x ∈ C, (dotProduct x xStar : ℝ) ≤ 1} := by
  let Aadj :
      EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    ((LinearMap.adjoint :
            (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ≃ₗ⋆[ℝ]
              (EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))
          A)
  ext yStar
  constructor
  · intro hy
    have hy' :
        ∀ x ∈ C,
          (dotProduct x (Aadj (WithLp.toLp 2 yStar) : Fin n → ℝ) : ℝ) ≤ 1 := by
      intro x hxC
      have hyx :
          (dotProduct (A (WithLp.toLp 2 x) : Fin m → ℝ) yStar : ℝ) ≤ 1 :=
        hy (A (WithLp.toLp 2 x) : Fin m → ℝ) ⟨x, hxC, rfl⟩
      calc
        (dotProduct x (Aadj (WithLp.toLp 2 yStar) : Fin n → ℝ) : ℝ) =
            dotProduct (A (WithLp.toLp 2 x) : Fin m → ℝ) yStar := by
              simpa [Aadj] using
                (section16_dotProduct_map_eq_dotProduct_adjoint
                  (A := A) (x := x) (yStar := yStar)).symm
        _ ≤ 1 := hyx
    simpa [Set.preimage, Aadj] using hy'
  · intro hy
    have hy' :
        ∀ x ∈ C,
          (dotProduct x (Aadj (WithLp.toLp 2 yStar) : Fin n → ℝ) : ℝ) ≤ 1 := by
      simpa [Set.preimage, Aadj] using hy
    rintro y ⟨x, hxC, rfl⟩
    have hyx := hy' x hxC
    calc
      (dotProduct (A (WithLp.toLp 2 x) : Fin m → ℝ) yStar : ℝ) =
          dotProduct x (Aadj (WithLp.toLp 2 yStar) : Fin n → ℝ) := by
            simpa [Aadj] using
              (section16_dotProduct_map_eq_dotProduct_adjoint
                (A := A) (x := x) (yStar := yStar))
      _ ≤ 1 := hyx

/-- Closure of a `≤ 1` sublevel set matches the `≤ 1` sublevel of the convex-function closure. -/
lemma section16_closure_sublevel_eq_sublevel_convexFunctionClosure_one {n : Nat}
    {h : (Fin n → ℝ) → EReal}
    (hh : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h)
    (hInf : iInf (fun x => h x) < (1 : EReal)) :
    closure {x : EuclideanSpace ℝ (Fin n) | h (x : Fin n → ℝ) ≤ (1 : EReal)} =
      {x : EuclideanSpace ℝ (Fin n) |
        convexFunctionClosure h (x : Fin n → ℝ) ≤ (1 : EReal)} := by
  have hlevel :=
    (properConvexFunction_levelSets_same_closure_ri_dim (n := n) (f := h) hh
      (α := (1 : ℝ)) hInf)
  simpa using hlevel.1

/-- The adjoint image of the support-function sublevel lies in the fiberwise `sInf` sublevel. -/
lemma section16_image_adjoint_polar_subset_sublevel_sInf {n m : Nat}
    (Aadj : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (D : Set (Fin m → ℝ)) :
    Set.image
        (fun yStar : Fin m → ℝ => (Aadj (WithLp.toLp 2 yStar) : Fin n → ℝ))
        {yStar : Fin m → ℝ | supportFunctionEReal D yStar ≤ (1 : EReal)} ⊆
      {xStar : Fin n → ℝ |
        sInf
            ((fun yStar : EuclideanSpace ℝ (Fin m) =>
                  supportFunctionEReal D (yStar : Fin m → ℝ)) ''
              {yStar | Aadj yStar = WithLp.toLp 2 xStar}) ≤ (1 : EReal)} := by
  classical
  rintro xStar ⟨yStar, hyStar, rfl⟩
  have hmem :
      supportFunctionEReal D yStar ∈
        (fun yStar' : EuclideanSpace ℝ (Fin m) =>
            supportFunctionEReal D (yStar' : Fin m → ℝ)) ''
          {yStar' |
            Aadj yStar' = WithLp.toLp 2 (Aadj (WithLp.toLp 2 yStar) : Fin n → ℝ)} := by
    refine ⟨WithLp.toLp 2 yStar, ?_, ?_⟩
    · simp [WithLp.toLp_ofLp]
    · simp
  have hle :
      sInf
          ((fun yStar' : EuclideanSpace ℝ (Fin m) =>
                supportFunctionEReal D (yStar' : Fin m → ℝ)) ''
            {yStar' |
              Aadj yStar' = WithLp.toLp 2 (Aadj (WithLp.toLp 2 yStar) : Fin n → ℝ)}) ≤
        supportFunctionEReal D yStar := by
    exact sInf_le hmem
  have hfinal :
      sInf
          ((fun yStar' : EuclideanSpace ℝ (Fin m) =>
                supportFunctionEReal D (yStar' : Fin m → ℝ)) ''
            {yStar' |
              Aadj yStar' = WithLp.toLp 2 (Aadj (WithLp.toLp 2 yStar) : Fin n → ℝ)}) ≤
        (1 : EReal) := le_trans hle hyStar
  simp only [Set.mem_setOf_eq]
  exact hfinal

/-!
Helper lemmas for the polar/sublevel closure correspondence.
-/

/-- The fiberwise `sInf` at the origin is bounded by `0`. -/
lemma section16_sInf_fiber_zero_le {n m : Nat}
    (Aadj : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (D : Set (Fin m → ℝ)) :
    sInf
        ((fun yStar : EuclideanSpace ℝ (Fin m) =>
              supportFunctionEReal D (yStar : Fin m → ℝ)) ''
          {yStar | Aadj yStar = WithLp.toLp 2 (0 : Fin n → ℝ)}) ≤
      (0 : EReal) := by
  classical
  have hmem :
      supportFunctionEReal D (0 : Fin m → ℝ) ∈
        (fun yStar : EuclideanSpace ℝ (Fin m) =>
            supportFunctionEReal D (yStar : Fin m → ℝ)) ''
          {yStar | Aadj yStar = WithLp.toLp 2 (0 : Fin n → ℝ)} := by
    refine ⟨(0 : EuclideanSpace ℝ (Fin m)), ?_, rfl⟩
    simp
  have hle :
      sInf
          ((fun yStar : EuclideanSpace ℝ (Fin m) =>
                supportFunctionEReal D (yStar : Fin m → ℝ)) ''
            {yStar | Aadj yStar = WithLp.toLp 2 (0 : Fin n → ℝ)}) ≤
        supportFunctionEReal D (0 : Fin m → ℝ) := by
    exact sInf_le hmem
  have hle0 : supportFunctionEReal D (0 : Fin m → ℝ) ≤ (0 : EReal) := by
    unfold supportFunctionEReal
    refine sSup_le ?_
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    simp
  exact le_trans hle hle0

/-- Reverse inclusion for `section16_closure_image_adjoint_polar_eq_closure_sublevel_sInf`. -/
lemma section16_closure_image_adjoint_polar_eq_closure_sublevel_sInf_reverse {n m : Nat}
    (Aadj : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (D : Set (Fin m → ℝ)) :
    {xStar : Fin n → ℝ |
        sInf
            ((fun yStar : EuclideanSpace ℝ (Fin m) =>
                  supportFunctionEReal D (yStar : Fin m → ℝ)) ''
              {yStar | Aadj yStar = WithLp.toLp 2 xStar}) ≤ (1 : EReal)} ⊆
      closure
        (Set.image
          (fun yStar : Fin m → ℝ => (Aadj (WithLp.toLp 2 yStar) : Fin n → ℝ))
          {yStar : Fin m → ℝ | supportFunctionEReal D yStar ≤ (1 : EReal)}) := by
  classical
  intro xStar hx
  refine Metric.mem_closure_iff.2 ?_
  intro ε hε
  by_cases hx0 : xStar = 0
  · subst hx0
    have hle0 :
        supportFunctionEReal D (0 : Fin m → ℝ) ≤ (0 : EReal) := by
      unfold supportFunctionEReal
      refine sSup_le ?_
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      simp
    have hmem :
        (0 : Fin n → ℝ) ∈
          Set.image
            (fun yStar : Fin m → ℝ => (Aadj (WithLp.toLp 2 yStar) : Fin n → ℝ))
            {yStar : Fin m → ℝ | supportFunctionEReal D yStar ≤ (1 : EReal)} := by
      refine ⟨(0 : Fin m → ℝ), ?_, ?_⟩
      · exact le_trans hle0 (by
          exact_mod_cast (by linarith : (0 : ℝ) ≤ 1))
      · simp
    refine ⟨(0 : Fin n → ℝ), hmem, ?_⟩
    simp [hε]
  ·
    have hxnorm : 0 < ‖xStar‖ := by
      have : xStar ≠ 0 := hx0
      simpa using (norm_pos_iff.mpr this)
    set δ : ℝ := ε / ‖xStar‖ with hδ
    have hδpos : 0 < δ := by
      exact div_pos hε hxnorm
    set t : ℝ := 1 / (1 + δ) with ht
    have htpos : 0 < t := by
      have h1δpos : 0 < 1 + δ := by linarith
      simpa [ht] using (one_div_pos.2 h1δpos)
    have hlt : (1 : EReal) < (1 + δ : EReal) := by
      exact_mod_cast (by linarith : (1 : ℝ) < 1 + δ)
    have hsInf_lt :
        sInf
            ((fun yStar : EuclideanSpace ℝ (Fin m) =>
                  supportFunctionEReal D (yStar : Fin m → ℝ)) ''
              {yStar | Aadj yStar = WithLp.toLp 2 xStar}) <
          (1 + δ : EReal) := lt_of_le_of_lt hx hlt
    rcases (sInf_lt_iff).1 hsInf_lt with ⟨z, hzmem, hzlt⟩
    rcases hzmem with ⟨yStar, hyA, rfl⟩
    have hy_le :
        supportFunctionEReal D (yStar : Fin m → ℝ) ≤ (1 + δ : EReal) :=
      le_of_lt hzlt
    have hy_bound :
        ∀ x ∈ D, (dotProduct x (yStar : Fin m → ℝ) : ℝ) ≤ 1 + δ := by
      exact
        (section13_supportFunctionEReal_le_coe_iff
            (C := D) (y := (yStar : Fin m → ℝ)) (μ := 1 + δ)).1 hy_le
    have hscaled :
        supportFunctionEReal D (t • (yStar : Fin m → ℝ)) ≤ (1 : EReal) := by
      refine
        (section13_supportFunctionEReal_le_coe_iff
            (C := D) (y := t • (yStar : Fin m → ℝ)) (μ := 1)).2 ?_
      intro x hxD
      have hxle : (dotProduct x (yStar : Fin m → ℝ) : ℝ) ≤ 1 + δ := hy_bound x hxD
      have hdot :
          (dotProduct x (t • (yStar : Fin m → ℝ)) : ℝ) =
            t * dotProduct x (yStar : Fin m → ℝ) := by
        simp [dotProduct_smul, smul_eq_mul, mul_comm]
      have ht_nonneg : 0 ≤ t := le_of_lt htpos
      have hmul : t * dotProduct x (yStar : Fin m → ℝ) ≤ t * (1 + δ) :=
        mul_le_mul_of_nonneg_left hxle ht_nonneg
      have ht_one : t * (1 + δ) = 1 := by
        have h1δne : (1 + δ) ≠ 0 := by linarith
        simp [ht, h1δne]
      calc
        (dotProduct x (t • (yStar : Fin m → ℝ)) : ℝ) =
            t * dotProduct x (yStar : Fin m → ℝ) := hdot
        _ ≤ t * (1 + δ) := hmul
        _ = 1 := ht_one
    have himage :
        (Aadj (WithLp.toLp 2 (t • (yStar : Fin m → ℝ))) : Fin n → ℝ) ∈
          Set.image
            (fun yStar : Fin m → ℝ => (Aadj (WithLp.toLp 2 yStar) : Fin n → ℝ))
            {yStar : Fin m → ℝ | supportFunctionEReal D yStar ≤ (1 : EReal)} := by
      refine ⟨t • (yStar : Fin m → ℝ), hscaled, rfl⟩
    have hyA' : (Aadj yStar : Fin n → ℝ) = xStar := by
      have hyA' := congrArg (fun z : EuclideanSpace ℝ (Fin n) => (z : Fin n → ℝ)) hyA
      simpa [WithLp.ofLp_toLp] using hyA'
    have himage_eq :
        (Aadj (WithLp.toLp 2 (t • (yStar : Fin m → ℝ))) : Fin n → ℝ) = t • xStar := by
      simp [map_smul, hyA']
    have hdist_lt : dist (t • xStar) xStar < ε := by
      have hsub :
          t • xStar - xStar = (t - 1) • xStar := by
        simpa using (sub_smul t (1 : ℝ) xStar).symm
      have hdist :
          dist (t • xStar) xStar = |t - 1| * ‖xStar‖ := by
        simp [dist_eq_norm, hsub, norm_smul]
      have htlt : t < 1 := by
        have h1δ : (1 : ℝ) < 1 + δ := by linarith
        have h := one_div_lt_one_div_of_lt (a := (1 : ℝ)) (b := 1 + δ) (by norm_num) h1δ
        simpa [ht] using h
      have h1t : 1 - t = δ * (1 / (1 + δ)) := by
        have h1δne : (1 + δ) ≠ 0 := by linarith
        have haux : 1 - (1 / (1 + δ)) = δ / (1 + δ) := by
          field_simp [h1δne]
          ring
        calc
          1 - t = 1 - (1 / (1 + δ)) := by simp [ht]
          _ = δ / (1 + δ) := haux
          _ = δ * (1 / (1 + δ)) := by
              simp [div_eq_mul_inv]
      have hfrac : (1 / (1 + δ) : ℝ) < 1 := by
        have h1δ : (1 : ℝ) < 1 + δ := by linarith
        have h := one_div_lt_one_div_of_lt (a := (1 : ℝ)) (b := 1 + δ) (by norm_num) h1δ
        simpa using h
      have hmul : δ * (1 / (1 + δ) : ℝ) < δ := by
        have hδpos' : 0 < δ := hδpos
        have h := mul_lt_mul_of_pos_left hfrac hδpos'
        simpa using h
      have habs_lt : |t - 1| < δ := by
        have htle : t - 1 ≤ 0 := by linarith [htlt]
        have habs : |t - 1| = 1 - t := by
          have habs' := abs_of_nonpos htle
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using habs'
        have h1t_lt : 1 - t < δ := by
          simpa [h1t] using hmul
        simpa [habs] using h1t_lt
      have hmul_lt : |t - 1| * ‖xStar‖ < δ * ‖xStar‖ := by
        exact mul_lt_mul_of_pos_right habs_lt hxnorm
      have hδε : δ * ‖xStar‖ = ε := by
        have hxne : ‖xStar‖ ≠ 0 := by exact ne_of_gt hxnorm
        calc
          δ * ‖xStar‖ = (ε / ‖xStar‖) * ‖xStar‖ := by simp [hδ]
          _ = ε := by
              field_simp [hxne]
      have hmul_lt' : |t - 1| * ‖xStar‖ < ε := by
        simpa [hδε] using hmul_lt
      simpa [hdist] using hmul_lt'
    refine ⟨(Aadj (WithLp.toLp 2 (t • (yStar : Fin m → ℝ))) : Fin n → ℝ), himage, ?_⟩
    have hdist_lt' : dist xStar (t • (Aadj yStar : Fin n → ℝ)) < ε := by
      simpa [hyA', dist_comm] using hdist_lt
    simpa using hdist_lt'

/-- The closure of the adjoint image of the polar sublevel equals the closure of the `sInf` sublevel. -/
lemma section16_closure_image_adjoint_polar_eq_closure_sublevel_sInf {n m : Nat}
    (Aadj : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (D : Set (Fin m → ℝ)) :
    closure
        (Set.image
          (fun yStar : Fin m → ℝ => (Aadj (WithLp.toLp 2 yStar) : Fin n → ℝ))
          {yStar : Fin m → ℝ | supportFunctionEReal D yStar ≤ (1 : EReal)}) =
      closure
        {xStar : Fin n → ℝ |
          sInf
              ((fun yStar : EuclideanSpace ℝ (Fin m) =>
                    supportFunctionEReal D (yStar : Fin m → ℝ)) ''
                {yStar | Aadj yStar = WithLp.toLp 2 xStar}) ≤ (1 : EReal)} := by
  classical
  apply subset_antisymm
  ·
    refine closure_mono ?_
    exact section16_image_adjoint_polar_subset_sublevel_sInf (Aadj := Aadj) (D := D)
  ·
    refine closure_minimal ?_ isClosed_closure
    exact
      section16_closure_image_adjoint_polar_eq_closure_sublevel_sInf_reverse (Aadj := Aadj) (D := D)

/-- Properness of the fiberwise `sInf` under `0 ∈ closure D`. -/
lemma section16_properConvexFunctionOn_h_of_zero_mem_closure {n m : Nat}
    (Aadj : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (D : Set (Fin m → ℝ)) (hD : Convex ℝ D)
    (h0D : (0 : Fin m → ℝ) ∈ closure D) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
      (fun xStar : Fin n → ℝ =>
        sInf
          ((fun yStar : EuclideanSpace ℝ (Fin m) =>
                supportFunctionEReal D (yStar : Fin m → ℝ)) ''
            {yStar | Aadj yStar = WithLp.toLp 2 xStar})) := by
  classical
  have hDne : D.Nonempty := by
    by_contra hDne
    have hDempty : D = ∅ := (Set.not_nonempty_iff_eq_empty).1 hDne
    simp [hDempty] at h0D
  have hnonneg_supp :
      ∀ yStar : Fin m → ℝ, (0 : EReal) ≤ supportFunctionEReal D yStar := by
    have hiff :=
      section13_zero_mem_closure_iff_forall_zero_le_supportFunctionEReal (C := D) hD hDne
    exact (hiff.mp h0D)
  have hconv :
      ConvexFunction
        (fun xStar : Fin n → ℝ =>
          sInf
            ((fun yStar : EuclideanSpace ℝ (Fin m) =>
                  supportFunctionEReal D (yStar : Fin m → ℝ)) ''
              {yStar | Aadj yStar = WithLp.toLp 2 xStar})) := by
    have hf :
        ConvexFunction (supportFunctionEReal D) :=
      (section13_supportFunctionEReal_closedProperConvex_posHom (n := m) (C := D) hDne hD).1.1
    have hconv' :=
      section16_convexFunction_linearImage_sInf_part3 (Aadj := Aadj)
        (f := supportFunctionEReal D) hf
    simpa [section16_fiber_set_eq_toLp_fiber_set (Aadj := Aadj)] using hconv'
  have hconv_on :
      ConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (fun xStar : Fin n → ℝ =>
          sInf
            ((fun yStar : EuclideanSpace ℝ (Fin m) =>
                  supportFunctionEReal D (yStar : Fin m → ℝ)) ''
              {yStar | Aadj yStar = WithLp.toLp 2 xStar})) := by
    simpa [ConvexFunction] using hconv
  have hnonneg_h :
      ∀ xStar : Fin n → ℝ,
        (0 : EReal) ≤
          sInf
            ((fun yStar : EuclideanSpace ℝ (Fin m) =>
                  supportFunctionEReal D (yStar : Fin m → ℝ)) ''
              {yStar | Aadj yStar = WithLp.toLp 2 xStar}) := by
    intro xStar
    refine le_sInf ?_
    intro z hz
    rcases hz with ⟨yStar, hyA, rfl⟩
    exact hnonneg_supp (yStar : Fin m → ℝ)
  have hnotbot :
      ∀ xStar : Fin n → ℝ,
        sInf
            ((fun yStar : EuclideanSpace ℝ (Fin m) =>
                  supportFunctionEReal D (yStar : Fin m → ℝ)) ''
              {yStar | Aadj yStar = WithLp.toLp 2 xStar}) ≠ (⊥ : EReal) := by
    intro xStar
    exact
      ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (hnonneg_h xStar))
  have h0_le :
      sInf
          ((fun yStar : EuclideanSpace ℝ (Fin m) =>
                supportFunctionEReal D (yStar : Fin m → ℝ)) ''
            {yStar | Aadj yStar = WithLp.toLp 2 (0 : Fin n → ℝ)}) ≤
        (0 : EReal) :=
    section16_sInf_fiber_zero_le (Aadj := Aadj) (D := D)
  have hnonempty_epi :
      Set.Nonempty
        (epigraph (Set.univ : Set (Fin n → ℝ))
          (fun xStar : Fin n → ℝ =>
            sInf
              ((fun yStar : EuclideanSpace ℝ (Fin m) =>
                    supportFunctionEReal D (yStar : Fin m → ℝ)) ''
                {yStar | Aadj yStar = WithLp.toLp 2 xStar}))) := by
    refine ⟨(0, (0 : ℝ)), ?_⟩
    refine ⟨(by
      simp : (0 : Fin n → ℝ) ∈ (Set.univ : Set (Fin n → ℝ))), ?_⟩
    exact h0_le
  refine ⟨hconv_on, hnonempty_epi, ?_⟩
  intro xStar hx
  exact hnotbot xStar

/-- The fiberwise infimum is strictly below `1` under `0 ∈ closure D`. -/
lemma section16_iInf_h_lt_one_of_zero_mem_closure {n m : Nat}
    (Aadj : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (D : Set (Fin m → ℝ)) :
    iInf
        (fun xStar : Fin n → ℝ =>
          sInf
            ((fun yStar : EuclideanSpace ℝ (Fin m) =>
                  supportFunctionEReal D (yStar : Fin m → ℝ)) ''
              {yStar | Aadj yStar = WithLp.toLp 2 xStar})) <
      (1 : EReal) := by
  have h0_le :
      sInf
          ((fun yStar : EuclideanSpace ℝ (Fin m) =>
                supportFunctionEReal D (yStar : Fin m → ℝ)) ''
            {yStar | Aadj yStar = WithLp.toLp 2 (0 : Fin n → ℝ)}) ≤
        (0 : EReal) :=
    section16_sInf_fiber_zero_le (Aadj := Aadj) (D := D)
  have hInf_le :
      iInf
          (fun xStar : Fin n → ℝ =>
            sInf
              ((fun yStar : EuclideanSpace ℝ (Fin m) =>
                    supportFunctionEReal D (yStar : Fin m → ℝ)) ''
                {yStar | Aadj yStar = WithLp.toLp 2 xStar})) ≤
        sInf
          ((fun yStar : EuclideanSpace ℝ (Fin m) =>
                supportFunctionEReal D (yStar : Fin m → ℝ)) ''
            {yStar | Aadj yStar = WithLp.toLp 2 (0 : Fin n → ℝ)}) := by
    exact iInf_le (fun xStar : Fin n → ℝ =>
      sInf
        ((fun yStar : EuclideanSpace ℝ (Fin m) =>
              supportFunctionEReal D (yStar : Fin m → ℝ)) ''
          {yStar | Aadj yStar = WithLp.toLp 2 xStar})) (0 : Fin n → ℝ)
  have hInf_le0 :
      iInf
          (fun xStar : Fin n → ℝ =>
            sInf
              ((fun yStar : EuclideanSpace ℝ (Fin m) =>
                    supportFunctionEReal D (yStar : Fin m → ℝ)) ''
                {yStar | Aadj yStar = WithLp.toLp 2 xStar})) ≤
        (0 : EReal) :=
    le_trans hInf_le h0_le
  have h0lt1 : (0 : EReal) < (1 : EReal) := by
    exact_mod_cast (by norm_num : (0 : ℝ) < 1)
  exact lt_of_le_of_lt hInf_le0 h0lt1

/-- Corollary 16.3.2.2. Let `A` be a linear transformation from `ℝ^n` to `ℝ^m`. For any convex
set `D ⊆ ℝ^m` with `0 ∈ cl D`, one has

`(A⁻¹ (cl D))^* = cl (A^* (D^*))`,

where `cl` is the topological closure of sets, `D^*` is the polar set, and `A^*` is the adjoint
of `A`. -/
theorem section16_polar_preimage_closure_eq_closure_adjoint_image {n m : Nat}
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (D : Set (Fin m → ℝ)) (hD : Convex ℝ D) (h0D : (0 : Fin m → ℝ) ∈ closure D) :
    {xStar : Fin n → ℝ |
        ∀ x ∈ Set.preimage (fun x : Fin n → ℝ => (A (WithLp.toLp 2 x) : Fin m → ℝ)) (closure D),
          (dotProduct x xStar : ℝ) ≤ 1} =
      closure
        (Set.image
          (fun yStar : Fin m → ℝ =>
            (((LinearMap.adjoint :
                      (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ≃ₗ⋆[ℝ]
                        (EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))
                    A)
                (WithLp.toLp 2 yStar) : Fin n → ℝ))
          {yStar : Fin m → ℝ | ∀ y ∈ D, (dotProduct y yStar : ℝ) ≤ 1}) := by
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
        ((fun yStar : EuclideanSpace ℝ (Fin m) =>
              supportFunctionEReal D (yStar : Fin m → ℝ)) ''
          {yStar | Aadj yStar = WithLp.toLp 2 xStar})
  have hpolar_preimage :
      {xStar : Fin n → ℝ |
          ∀ x ∈ Set.preimage
                (fun x : Fin n → ℝ => (A (WithLp.toLp 2 x) : Fin m → ℝ)) (closure D),
            (dotProduct x xStar : ℝ) ≤ 1} =
        {xStar : Fin n → ℝ |
          supportFunctionEReal
              (Set.preimage
                (fun x : Fin n → ℝ => (A (WithLp.toLp 2 x) : Fin m → ℝ)) (closure D))
              xStar ≤ (1 : EReal)} := by
    simpa using
      (section16_polar_eq_sublevel_deltaStar
        (C :=
          Set.preimage
            (fun x : Fin n → ℝ => (A (WithLp.toLp 2 x) : Fin m → ℝ)) (closure D)))
  have hpolar_D :
      {yStar : Fin m → ℝ | ∀ y ∈ D, (dotProduct y yStar : ℝ) ≤ 1} =
        {yStar : Fin m → ℝ | supportFunctionEReal D yStar ≤ (1 : EReal)} := by
    simpa using (section16_polar_eq_sublevel_deltaStar (C := D))
  have hsupport :
      supportFunctionEReal
          (Set.preimage
            (fun x : Fin n → ℝ => (A (WithLp.toLp 2 x) : Fin m → ℝ)) (closure D)) =
        convexFunctionClosure h := by
    simpa [Aadj, h] using
      (section16_supportFunctionEReal_preimage_closure_eq_convexFunctionClosure_adjoint_image
        (A := A) (D := D) hD)
  have hsublevel :
      {xStar : Fin n → ℝ |
          supportFunctionEReal
              (Set.preimage
                (fun x : Fin n → ℝ => (A (WithLp.toLp 2 x) : Fin m → ℝ)) (closure D))
              xStar ≤ (1 : EReal)} =
        {xStar : Fin n → ℝ | convexFunctionClosure h xStar ≤ (1 : EReal)} := by
    ext xStar
    simp [hsupport]
  have hclosure_image :
      closure
          (Set.image
            (fun yStar : Fin m → ℝ => (Aadj (WithLp.toLp 2 yStar) : Fin n → ℝ))
            {yStar : Fin m → ℝ | supportFunctionEReal D yStar ≤ (1 : EReal)}) =
        closure {xStar : Fin n → ℝ | h xStar ≤ (1 : EReal)} := by
    simpa [Aadj, h] using
      (section16_closure_image_adjoint_polar_eq_closure_sublevel_sInf (Aadj := Aadj) (D := D))
  have hclosure_sublevel :
      closure {xStar : Fin n → ℝ | h xStar ≤ (1 : EReal)} =
        {xStar : Fin n → ℝ | convexFunctionClosure h xStar ≤ (1 : EReal)} := by
    have hh :
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h := by
      simpa [h] using
        (section16_properConvexFunctionOn_h_of_zero_mem_closure
          (Aadj := Aadj) (D := D) hD h0D)
    have hInf : iInf (fun x => h x) < (1 : EReal) := by
      simpa [h] using
        (section16_iInf_h_lt_one_of_zero_mem_closure (Aadj := Aadj) (D := D))
    -- Transport the Euclidean-space closure statement to `Fin n → ℝ` via `WithLp.toLp`.
    let S : Set (EuclideanSpace ℝ (Fin n)) :=
      {x | h (x : Fin n → ℝ) ≤ (1 : EReal)}
    let T : Set (EuclideanSpace ℝ (Fin n)) :=
      {x | convexFunctionClosure h (x : Fin n → ℝ) ≤ (1 : EReal)}
    have hclosure_sublevel' :
        closure S = T := by
      simpa [S, T] using
        (section16_closure_sublevel_eq_sublevel_convexFunctionClosure_one (h := h) hh hInf)
    let e := (EuclideanSpace.equiv (Fin n) ℝ)
    have himage_S :
        (fun x : EuclideanSpace ℝ (Fin n) => (e x : Fin n → ℝ)) '' S =
          {xStar : Fin n → ℝ | h xStar ≤ (1 : EReal)} := by
      ext xStar
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa using hx
      · intro hx
        refine ⟨e.symm xStar, ?_, ?_⟩
        · simpa [e.apply_symm_apply] using hx
        · simp [e.apply_symm_apply]
    have himage_T :
        (fun x : EuclideanSpace ℝ (Fin n) => (e x : Fin n → ℝ)) '' T =
          {xStar : Fin n → ℝ | convexFunctionClosure h xStar ≤ (1 : EReal)} := by
      ext xStar
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa using hx
      · intro hx
        refine ⟨e.symm xStar, ?_, ?_⟩
        · simpa [e.apply_symm_apply] using hx
        · simp [e.apply_symm_apply]
    have himage_closure_S :
        (fun x : EuclideanSpace ℝ (Fin n) => (e x : Fin n → ℝ)) '' closure S =
          closure
            ((fun x : EuclideanSpace ℝ (Fin n) => (e x : Fin n → ℝ)) '' S) := by
      simpa using
        (Homeomorph.image_closure (h := e.toHomeomorph) (s := S))
    have himage :=
      congrArg
        (fun s =>
          (fun x : EuclideanSpace ℝ (Fin n) => (e x : Fin n → ℝ)) '' s)
        hclosure_sublevel'
    have hclosure_fun :
        closure {xStar : Fin n → ℝ | h xStar ≤ (1 : EReal)} =
          {xStar : Fin n → ℝ | convexFunctionClosure h xStar ≤ (1 : EReal)} := by
      -- Rewrite the transported equality using the image/closure lemmas above.
      simpa [himage_S, himage_T, himage_closure_S] using himage
    exact hclosure_fun
  have hfinal :
      {xStar : Fin n → ℝ |
          ∀ x ∈ Set.preimage
                (fun x : Fin n → ℝ => (A (WithLp.toLp 2 x) : Fin m → ℝ)) (closure D),
            (dotProduct x xStar : ℝ) ≤ 1} =
        closure
          (Set.image
            (fun yStar : Fin m → ℝ => (Aadj (WithLp.toLp 2 yStar) : Fin n → ℝ))
            {yStar : Fin m → ℝ | supportFunctionEReal D yStar ≤ (1 : EReal)}) := by
    calc
      {xStar : Fin n → ℝ |
          ∀ x ∈ Set.preimage
                (fun x : Fin n → ℝ => (A (WithLp.toLp 2 x) : Fin m → ℝ)) (closure D),
            (dotProduct x xStar : ℝ) ≤ 1} =
          {xStar : Fin n → ℝ |
            supportFunctionEReal
                (Set.preimage
                  (fun x : Fin n → ℝ => (A (WithLp.toLp 2 x) : Fin m → ℝ)) (closure D))
                xStar ≤ (1 : EReal)} := hpolar_preimage
      _ = {xStar : Fin n → ℝ | convexFunctionClosure h xStar ≤ (1 : EReal)} := hsublevel
      _ = closure {xStar : Fin n → ℝ | h xStar ≤ (1 : EReal)} := by
          symm
          exact hclosure_sublevel
      _ =
          closure
            (Set.image
              (fun yStar : Fin m → ℝ => (Aadj (WithLp.toLp 2 yStar) : Fin n → ℝ))
              {yStar : Fin m → ℝ | supportFunctionEReal D yStar ≤ (1 : EReal)}) := by
          symm
          exact hclosure_image
  simpa [hpolar_D] using hfinal

/-- Rewriting `sInf` of an image by an explicit existential description. -/
lemma section16_sInf_image_fiber_eq_sInf_exists {α : Type*} (φ : α → EReal) (S : Set α) :
    sInf (φ '' S) = sInf {z : EReal | ∃ y ∈ S, z = φ y} := by
  classical
  have hset : φ '' S = {z : EReal | ∃ y ∈ S, z = φ y} := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
  simp [hset]

/-- For a proper function, the recession function agrees with the unrestricted formula. -/
lemma section16_recessionFunction_eq_sSup_unrestricted {n : Nat}
    {f : (Fin n → ℝ) → EReal} (y : Fin n → ℝ) :
    recessionFunction f y =
      sSup { r : EReal | ∃ x : Fin n → ℝ, r = f (x + y) - f x } := by
  classical
  set S : Set EReal :=
    { r : EReal |
      ∃ x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f, r = f (x + y) - f x } with hS
  set T : Set EReal :=
    { r : EReal | ∃ x : Fin n → ℝ, r = f (x + y) - f x } with hT
  have hle1 : sSup S ≤ sSup T := by
    refine sSup_le ?_
    intro r hr
    rcases hr with ⟨x, hx, rfl⟩
    exact le_sSup ⟨x, rfl⟩
  have hle2 : sSup T ≤ sSup S := by
    refine sSup_le ?_
    intro r hr
    rcases hr with ⟨x, rfl⟩
    by_cases htop : f x = ⊤
    · have hrbot : f (x + y) - f x = (⊥ : EReal) := by
        simp [htop]
      simp [hrbot]
    · have hx : x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f := by
        have hx' : x ∈ (Set.univ : Set (Fin n → ℝ)) ∧ f x < (⊤ : EReal) := by
          refine ⟨by simp, ?_⟩
          exact (lt_top_iff_ne_top).2 htop
        simpa [effectiveDomain_eq] using hx'
      exact le_sSup ⟨x, hx, rfl⟩
  have hsup : sSup S = sSup T := le_antisymm hle1 hle2
  simpa [recessionFunction, hS, hT] using hsup


end Section16
end Chap03
