/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Weiran Shi, Yunxi Duan, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section13_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section13_part6
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section13_part10
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section06_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chap01.section05_part7
import Books.ConvexAnalysis_Rockafellar_1970.Chap01.section05_part10
import Books.ConvexAnalysis_Rockafellar_1970.Chap01.section05_part2

section Chap03
section Section16

open scoped BigOperators
open scoped Pointwise

/-- Dot product is additive in the left argument. -/
lemma section16_dotProduct_add_left {n : ℕ} (u v w : Fin n → ℝ) :
    dotProduct (u + v) w = dotProduct u w + dotProduct v w := by
  calc
    dotProduct (u + v) w = dotProduct w (u + v) := by simp [dotProduct_comm]
    _ = dotProduct w u + dotProduct w v := by
      simp
    _ = dotProduct u w + dotProduct v w := by
      simp [dotProduct_comm]

/-- Translate the Fenchel conjugate range under `x ↦ x - a`. -/
lemma section16_range_fenchelConjugate_translate {n : ℕ} (h : (Fin n → ℝ) → EReal)
    (a xStar : Fin n → ℝ) :
    Set.range (fun x => ((x ⬝ᵥ xStar : ℝ) : EReal) - h (x - a)) =
      (fun z : EReal => z + ((dotProduct a xStar : ℝ) : EReal)) ''
        Set.range (fun y => ((y ⬝ᵥ xStar : ℝ) : EReal) - h y) := by
  classical
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨(((x - a) ⬝ᵥ xStar : ℝ) : EReal) - h (x - a), ?_⟩
    refine ⟨⟨x - a, rfl⟩, ?_⟩
    have hdot :
        (x ⬝ᵥ xStar : ℝ) = (x - a) ⬝ᵥ xStar + dotProduct a xStar := by
      calc
        x ⬝ᵥ xStar = ((x - a) + a) ⬝ᵥ xStar := by
          simp
        _ = (x - a) ⬝ᵥ xStar + a ⬝ᵥ xStar := by
          simp
        _ = (x - a) ⬝ᵥ xStar + dotProduct a xStar := by rfl
    have hdot' :
        ((x ⬝ᵥ xStar : ℝ) : EReal) =
          ((x - a) ⬝ᵥ xStar : ℝ) + ((dotProduct a xStar : ℝ) : EReal) := by
      calc
        ((x ⬝ᵥ xStar : ℝ) : EReal) =
            (((x - a) ⬝ᵥ xStar + dotProduct a xStar : ℝ) : EReal) := by
          rw [hdot]
        _ = ((x - a) ⬝ᵥ xStar : ℝ) + ((dotProduct a xStar : ℝ) : EReal) := by
          simpa using (EReal.coe_add ((x - a) ⬝ᵥ xStar) (dotProduct a xStar))
    calc
      (((x - a) ⬝ᵥ xStar : ℝ) : EReal) - h (x - a) + ((dotProduct a xStar : ℝ) : EReal) =
          ((((x - a) ⬝ᵥ xStar : ℝ) : EReal) + ((dotProduct a xStar : ℝ) : EReal)) -
            h (x - a) := by
        simp [sub_eq_add_neg, add_assoc, add_comm]
      _ = ((x ⬝ᵥ xStar : ℝ) : EReal) - h (x - a) := by
        rw [hdot'.symm]
  · rintro ⟨z, ⟨y, rfl⟩, rfl⟩
    refine ⟨y + a, ?_⟩
    have hdot :
        (y + a) ⬝ᵥ xStar = y ⬝ᵥ xStar + dotProduct a xStar := by
      simp
    calc
      (((y + a) ⬝ᵥ xStar : ℝ) : EReal) - h ((y + a) - a) =
          (((y + a) ⬝ᵥ xStar : ℝ) : EReal) - h y := by
        simp [sub_eq_add_neg, add_assoc, add_comm]
      _ =
          (((y ⬝ᵥ xStar : ℝ) : EReal) + ((dotProduct a xStar : ℝ) : EReal)) - h y := by
        simp [hdot, EReal.coe_add]
      _ = ((y ⬝ᵥ xStar : ℝ) : EReal) - h y + ((dotProduct a xStar : ℝ) : EReal) := by
        simp [sub_eq_add_neg, add_left_comm, add_comm]

/-- Text 16.0.1: Basic operations on a convex function and their effect on the Fenchel conjugate.

- If `h` is translated by `a`, i.e. `f x = h (x - a)`, then `f* x* = h* x* + ⟪a, x*⟫`.
- If a linear functional is added, i.e. `f x = h x + ⟪x, a*⟫`, then `f* x* = h* (x* - a*)`.
- For a real constant `α`, the conjugate of `h + α` is `h* - α`.

As a special case, for a set `C`, the support function of the translate `C + a` is
`supportFunctionEReal C + ⟪a, ·⟫`, since the support function is the conjugate of the indicator
function. -/
lemma section16_fenchelConjugate_translate {n : ℕ} (h : (Fin n → ℝ) → EReal) (a : Fin n → ℝ) :
    fenchelConjugate n (fun x => h (x - a)) =
      fun xStar => fenchelConjugate n h xStar + ((dotProduct a xStar : ℝ) : EReal) := by
  classical
  funext xStar
  unfold fenchelConjugate
  have hrange :=
    section16_range_fenchelConjugate_translate (h := h) (a := a) (xStar := xStar)
  calc
    sSup (Set.range (fun x => ((x ⬝ᵥ xStar : ℝ) : EReal) - h (x - a))) =
        sSup ((fun z : EReal => z + ((dotProduct a xStar : ℝ) : EReal)) ''
          Set.range (fun y => ((y ⬝ᵥ xStar : ℝ) : EReal) - h y)) := by
      simp [hrange]
    _ =
        sSup (Set.range (fun y => ((y ⬝ᵥ xStar : ℝ) : EReal) - h y)) +
          ((dotProduct a xStar : ℝ) : EReal) := by
      simpa using
        (section13_sSup_image_add_right (c := dotProduct a xStar)
          (s := Set.range (fun y => ((y ⬝ᵥ xStar : ℝ) : EReal) - h y)))

/-- Rewriting the affine piece after adding a linear functional. -/
lemma section16_affine_piece_add_linear {n : ℕ} (h : (Fin n → ℝ) → EReal)
    (aStar : Fin n → ℝ) (x xStar : Fin n → ℝ) :
    ((x ⬝ᵥ xStar : ℝ) : EReal) - (h x + ((dotProduct x aStar : ℝ) : EReal)) =
      ((x ⬝ᵥ (xStar - aStar) : ℝ) : EReal) - h x := by
  have hneg :
      -(h x + ((dotProduct x aStar : ℝ) : EReal)) =
        -h x - ((dotProduct x aStar : ℝ) : EReal) := by
    exact
      (EReal.neg_add (x := h x) (y := ((dotProduct x aStar : ℝ) : EReal))
        (Or.inr (by simp)) (Or.inr (by simp)))
  have hdotE :
      ((x ⬝ᵥ (xStar - aStar) : ℝ) : EReal) =
        ((x ⬝ᵥ xStar : ℝ) : EReal) - ((dotProduct x aStar : ℝ) : EReal) := by
    have hdot :
        ((x ⬝ᵥ (xStar - aStar) : ℝ) : EReal) =
          ((x ⬝ᵥ xStar - x ⬝ᵥ aStar : ℝ) : EReal) := by
      exact congrArg (fun r : ℝ => (r : EReal)) (dotProduct_sub x xStar aStar)
    calc
      ((x ⬝ᵥ (xStar - aStar) : ℝ) : EReal) =
          ((x ⬝ᵥ xStar - x ⬝ᵥ aStar : ℝ) : EReal) := hdot
      _ = ((x ⬝ᵥ xStar : ℝ) : EReal) - ((dotProduct x aStar : ℝ) : EReal) := by
        simp [EReal.coe_sub]
  calc
    ((x ⬝ᵥ xStar : ℝ) : EReal) - (h x + ((dotProduct x aStar : ℝ) : EReal)) =
        ((x ⬝ᵥ xStar : ℝ) : EReal) + -(h x + ((dotProduct x aStar : ℝ) : EReal)) := by
      simp [sub_eq_add_neg]
    _ = ((x ⬝ᵥ xStar : ℝ) : EReal) + (-h x - ((dotProduct x aStar : ℝ) : EReal)) := by
      simp [hneg]
    _ = ((x ⬝ᵥ xStar : ℝ) : EReal) - ((dotProduct x aStar : ℝ) : EReal) - h x := by
      simp [sub_eq_add_neg, add_assoc, add_comm]
    _ = ((x ⬝ᵥ (xStar - aStar) : ℝ) : EReal) - h x := by
      rw [hdotE.symm]

/-- Range rewrite for adding a linear functional inside `fenchelConjugate`. -/
lemma section16_range_fenchelConjugate_add_linear {n : ℕ} (h : (Fin n → ℝ) → EReal)
    (aStar xStar : Fin n → ℝ) :
    Set.range (fun x => ((x ⬝ᵥ xStar : ℝ) : EReal) - (h x + ((dotProduct x aStar : ℝ) : EReal))) =
      Set.range (fun x => ((x ⬝ᵥ (xStar - aStar) : ℝ) : EReal) - h x) := by
  classical
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨x, ?_⟩
    simpa using
      (section16_affine_piece_add_linear (h := h) (aStar := aStar) (x := x) (xStar := xStar)).symm
  · rintro ⟨x, rfl⟩
    refine ⟨x, ?_⟩
    simpa using
      (section16_affine_piece_add_linear (h := h) (aStar := aStar) (x := x) (xStar := xStar))

lemma section16_fenchelConjugate_add_linear {n : ℕ} (h : (Fin n → ℝ) → EReal) (aStar : Fin n → ℝ) :
    fenchelConjugate n (fun x => h x + ((dotProduct x aStar : ℝ) : EReal)) =
      fun xStar => fenchelConjugate n h (xStar - aStar) := by
  classical
  funext xStar
  unfold fenchelConjugate
  have hrange :=
    section16_range_fenchelConjugate_add_linear (h := h) (aStar := aStar) (xStar := xStar)
  simp [hrange]

/-- Rewriting the affine piece after adding a constant. -/
lemma section16_affine_piece_add_const {n : ℕ} (h : (Fin n → ℝ) → EReal) (α : ℝ)
    (x xStar : Fin n → ℝ) :
    ((x ⬝ᵥ xStar : ℝ) : EReal) - (h x + (α : EReal)) =
      (((x ⬝ᵥ xStar : ℝ) : EReal) - h x) + ((-α : ℝ) : EReal) := by
  have hneg :
      -(h x + (α : EReal)) =
        -h x - (α : EReal) := by
    exact
      (EReal.neg_add (x := h x) (y := (α : EReal))
        (Or.inr (by simp)) (Or.inr (by simp)))
  calc
    ((x ⬝ᵥ xStar : ℝ) : EReal) - (h x + (α : EReal)) =
        ((x ⬝ᵥ xStar : ℝ) : EReal) + -(h x + (α : EReal)) := by
      simp [sub_eq_add_neg]
    _ = ((x ⬝ᵥ xStar : ℝ) : EReal) + (-h x - (α : EReal)) := by
      simp [hneg]
    _ = (((x ⬝ᵥ xStar : ℝ) : EReal) - h x) + ((-α : ℝ) : EReal) := by
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Range rewrite for adding a constant inside `fenchelConjugate`. -/
lemma section16_range_fenchelConjugate_add_const {n : ℕ} (h : (Fin n → ℝ) → EReal) (α : ℝ)
    (xStar : Fin n → ℝ) :
    Set.range (fun x => ((x ⬝ᵥ xStar : ℝ) : EReal) - (h x + (α : EReal))) =
      (fun z : EReal => z + ((-α : ℝ) : EReal)) ''
        Set.range (fun x => ((x ⬝ᵥ xStar : ℝ) : EReal) - h x) := by
  classical
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨((x ⬝ᵥ xStar : ℝ) : EReal) - h x, ?_⟩
    refine ⟨⟨x, rfl⟩, ?_⟩
    simpa using
      (section16_affine_piece_add_const (h := h) (α := α) (x := x) (xStar := xStar)).symm
  · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
    refine ⟨x, ?_⟩
    simpa using
      (section16_affine_piece_add_const (h := h) (α := α) (x := x) (xStar := xStar))

lemma section16_fenchelConjugate_add_const {n : ℕ} (h : (Fin n → ℝ) → EReal) (α : ℝ) :
    fenchelConjugate n (fun x => h x + (α : EReal)) =
      fun xStar => fenchelConjugate n h xStar - (α : EReal) := by
  classical
  funext xStar
  unfold fenchelConjugate
  have hrange :=
    section16_range_fenchelConjugate_add_const (h := h) (α := α) (xStar := xStar)
  calc
    sSup (Set.range (fun x => ((x ⬝ᵥ xStar : ℝ) : EReal) - (h x + (α : EReal)))) =
        sSup ((fun z : EReal => z + ((-α : ℝ) : EReal)) ''
          Set.range (fun x => ((x ⬝ᵥ xStar : ℝ) : EReal) - h x)) := by
      simp [hrange]
    _ =
        sSup (Set.range (fun x => ((x ⬝ᵥ xStar : ℝ) : EReal) - h x)) +
          ((-α : ℝ) : EReal) := by
      simpa using
        (section13_sSup_image_add_right (c := -α)
          (s := Set.range (fun x => ((x ⬝ᵥ xStar : ℝ) : EReal) - h x)))
    _ =
        sSup (Set.range (fun x => ((x ⬝ᵥ xStar : ℝ) : EReal) - h x)) -
          (α : EReal) := by
      simp [sub_eq_add_neg]

lemma section16_supportFunctionEReal_translate {n : ℕ} (C : Set (Fin n → ℝ)) (a : Fin n → ℝ) :
    supportFunctionEReal (Set.image (fun x : Fin n → ℝ => x + a) C) =
      fun xStar => supportFunctionEReal C xStar + ((dotProduct a xStar : ℝ) : EReal) := by
  classical
  have hmem :
      ∀ x : Fin n → ℝ,
        x ∈ Set.image (fun y : Fin n → ℝ => y + a) C ↔ x - a ∈ C := by
    intro x
    constructor
    · rintro ⟨y, hyC, rfl⟩
      simpa [add_sub_cancel] using hyC
    · intro hxC
      refine ⟨x - a, hxC, ?_⟩
      simp [sub_add_cancel]
  have hset :
      Set.image (fun x : Fin n → ℝ => x + a) C =
        (fun x : Fin n → ℝ => x + -a) ⁻¹' C := by
    ext x
    constructor
    · intro hx
      have hx' : x - a ∈ C := (hmem x).1 hx
      simpa [sub_eq_add_neg] using hx'
    · intro hx
      have hx' : x - a ∈ C := by
        simpa [sub_eq_add_neg] using hx
      exact (hmem x).2 hx'
  have hindpre :
      indicatorFunction ((fun x : Fin n → ℝ => x + -a) ⁻¹' C) =
        fun x => indicatorFunction C (x - a) := by
    funext x
    simp [indicatorFunction, Set.mem_preimage, sub_eq_add_neg]
  have hconj :
      fenchelConjugate n (indicatorFunction ((fun x : Fin n → ℝ => x + -a) ⁻¹' C)) =
        fun xStar =>
          fenchelConjugate n (indicatorFunction C) xStar + ((dotProduct a xStar : ℝ) : EReal) := by
    simpa [hindpre.symm] using
      (section16_fenchelConjugate_translate (h := indicatorFunction C) (a := a))
  have hEq1 :=
    section13_fenchelConjugate_indicatorFunction_eq_supportFunctionEReal
      (C := (fun x : Fin n → ℝ => x + -a) ⁻¹' C)
  have hEq2 :=
    section13_fenchelConjugate_indicatorFunction_eq_supportFunctionEReal (C := C)
  have hconj' :
      supportFunctionEReal ((fun x : Fin n → ℝ => x + -a) ⁻¹' C) =
        fun xStar => supportFunctionEReal C xStar + ((dotProduct a xStar : ℝ) : EReal) := by
    simpa [hEq1, hEq2] using hconj
  simpa [hset] using hconj'

/-- Text 16.0.2: The polar of a convex set `C` is a `≤ 1` level set of the support function
`δ^*(· | C)`, namely

`C^∘ = {x^* | δ^*(x^* | C) ≤ 1}`. -/
lemma section16_polar_eq_sublevel_deltaStar {n : ℕ} (C : Set (Fin n → ℝ)) :
    {xStar | ∀ x ∈ C, (dotProduct x xStar : ℝ) ≤ 1} =
      {xStar | supportFunctionEReal C xStar ≤ (1 : EReal)} := by
  ext xStar
  constructor
  · intro h
    exact (section13_supportFunctionEReal_le_coe_iff (C := C) (y := xStar) (μ := 1)).2 h
  · intro h
    exact (section13_supportFunctionEReal_le_coe_iff (C := C) (y := xStar) (μ := 1)).1 h

/-- The conjugate of the constant zero function is the indicator of `{0}`. -/
lemma section16_fenchelConjugate_const_zero {n : ℕ} :
    fenchelConjugate n (fun _ : (Fin n → ℝ) => (0 : EReal)) =
      indicatorFunction ({0} : Set (Fin n → ℝ)) := by
  classical
  have hCne : ({0} : Set (Fin n → ℝ)).Nonempty := by simp
  have hCbd :
      ∀ xStar : Fin n → ℝ,
        BddAbove (Set.image (fun x : Fin n → ℝ => dotProduct x xStar) ({0} : Set (Fin n → ℝ))) := by
    intro xStar
    simp
  have hconv : Convex ℝ ({0} : Set (Fin n → ℝ)) := by
    simp
  have hcl :
      clConv n (indicatorFunction ({0} : Set (Fin n → ℝ))) =
        indicatorFunction ({0} : Set (Fin n → ℝ)) := by
    simpa using
      (section13_clConv_indicatorFunction_eq_indicatorFunction_closure
        (C := ({0} : Set (Fin n → ℝ))) hconv hCne)
  have hdelta :
      (fun xStar : Fin n → ℝ =>
          ((deltaStar ({0} : Set (Fin n → ℝ)) xStar : ℝ) : EReal)) =
        fun _ => (0 : EReal) := by
    funext xStar
    simp [deltaStar, supportFunction_eq_sSup_image_dotProduct]
  have hmain :
      fenchelConjugate n
          (fun xStar : Fin n → ℝ =>
            ((deltaStar ({0} : Set (Fin n → ℝ)) xStar : ℝ) : EReal)) =
        clConv n (indicatorFunction ({0} : Set (Fin n → ℝ))) :=
    section13_fenchelConjugate_deltaStar_eq_clConv_indicatorFunction
      (C := ({0} : Set (Fin n → ℝ))) hCne hCbd
  simpa [hdelta, hcl] using hmain

/-- Scaling precomposition inside a Fenchel conjugate. -/
lemma section16_fenchelConjugate_precomp_smul {n : ℕ} (f : (Fin n → ℝ) → EReal) {lam : ℝ}
    (hlam : lam ≠ 0) :
    fenchelConjugate n (fun x => f (lam⁻¹ • x)) =
      fun xStar => fenchelConjugate n f (lam • xStar) := by
  classical
  funext xStar
  unfold fenchelConjugate
  apply congrArg sSup
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨lam⁻¹ • x, ?_⟩
    have hdot : (lam⁻¹ • x) ⬝ᵥ (lam • xStar) = x ⬝ᵥ xStar := by
      rw [smul_dotProduct, dotProduct_smul, smul_smul, inv_mul_cancel₀ hlam, one_smul]
    simp [hdot]
  · rintro ⟨x, rfl⟩
    refine ⟨lam • x, ?_⟩
    have hx : lam⁻¹ • (lam • x) = x := by
      simp [smul_smul, inv_mul_cancel₀ hlam]
    have hdot : (lam • x) ⬝ᵥ xStar = x ⬝ᵥ (lam • xStar) := by
      simp [smul_dotProduct, dotProduct_smul]
    simp [hx, hdot]

/-- The conjugate of the singleton indicator is the constant zero function. -/
lemma section16_fenchelConjugate_indicator_singleton_zero {n : ℕ} :
    fenchelConjugate n (indicatorFunction ({0} : Set (Fin n → ℝ))) = (fun _ => (0 : EReal)) := by
  classical
  have hCne : ({0} : Set (Fin n → ℝ)).Nonempty := by simp
  have hCbd :
      ∀ xStar : Fin n → ℝ,
        BddAbove (Set.image (fun x : Fin n → ℝ => dotProduct x xStar) ({0} : Set (Fin n → ℝ))) := by
    intro xStar
    simp
  have hfun :=
    section13_fenchelConjugate_indicatorFunction_eq_deltaStar_fun
      (C := ({0} : Set (Fin n → ℝ))) hCne hCbd
  funext xStar
  have hdelta : deltaStar ({0} : Set (Fin n → ℝ)) xStar = 0 := by
    simp [deltaStar, supportFunction_eq_sSup_image_dotProduct]
  simpa [hdelta] using congrArg (fun g => g xStar) hfun

/-- Theorem 16.1: For any proper convex function `f`, one has `(λ f)^* = f^* λ` and
`(f λ)^* = λ f^*`, `0 ≤ λ < ∞`.

Here `f^*` is the Fenchel conjugate `fenchelConjugate n f`, `λ f` is pointwise multiplication
`x ↦ (λ : EReal) * f x`, and `f λ` is the right scalar multiple `rightScalarMultiple f λ`. -/
theorem section16_fenchelConjugate_scaling {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) {lam : ℝ} (hlam : 0 ≤ lam) :
    fenchelConjugate n (fun x => ((lam : ℝ) : EReal) * f x) =
        rightScalarMultiple (fenchelConjugate n f) lam ∧
      fenchelConjugate n (rightScalarMultiple f lam) =
        fun xStar => ((lam : ℝ) : EReal) * fenchelConjugate n f xStar := by
  classical
  by_cases hzero : lam = 0
  · subst hzero
    have hzero_mul :
        (fun x => ((0 : ℝ) : EReal) * f x) = fun _ => (0 : EReal) := by
      funext x
      simp
    have hfinite_f : ∃ x, f x ≠ (⊤ : EReal) := by
      rcases properConvexFunctionOn_exists_finite_point (n := n) (f := f) hf with ⟨x0, r0, hx0⟩
      refine ⟨x0, ?_⟩
      simp [hx0]
    have hfinite_fstar : ∃ xStar, fenchelConjugate n f xStar ≠ (⊤ : EReal) := by
      have hfstar :
          ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) :=
        proper_fenchelConjugate_of_proper (n := n) (f := f) hf
      rcases properConvexFunctionOn_exists_finite_point (n := n) (f := fenchelConjugate n f) hfstar with
        ⟨x0, r0, hx0⟩
      refine ⟨x0, ?_⟩
      simp [hx0]
    have hconvStar : ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) := by
      have hconv : ConvexFunction (fenchelConjugate n f) :=
        (fenchelConjugate_closedConvex (n := n) (f := f)).2
      simpa [ConvexFunction] using hconv
    have hconv : ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f := hf.1
    have hleft :
        fenchelConjugate n (fun x => ((0 : ℝ) : EReal) * f x) =
          rightScalarMultiple (fenchelConjugate n f) 0 := by
      have hconst :
          fenchelConjugate n (fun _ : Fin n → ℝ => (0 : EReal)) =
            indicatorFunction ({0} : Set (Fin n → ℝ)) :=
        section16_fenchelConjugate_const_zero (n := n)
      have hright :
          rightScalarMultiple (fenchelConjugate n f) 0 =
            indicatorFunction ({0} : Set (Fin n → ℝ)) :=
        rightScalarMultiple_zero_eq_indicator (f := fenchelConjugate n f) hconvStar hfinite_fstar
      have hconst' :
          fenchelConjugate n (fun x => ((0 : ℝ) : EReal) * f x) =
            indicatorFunction ({0} : Set (Fin n → ℝ)) := by
        simpa [hzero_mul] using hconst
      exact hconst'.trans hright.symm
    have hright0 :
        rightScalarMultiple f 0 = indicatorFunction ({0} : Set (Fin n → ℝ)) :=
      rightScalarMultiple_zero_eq_indicator (f := f) hconv hfinite_f
    have hstar0 :
        fenchelConjugate n (rightScalarMultiple f 0) = fun _ => (0 : EReal) := by
      simpa [hright0] using (section16_fenchelConjugate_indicator_singleton_zero (n := n))
    have hmul0 :
        (fun xStar => ((0 : ℝ) : EReal) * fenchelConjugate n f xStar) = fun _ => (0 : EReal) := by
      funext xStar
      simp
    have hright :
        fenchelConjugate n (rightScalarMultiple f 0) =
          fun xStar => ((0 : ℝ) : EReal) * fenchelConjugate n f xStar := by
      simpa [hmul0] using hstar0
    exact ⟨hleft, hright⟩
  · have hne : lam ≠ 0 := hzero
    have hpos : 0 < lam := lt_of_le_of_ne hlam (Ne.symm hne)
    have hleft :
        fenchelConjugate n (fun x => ((lam : ℝ) : EReal) * f x) =
          rightScalarMultiple (fenchelConjugate n f) lam :=
      section13_fenchelConjugate_smul_eq_rightScalarMultiple (n := n) (f := f) (lam := lam) hpos
    have hconv : ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f := hf.1
    have hconvStar : ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) := by
      have hconv' : ConvexFunction (fenchelConjugate n f) :=
        (fenchelConjugate_closedConvex (n := n) (f := f)).2
      simpa [ConvexFunction] using hconv'
    have hrightScalar :
        rightScalarMultiple f lam = fun x => ((lam : ℝ) : EReal) * f (lam⁻¹ • x) := by
      funext x
      exact rightScalarMultiple_pos (f := f) (lam := lam) hconv hpos x
    have hscale :
        fenchelConjugate n (rightScalarMultiple f lam) =
          rightScalarMultiple (fenchelConjugate n (fun x => f (lam⁻¹ • x))) lam := by
      simpa [hrightScalar] using
        (section13_fenchelConjugate_smul_eq_rightScalarMultiple
          (n := n) (f := fun x => f (lam⁻¹ • x)) (lam := lam) hpos)
    have hprecomp :
        fenchelConjugate n (fun x => f (lam⁻¹ • x)) =
          fun xStar => fenchelConjugate n f (lam • xStar) :=
      section16_fenchelConjugate_precomp_smul (f := f) (lam := lam) hne
    have hscale' :
        fenchelConjugate n (rightScalarMultiple f lam) =
          rightScalarMultiple (fun xStar => fenchelConjugate n f (lam • xStar)) lam := by
      simpa [hprecomp] using hscale
    have hconvPrecomp :
        ConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
          (fun xStar => fenchelConjugate n f (lam • xStar)) := by
      let A : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
        { toFun := fun x => lam • x
          map_add' := by
            intro x y
            simp [smul_add]
          map_smul' := by
            intro t x
            simp [smul_smul, mul_comm] }
      simpa [A] using
        (convexFunctionOn_precomp_linearMap (A := A) (g := fenchelConjugate n f) hconvStar)
    have hright :
        rightScalarMultiple (fun xStar => fenchelConjugate n f (lam • xStar)) lam =
          fun xStar => ((lam : ℝ) : EReal) * fenchelConjugate n f xStar := by
      funext xStar
      have hformula :=
        rightScalarMultiple_pos
          (f := fun xStar => fenchelConjugate n f (lam • xStar)) (lam := lam) hconvPrecomp hpos xStar
      simpa [smul_smul, mul_inv_cancel₀ hne] using hformula
    have hrightFinal :
        fenchelConjugate n (rightScalarMultiple f lam) =
          fun xStar => ((lam : ℝ) : EReal) * fenchelConjugate n f xStar := by
      simpa [hright] using hscale'
    exact ⟨hleft, hrightFinal⟩

/-- Scaling the dot-product image-set commutes with set scaling. -/
lemma section16_image_dotProduct_smul_set {n : ℕ} (C : Set (Fin n → ℝ)) (lam : ℝ)
    (xStar : Fin n → ℝ) :
    Set.image (fun x => dotProduct x xStar) (lam • C) =
      lam • Set.image (fun x => dotProduct x xStar) C := by
  classical
  ext r
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases (Set.mem_smul_set).1 hx with ⟨y, hyC, rfl⟩
    refine (Set.mem_smul_set).2 ?_
    refine ⟨dotProduct y xStar, ⟨y, hyC, rfl⟩, ?_⟩
    simp [smul_dotProduct, smul_eq_mul]
  · rintro hr
    rcases (Set.mem_smul_set).1 hr with ⟨s, hs, rfl⟩
    rcases hs with ⟨y, hyC, rfl⟩
    refine ⟨lam • y, ?_, ?_⟩
    · exact (Set.mem_smul_set).2 ⟨y, hyC, rfl⟩
    · simp [smul_dotProduct, smul_eq_mul]

/-- Corollary 16.1.1. For any non-empty convex set `C`, one has
`δ^*(x^* | λ C) = λ δ^*(x^* | C)`, `0 ≤ λ < ∞`. -/
theorem section16_deltaStar_scaling {n : ℕ} (C : Set (Fin n → ℝ)) {lam : ℝ} (hlam : 0 ≤ lam) :
    deltaStar (lam • C) = fun xStar => lam * deltaStar C xStar := by
  classical
  funext xStar
  calc
    deltaStar (lam • C) xStar =
        sSup (Set.image (fun x : Fin n → ℝ => dotProduct x xStar) (lam • C)) := by
          simp [deltaStar_eq_sSup_image_dotProduct_right]
    _ = sSup (lam • Set.image (fun x : Fin n → ℝ => dotProduct x xStar) C) := by
          simp [section16_image_dotProduct_smul_set]
    _ =
        lam • sSup (Set.image (fun x : Fin n → ℝ => dotProduct x xStar) C) := by
          exact
            (Real.sSup_smul_of_nonneg (a := lam)
              (s := Set.image (fun x : Fin n → ℝ => dotProduct x xStar) C) hlam)
    _ = lam * deltaStar C xStar := by
          simp [smul_eq_mul, deltaStar_eq_sSup_image_dotProduct_right]

/-- Membership in an inverse-scaled set can be rewritten using the original scaling. -/
lemma section16_mem_inv_smul_set_iff {n : ℕ} {lam : ℝ} (hlam0 : lam ≠ 0)
    (S : Set (Fin n → ℝ)) (x : Fin n → ℝ) :
    x ∈ lam⁻¹ • S ↔ lam • x ∈ S := by
  constructor
  · intro hx
    rcases (Set.mem_smul_set).1 hx with ⟨y, hy, rfl⟩
    simpa [smul_smul, mul_inv_cancel₀ hlam0] using hy
  · intro hx
    refine (Set.mem_smul_set).2 ?_
    refine ⟨lam • x, hx, ?_⟩
    simp [smul_smul, inv_mul_cancel₀ hlam0]

/-- The polar inequality for a scaled set is equivalent to a scaled dual variable. -/
lemma section16_polar_smul_iff {n : ℕ} (C : Set (Fin n → ℝ)) {lam : ℝ} (xStar : Fin n → ℝ) :
    (∀ x ∈ (lam • C), (dotProduct x xStar : ℝ) ≤ 1) ↔
      (∀ x ∈ C, (dotProduct x (lam • xStar) : ℝ) ≤ 1) := by
  constructor
  · intro h x hx
    have hx' : lam • x ∈ lam • C := (Set.mem_smul_set).2 ⟨x, hx, rfl⟩
    have h' : (dotProduct (lam • x) xStar : ℝ) ≤ 1 := h (lam • x) hx'
    simpa [smul_dotProduct, dotProduct_smul] using h'
  · intro h x hx
    rcases (Set.mem_smul_set).1 hx with ⟨y, hyC, rfl⟩
    have h' : (dotProduct y (lam • xStar) : ℝ) ≤ 1 := h y hyC
    simpa [smul_dotProduct, dotProduct_smul] using h'

/-- Corollary 16.1.2. For any non-empty convex set `C` one has `(λ C)^∘ = λ^{-1} C^∘` for
`0 < λ < ∞`. -/
theorem section16_polar_scaling {n : ℕ} (C : Set (Fin n → ℝ)) {lam : ℝ} (hlam : 0 < lam) :
    {xStar | ∀ x ∈ (lam • C), (dotProduct x xStar : ℝ) ≤ 1} =
      lam⁻¹ • {xStar | ∀ x ∈ C, (dotProduct x xStar : ℝ) ≤ 1} := by
  classical
  have hne : lam ≠ 0 := ne_of_gt hlam
  ext xStar
  constructor
  · intro hx
    have hx' : ∀ x ∈ C, (dotProduct x (lam • xStar) : ℝ) ≤ 1 :=
      (section16_polar_smul_iff (C := C) (lam := lam) (xStar := xStar)).1 hx
    exact (section16_mem_inv_smul_set_iff (lam := lam) hne _ _).2 hx'
  · intro hx
    have hx' : ∀ x ∈ C, (dotProduct x (lam • xStar) : ℝ) ≤ 1 :=
      (section16_mem_inv_smul_set_iff (lam := lam) hne _ _).1 hx
    exact (section16_polar_smul_iff (C := C) (lam := lam) (xStar := xStar)).2 hx'

/-- The intrinsic interior of a submodule (as a set) is the submodule itself. -/
lemma section16_intrinsicInterior_submodule_eq {n : Nat} (L : Submodule ℝ (Fin n → ℝ)) :
    intrinsicInterior ℝ (L : Set (Fin n → ℝ)) = (L : Set (Fin n → ℝ)) := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let e : E ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)
  let LE : Set E := e ⁻¹' (L : Set (Fin n → ℝ))
  have hLE : e '' LE = (L : Set (Fin n → ℝ)) := by
    simpa [LE] using (Equiv.image_preimage (e := e.toEquiv) (s := (L : Set (Fin n → ℝ))))
  have hriLE : euclideanRelativeInterior n LE = LE := by
    have hri' :
        euclideanRelativeInterior n ((L.comap e.toLinearMap : Submodule ℝ E) : Set E) =
          ((L.comap e.toLinearMap : Submodule ℝ E) : Set E) := by
      simpa using
        (euclideanRelativeInterior_affineSubspace_eq n
          ((L.comap e.toLinearMap).toAffineSubspace))
    simpa [LE] using hri'
  have hpre : intrinsicInterior ℝ LE = LE := by
    calc
      intrinsicInterior ℝ LE = euclideanRelativeInterior n LE := by
        simpa using
          (intrinsicInterior_eq_euclideanRelativeInterior (n := n) (C := LE))
      _ = LE := hriLE
  have himage :
      intrinsicInterior ℝ (e '' LE) = e '' intrinsicInterior ℝ LE :=
    ContinuousLinearEquiv.image_intrinsicInterior (e := e) (s := LE)
  simpa [hLE, hpre] using himage

/-- Nonempty intersection in Euclidean space corresponds to non-disjoint intrinsic interiors. -/
lemma section16_nonempty_preimage_inter_ri_preimage_iff_not_disjoint_intrinsicInterior {n : Nat}
    (L : Submodule ℝ (Fin n → ℝ)) (C : Set (Fin n → ℝ)) :
    Set.Nonempty
        (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹' (L : Set (Fin n → ℝ))) ∩
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹' C)) ↔
      ¬ Disjoint (intrinsicInterior ℝ (L : Set (Fin n → ℝ))) (intrinsicInterior ℝ C) := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let e : E ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)
  have hpreL :
      ((fun x : E => (x : Fin n → ℝ)) ⁻¹' (L : Set (Fin n → ℝ))) = e ⁻¹' (L : Set (Fin n → ℝ)) := by
    ext x
    change x.ofLp ∈ L ↔ (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)) x ∈ L
    simp [PiLp.coe_continuousLinearEquiv]
  have hpreC :
      ((fun x : E => (x : Fin n → ℝ)) ⁻¹' C) = e ⁻¹' C := by
    ext x
    change x.ofLp ∈ C ↔ (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)) x ∈ C
    simp [PiLp.coe_continuousLinearEquiv]
  have hriC :
      euclideanRelativeInterior n (e ⁻¹' C) = intrinsicInterior ℝ (e ⁻¹' C) := by
    simpa using
      (intrinsicInterior_eq_euclideanRelativeInterior (n := n) (C := (e ⁻¹' C))).symm
  have himage_inter :
      e '' (e ⁻¹' (L : Set (Fin n → ℝ)) ∩ intrinsicInterior ℝ (e ⁻¹' C)) =
        (L : Set (Fin n → ℝ)) ∩ intrinsicInterior ℝ C := by
    have hLimage :
        e '' (e ⁻¹' (L : Set (Fin n → ℝ))) = (L : Set (Fin n → ℝ)) := by
      simpa using (Equiv.image_preimage (e := e.toEquiv) (s := (L : Set (Fin n → ℝ))))
    have hCimage :
        e '' intrinsicInterior ℝ (e ⁻¹' C) = intrinsicInterior ℝ C := by
      have h :=
        ContinuousLinearEquiv.image_intrinsicInterior (e := e) (s := e ⁻¹' C)
      have hC : e '' (e ⁻¹' C) = C := by
        simpa using (Equiv.image_preimage (e := e.toEquiv) (s := C))
      have h' :
          intrinsicInterior ℝ C = e '' intrinsicInterior ℝ (e ⁻¹' C) := by
        simpa [hC] using h
      simpa using h'.symm
    have hinter :
        e '' (e ⁻¹' (L : Set (Fin n → ℝ)) ∩ intrinsicInterior ℝ (e ⁻¹' C)) =
          e '' (e ⁻¹' (L : Set (Fin n → ℝ))) ∩ e '' intrinsicInterior ℝ (e ⁻¹' C) :=
      Set.image_inter (f := e) (s := e ⁻¹' (L : Set (Fin n → ℝ)))
        (t := intrinsicInterior ℝ (e ⁻¹' C)) e.injective
    simpa [hLimage, hCimage] using hinter
  have hnonempty_image :
      Set.Nonempty (e ⁻¹' (L : Set (Fin n → ℝ)) ∩ intrinsicInterior ℝ (e ⁻¹' C)) ↔
        Set.Nonempty ((L : Set (Fin n → ℝ)) ∩ intrinsicInterior ℝ C) := by
    constructor
    · intro h
      have h' :
          Set.Nonempty
              (e '' (e ⁻¹' (L : Set (Fin n → ℝ)) ∩ intrinsicInterior ℝ (e ⁻¹' C))) :=
        h.image e
      simpa [himage_inter] using h'
    · intro h
      rcases h with ⟨y, hy⟩
      have hy' :
          y ∈
            e '' (e ⁻¹' (L : Set (Fin n → ℝ)) ∩ intrinsicInterior ℝ (e ⁻¹' C)) := by
        -- Rewrite the goal using the image-intersection identity.
        rw [himage_inter]
        exact hy
      rcases hy' with ⟨x, hx, rfl⟩
      exact ⟨x, hx⟩
  have hnonempty_pre :
      Set.Nonempty
          (((fun x : E => (x : Fin n → ℝ)) ⁻¹' (L : Set (Fin n → ℝ))) ∩
            euclideanRelativeInterior n ((fun x : E => (x : Fin n → ℝ)) ⁻¹' C)) ↔
        Set.Nonempty (e ⁻¹' (L : Set (Fin n → ℝ)) ∩ intrinsicInterior ℝ (e ⁻¹' C)) := by
    simp [hpreL, hpreC, hriC]
  have hnonempty_L :
      Set.Nonempty ((L : Set (Fin n → ℝ)) ∩ intrinsicInterior ℝ C) ↔
        Set.Nonempty
          (intrinsicInterior ℝ (L : Set (Fin n → ℝ)) ∩ intrinsicInterior ℝ C) := by
    simp [section16_intrinsicInterior_submodule_eq (L := L)]
  have hnonempty_disj :
      Set.Nonempty
          (intrinsicInterior ℝ (L : Set (Fin n → ℝ)) ∩ intrinsicInterior ℝ C) ↔
        ¬ Disjoint (intrinsicInterior ℝ (L : Set (Fin n → ℝ))) (intrinsicInterior ℝ C) := by
    constructor
    · rintro ⟨x, hx⟩ hdis
      exact (Set.disjoint_left.mp hdis) hx.1 hx.2
    · intro hnot
      by_contra hne
      apply hnot
      refine Set.disjoint_left.2 ?_
      intro x hxL hxC
      apply hne
      exact ⟨x, ⟨hxL, hxC⟩⟩
  exact hnonempty_pre.trans (hnonempty_image.trans (hnonempty_L.trans hnonempty_disj))
attribute [local instance] Classical.propDecidable

/-- The dot-product image over a submodule has `sInf/sSup` determined by orthogonality. -/
lemma section16_sInf_sSup_image_dotProduct_submodule {n : Nat} (L : Submodule ℝ (Fin n → ℝ))
    (b : Fin n → ℝ) :
    (sInf ((fun x : Fin n → ℝ => ((x ⬝ᵥ b : ℝ) : EReal)) '' (L : Set (Fin n → ℝ))) =
        if b ∈ orthogonalComplement n L then (0 : EReal) else (⊥ : EReal)) ∧
      (sSup ((fun x : Fin n → ℝ => ((x ⬝ᵥ b : ℝ) : EReal)) '' (L : Set (Fin n → ℝ))) =
        if b ∈ orthogonalComplement n L then (0 : EReal) else (⊤ : EReal)) := by
  classical
  by_cases hb : b ∈ orthogonalComplement n L
  · have himage :
        ((fun x : Fin n → ℝ => ((x ⬝ᵥ b : ℝ) : EReal)) '' (L : Set (Fin n → ℝ))) =
          ({0} : Set EReal) := by
      ext z
      constructor
      · rintro ⟨x, hxL, rfl⟩
        have horth : b ⬝ᵥ x = 0 := hb x hxL
        have hx0 : x ⬝ᵥ b = 0 := by simpa [dotProduct_comm] using horth
        simp [hx0]
      · intro hz
        have hxL : (0 : Fin n → ℝ) ∈ L := by simp
        refine ⟨0, hxL, ?_⟩
        simpa using hz.symm
    have hInf : sInf ((fun x : Fin n → ℝ => ((x ⬝ᵥ b : ℝ) : EReal)) '' (L : Set (Fin n → ℝ))) =
        (0 : EReal) := by
      simp [himage]
    have hSup : sSup ((fun x : Fin n → ℝ => ((x ⬝ᵥ b : ℝ) : EReal)) '' (L : Set (Fin n → ℝ))) =
        (0 : EReal) := by
      simp [himage]
    constructor
    · simpa [hb] using hInf
    · simpa [hb] using hSup
  · have hb' : ∃ x ∈ L, x ⬝ᵥ b ≠ 0 := by
      have hb' : ¬ ∀ x, x ∈ L → b ⬝ᵥ x = 0 := by
        simpa [orthogonalComplement] using hb
      rcases not_forall.mp hb' with ⟨x, hx⟩
      rcases (Classical.not_imp).1 hx with ⟨hxL, hneq⟩
      refine ⟨x, hxL, ?_⟩
      simpa [dotProduct_comm] using hneq
    rcases hb' with ⟨x0, hx0L, hdot0⟩
    set d : ℝ := x0 ⬝ᵥ b
    have hd : d ≠ 0 := by simpa [d] using hdot0
    have hSup :
        sSup ((fun x : Fin n → ℝ => ((x ⬝ᵥ b : ℝ) : EReal)) '' (L : Set (Fin n → ℝ))) =
          (⊤ : EReal) := by
      refine (sSup_eq_top).2 ?_
      intro c hc
      cases c using EReal.rec with
      | top =>
          exact (lt_irrefl (⊤ : EReal) hc).elim
      | bot =>
          refine ⟨((d : ℝ) : EReal), ?_, ?_⟩
          · refine ⟨x0, hx0L, ?_⟩
            simp [d]
          · exact EReal.bot_lt_coe d
      | coe r =>
          have hsign : 0 < d ∨ d < 0 :=
            lt_or_gt_of_ne (by simpa [eq_comm] using hd)
          cases hsign with
          | inl hpos =>
              let t : ℝ := r / d + 1
              have hlt : r < t * d := by
                have h1 : r / d < r / d + 1 := by linarith
                have h2 := mul_lt_mul_of_pos_right h1 hpos
                have hleft : (r / d) * d = r := by
                  field_simp [hpos.ne']
                have h2' : r < (r / d + 1) * d := by
                  simpa [hleft, t] using h2
                simpa [t] using h2'
              refine ⟨((t * d : ℝ) : EReal), ?_, ?_⟩
              · refine ⟨t • x0, L.smul_mem t hx0L, ?_⟩
                simp [d, t, smul_dotProduct]
              · exact (EReal.coe_lt_coe hlt)
          | inr hneg =>
              let t : ℝ := r / d - 1
              have hlt : r < t * d := by
                have h1 : r / d - 1 < r / d := by linarith
                have h2 := mul_lt_mul_of_neg_right h1 hneg
                have hleft : (r / d) * d = r := by
                  field_simp [hneg.ne']
                have h2' : r < (r / d - 1) * d := by
                  simpa [hleft, t] using h2
                simpa [t] using h2'
              refine ⟨((t * d : ℝ) : EReal), ?_, ?_⟩
              · refine ⟨t • x0, L.smul_mem t hx0L, ?_⟩
                simp [d, t, smul_dotProduct]
              · exact (EReal.coe_lt_coe hlt)
    have hInf :
        sInf ((fun x : Fin n → ℝ => ((x ⬝ᵥ b : ℝ) : EReal)) '' (L : Set (Fin n → ℝ))) =
          (⊥ : EReal) := by
      refine (sInf_eq_bot).2 ?_
      intro c hc
      cases c using EReal.rec with
      | bot =>
          exact (lt_irrefl (⊥ : EReal) hc).elim
      | top =>
          refine ⟨((d : ℝ) : EReal), ?_, ?_⟩
          · refine ⟨x0, hx0L, ?_⟩
            simp [d]
          · exact EReal.coe_lt_top d
      | coe r =>
          have hsign : 0 < d ∨ d < 0 :=
            lt_or_gt_of_ne (by simpa [eq_comm] using hd)
          cases hsign with
          | inl hpos =>
              let t : ℝ := r / d - 1
              have hlt : t * d < r := by
                have h1 : r / d - 1 < r / d := by linarith
                have h2 := mul_lt_mul_of_pos_right h1 hpos
                have hright : (r / d) * d = r := by
                  field_simp [hpos.ne']
                have h2' : (r / d - 1) * d < r := by
                  simpa [hright, t] using h2
                simpa [t] using h2'
              refine ⟨((t * d : ℝ) : EReal), ?_, ?_⟩
              · refine ⟨t • x0, L.smul_mem t hx0L, ?_⟩
                simp [d, t, smul_dotProduct]
              · exact (EReal.coe_lt_coe hlt)
          | inr hneg =>
              let t : ℝ := r / d + 1
              have hlt : t * d < r := by
                have h1 : r / d < r / d + 1 := by linarith
                have h2 := mul_lt_mul_of_neg_right h1 hneg
                have hright : (r / d) * d = r := by
                  field_simp [hneg.ne']
                have h2' : (r / d + 1) * d < r := by
                  simpa [hright, t] using h2
                simpa [t] using h2'
              refine ⟨((t * d : ℝ) : EReal), ?_, ?_⟩
              · refine ⟨t • x0, L.smul_mem t hx0L, ?_⟩
                simp [d, t, smul_dotProduct]
              · exact (EReal.coe_lt_coe hlt)
    constructor
    · simpa [hb] using hInf
    · simpa [hb] using hSup

/-- Negating the dual variable swaps the sign of the dot-product infimum condition. -/
lemma section16_sInf_lt_zero_iff_sSup_neg_gt_zero {n : Nat} (C : Set (Fin n → ℝ))
    (b : Fin n → ℝ) :
    (0 : EReal) > sInf ((fun x : Fin n → ℝ => ((x ⬝ᵥ b : ℝ) : EReal)) '' C) ↔
      sSup ((fun x : Fin n → ℝ => ((x ⬝ᵥ (-b) : ℝ) : EReal)) '' C) > (0 : EReal) := by
  classical
  set S : Set EReal := (fun x : Fin n → ℝ => ((x ⬝ᵥ b : ℝ) : EReal)) '' C
  set Sneg : Set EReal := (fun x : Fin n → ℝ => ((x ⬝ᵥ (-b) : ℝ) : EReal)) '' C
  constructor
  · intro h
    have h' : sInf S < (0 : EReal) := h
    rcases (sInf_lt_iff).1 h' with ⟨a, haS, ha⟩
    rcases haS with ⟨x, hx, rfl⟩
    have hxneg : x ⬝ᵥ b < (0 : ℝ) := by
      have hcoe : ((x ⬝ᵥ b : ℝ) : EReal) < ((0 : ℝ) : EReal) := by
        simpa using ha
      exact (EReal.coe_lt_coe_iff).1 hcoe
    have hxpos : (0 : ℝ) < x ⬝ᵥ (-b) := by
      have : (0 : ℝ) < -(x ⬝ᵥ b) := by linarith
      simpa [dotProduct_neg] using this
    have hxposE : (0 : EReal) < ((x ⬝ᵥ (-b) : ℝ) : EReal) :=
      EReal.coe_lt_coe hxpos
    have : (0 : EReal) < sSup Sneg := by
      exact (lt_sSup_iff).2 ⟨((x ⬝ᵥ (-b) : ℝ) : EReal), ⟨x, hx, rfl⟩, hxposE⟩
    exact this
  · intro h
    have h' : (0 : EReal) < sSup Sneg := h
    rcases (lt_sSup_iff).1 h' with ⟨a, haS, ha⟩
    rcases haS with ⟨x, hx, rfl⟩
    have hxpos : (0 : ℝ) < x ⬝ᵥ (-b) := by
      have hcoe : ((0 : ℝ) : EReal) < ((x ⬝ᵥ (-b) : ℝ) : EReal) := by
        simpa using ha
      exact (EReal.coe_lt_coe_iff).1 hcoe
    have hxneg : x ⬝ᵥ b < (0 : ℝ) := by
      have : (0 : ℝ) < -(x ⬝ᵥ b) := by simpa [dotProduct_neg] using hxpos
      linarith
    have hxnegE : ((x ⬝ᵥ b : ℝ) : EReal) < (0 : EReal) :=
      EReal.coe_lt_coe hxneg
    have : sInf S < (0 : EReal) := by
      exact (sInf_lt_iff).2 ⟨((x ⬝ᵥ b : ℝ) : EReal), ⟨x, hx, rfl⟩, hxnegE⟩
    exact this

/-- Proper separation of a submodule and an effective domain in terms of recession inequalities. -/
lemma section16_exists_hyperplaneSeparatesProperly_submodule_effectiveDomain_iff_exists_orthogonal_recession_ineq
    {n : Nat} (L : Submodule ℝ (Fin n → ℝ)) (f : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    (∃ H, HyperplaneSeparatesProperly n H (L : Set (Fin n → ℝ))
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)) ↔
      ∃ xStar : Fin n → ℝ,
        xStar ∈ orthogonalComplement n L ∧
          recessionFunction (fenchelConjugate n f) xStar ≤ (0 : EReal) ∧
            recessionFunction (fenchelConjugate n f) (-xStar) > (0 : EReal) := by
  classical
  set domf : Set (Fin n → ℝ) := effectiveDomain (Set.univ : Set (Fin n → ℝ)) f
  have hLne : (L : Set (Fin n → ℝ)).Nonempty := by
    refine ⟨0, by simp⟩
  have hdomne : domf.Nonempty :=
    section13_effectiveDomain_nonempty_of_proper (n := n) (f := f) hf
  have hsep_iff :
      (∃ H, HyperplaneSeparatesProperly n H (L : Set (Fin n → ℝ)) domf) ↔
        ∃ b : Fin n → ℝ,
          sInf ((fun x : Fin n → ℝ => ((x ⬝ᵥ b : ℝ) : EReal)) '' (L : Set (Fin n → ℝ))) ≥
              sSup ((fun x : Fin n → ℝ => ((x ⬝ᵥ b : ℝ) : EReal)) '' domf) ∧
            sSup ((fun x : Fin n → ℝ => ((x ⬝ᵥ b : ℝ) : EReal)) '' (L : Set (Fin n → ℝ))) >
              sInf ((fun x : Fin n → ℝ => ((x ⬝ᵥ b : ℝ) : EReal)) '' domf) := by
    simpa [domf] using
      (exists_hyperplaneSeparatesProperly_iff (n := n) (C₁ := (L : Set (Fin n → ℝ)))
        (C₂ := domf) hLne hdomne)
  have hsupp :
      supportFunctionEReal domf = recessionFunction (fenchelConjugate n f) := by
    simpa [domf] using
      (supportFunctionEReal_effectiveDomain_eq_recession_fenchelConjugate (n := n) (f := f)
        (hf := hf) (fStar0_plus := recessionFunction (fenchelConjugate n f))
        (hfStar0_plus := by intro y; rfl))
  have hsSup_dom (b : Fin n → ℝ) :
      sSup ((fun x : Fin n → ℝ => ((x ⬝ᵥ b : ℝ) : EReal)) '' domf) =
        supportFunctionEReal domf b := by
    classical
    have hset :
        ((fun x : Fin n → ℝ => ((x ⬝ᵥ b : ℝ) : EReal)) '' domf) =
          {z : EReal | ∃ x ∈ domf, z = ((dotProduct x b : ℝ) : EReal)} := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩
    simp [supportFunctionEReal, hset]
  have hSup_dom_neg (b : Fin n → ℝ) :
      sSup ((fun x : Fin n → ℝ => ((x ⬝ᵥ (-b) : ℝ) : EReal)) '' domf) =
        supportFunctionEReal domf (-b) := by
    simpa using hsSup_dom (-b)
  constructor
  · intro hsep
    rcases (hsep_iff).1 hsep with ⟨b, hInfSup, hSupInf⟩
    have hL := section16_sInf_sSup_image_dotProduct_submodule (L := L) (b := b)
    rcases hL with ⟨hInfL, hSupL⟩
    have hb : b ∈ orthogonalComplement n L := by
      by_contra hb
      have hInfL' :
          sInf ((fun x : Fin n → ℝ => ((x ⬝ᵥ b : ℝ) : EReal)) '' (L : Set (Fin n → ℝ))) =
            (⊥ : EReal) := by
        simpa [hb] using hInfL
      have hSup_dom_pos : (⊥ : EReal) < sSup ((fun x : Fin n → ℝ => ((x ⬝ᵥ b : ℝ) : EReal)) '' domf) := by
        rcases hdomne with ⟨x, hx⟩
        have hxmem :
            ((x ⬝ᵥ b : ℝ) : EReal) ∈
              ((fun x : Fin n → ℝ => ((x ⬝ᵥ b : ℝ) : EReal)) '' domf) :=
          ⟨x, hx, rfl⟩
        have hle : ((x ⬝ᵥ b : ℝ) : EReal) ≤
            sSup ((fun x : Fin n → ℝ => ((x ⬝ᵥ b : ℝ) : EReal)) '' domf) := le_sSup hxmem
        exact lt_of_lt_of_le (EReal.bot_lt_coe (x ⬝ᵥ b)) hle
      have hInfSup' :
          (⊥ : EReal) ≥ sSup ((fun x : Fin n → ℝ => ((x ⬝ᵥ b : ℝ) : EReal)) '' domf) := by
        simpa [hInfL'] using hInfSup
      exact (not_le_of_gt hSup_dom_pos) hInfSup'
    have hInfL' :
        sInf ((fun x : Fin n → ℝ => ((x ⬝ᵥ b : ℝ) : EReal)) '' (L : Set (Fin n → ℝ))) =
          (0 : EReal) := by
      simpa [hb] using hInfL
    have hSupL' :
        sSup ((fun x : Fin n → ℝ => ((x ⬝ᵥ b : ℝ) : EReal)) '' (L : Set (Fin n → ℝ))) =
          (0 : EReal) := by
      simpa [hb] using hSupL
    have hSup_dom_le :
        sSup ((fun x : Fin n → ℝ => ((x ⬝ᵥ b : ℝ) : EReal)) '' domf) ≤ (0 : EReal) := by
      have hInfSup' : (0 : EReal) ≥
          sSup ((fun x : Fin n → ℝ => ((x ⬝ᵥ b : ℝ) : EReal)) '' domf) := by
        simpa [hInfL'] using hInfSup
      exact hInfSup'
    have hInf_dom_lt :
        (0 : EReal) >
          sInf ((fun x : Fin n → ℝ => ((x ⬝ᵥ b : ℝ) : EReal)) '' domf) := by
      simpa [hSupL'] using hSupInf
    have hSup_dom_neg_pos :
        sSup ((fun x : Fin n → ℝ => ((x ⬝ᵥ (-b) : ℝ) : EReal)) '' domf) > (0 : EReal) :=
      (section16_sInf_lt_zero_iff_sSup_neg_gt_zero (C := domf) (b := b)).1 hInf_dom_lt
    refine ⟨b, hb, ?_, ?_⟩
    · have hle :
        supportFunctionEReal domf b ≤ (0 : EReal) := by
          simpa [hsSup_dom b] using hSup_dom_le
      simpa [hsupp] using hle
    · have hpos :
        supportFunctionEReal domf (-b) > (0 : EReal) := by
          rw [← hSup_dom_neg b]
          exact hSup_dom_neg_pos
      simpa [hsupp] using hpos
  · rintro ⟨xStar, hxorth, hle, hpos⟩
    have hL := section16_sInf_sSup_image_dotProduct_submodule (L := L) (b := xStar)
    rcases hL with ⟨hInfL, hSupL⟩
    have hInfL' :
        sInf ((fun x : Fin n → ℝ => ((x ⬝ᵥ xStar : ℝ) : EReal)) '' (L : Set (Fin n → ℝ))) =
          (0 : EReal) := by
      simpa [hxorth] using hInfL
    have hSupL' :
        sSup ((fun x : Fin n → ℝ => ((x ⬝ᵥ xStar : ℝ) : EReal)) '' (L : Set (Fin n → ℝ))) =
          (0 : EReal) := by
      simpa [hxorth] using hSupL
    have hSup_dom_le :
        sSup ((fun x : Fin n → ℝ => ((x ⬝ᵥ xStar : ℝ) : EReal)) '' domf) ≤ (0 : EReal) := by
      have hle' :
          supportFunctionEReal domf xStar ≤ (0 : EReal) := by
        simpa [hsupp] using hle
      simpa [hsSup_dom xStar] using hle'
    have hSup_dom_neg_pos :
        sSup ((fun x : Fin n → ℝ => ((x ⬝ᵥ (-xStar) : ℝ) : EReal)) '' domf) > (0 : EReal) := by
      have hpos' :
          supportFunctionEReal domf (-xStar) > (0 : EReal) := by
        simpa [hsupp] using hpos
      rw [hSup_dom_neg xStar]
      exact hpos'
    have hInf_dom_lt :
        (0 : EReal) >
          sInf ((fun x : Fin n → ℝ => ((x ⬝ᵥ xStar : ℝ) : EReal)) '' domf) :=
      (section16_sInf_lt_zero_iff_sSup_neg_gt_zero (C := domf) (b := xStar)).2 hSup_dom_neg_pos
    have hInfSup :
        sInf ((fun x : Fin n → ℝ => ((x ⬝ᵥ xStar : ℝ) : EReal)) '' (L : Set (Fin n → ℝ))) ≥
          sSup ((fun x : Fin n → ℝ => ((x ⬝ᵥ xStar : ℝ) : EReal)) '' domf) := by
      simpa [hInfL'] using hSup_dom_le
    have hSupInf :
        sSup ((fun x : Fin n → ℝ => ((x ⬝ᵥ xStar : ℝ) : EReal)) '' (L : Set (Fin n → ℝ))) >
          sInf ((fun x : Fin n → ℝ => ((x ⬝ᵥ xStar : ℝ) : EReal)) '' domf) := by
      simpa [hSupL'] using hInf_dom_lt
    exact (hsep_iff).2 ⟨xStar, hInfSup, hSupInf⟩

/-- Lemma 16.2. Let `L` be a subspace of `ℝ^n` and let `f` be a proper convex function.
Then `L` meets `ri (dom f)` if and only if there exists no vector `xStar ∈ L^⊥` such that
`(f^*0^+)(xStar) ≤ 0` and `(f^*0^+)(-xStar) > 0`.

Here `dom f` is the effective domain `effectiveDomain univ f`, `ri` is `euclideanRelativeInterior`,
and `(f^*0^+)` is represented as `recessionFunction (fenchelConjugate n f)`. -/
lemma section16_subspace_meets_ri_effectiveDomain_iff_not_exists_orthogonal_recession_ineq
    {n : Nat} (L : Submodule ℝ (Fin n → ℝ)) (f : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    Set.Nonempty
        ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹' (L : Set (Fin n → ℝ)) ∩
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)) ↔
      ¬ ∃ xStar : Fin n → ℝ,
          xStar ∈ orthogonalComplement n L ∧
            recessionFunction (fenchelConjugate n f) xStar ≤ (0 : EReal) ∧
              recessionFunction (fenchelConjugate n f) (-xStar) > (0 : EReal) := by
  classical
  set domf : Set (Fin n → ℝ) := effectiveDomain (Set.univ : Set (Fin n → ℝ)) f
  have hLne : (L : Set (Fin n → ℝ)).Nonempty := by
    refine ⟨0, by simp⟩
  have hdomne : domf.Nonempty :=
    section13_effectiveDomain_nonempty_of_proper (n := n) (f := f) hf
  have hLconv : Convex ℝ (L : Set (Fin n → ℝ)) := L.convex
  have hdomconv : Convex ℝ domf :=
    effectiveDomain_convex (S := (Set.univ : Set (Fin n → ℝ))) (f := f) hf.1
  have hnonempty_iff :
      Set.Nonempty
          (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹' (L : Set (Fin n → ℝ))) ∩
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹' domf)) ↔
        ¬ Disjoint (intrinsicInterior ℝ (L : Set (Fin n → ℝ))) (intrinsicInterior ℝ domf) := by
    simpa [domf] using
      (section16_nonempty_preimage_inter_ri_preimage_iff_not_disjoint_intrinsicInterior
        (L := L) (C := domf))
  have hsep_iff :
      (∃ H, HyperplaneSeparatesProperly n H (L : Set (Fin n → ℝ)) domf) ↔
        Disjoint (intrinsicInterior ℝ (L : Set (Fin n → ℝ))) (intrinsicInterior ℝ domf) := by
    simpa [domf] using
      (exists_hyperplaneSeparatesProperly_iff_disjoint_intrinsicInterior (n := n)
        (C₁ := (L : Set (Fin n → ℝ))) (C₂ := domf) hLne hdomne hLconv hdomconv)
  have hsep_iff' :
      ¬ Disjoint (intrinsicInterior ℝ (L : Set (Fin n → ℝ))) (intrinsicInterior ℝ domf) ↔
        ¬ ∃ H, HyperplaneSeparatesProperly n H (L : Set (Fin n → ℝ)) domf := by
    exact (not_congr hsep_iff).symm
  have horth_iff :
      (∃ H, HyperplaneSeparatesProperly n H (L : Set (Fin n → ℝ)) domf) ↔
        ∃ xStar : Fin n → ℝ,
          xStar ∈ orthogonalComplement n L ∧
            recessionFunction (fenchelConjugate n f) xStar ≤ (0 : EReal) ∧
              recessionFunction (fenchelConjugate n f) (-xStar) > (0 : EReal) := by
    simpa [domf] using
      (section16_exists_hyperplaneSeparatesProperly_submodule_effectiveDomain_iff_exists_orthogonal_recession_ineq
        (L := L) (f := f) hf)
  calc
    Set.Nonempty
        (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹' (L : Set (Fin n → ℝ))) ∩
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹' domf)) ↔
        ¬ Disjoint (intrinsicInterior ℝ (L : Set (Fin n → ℝ))) (intrinsicInterior ℝ domf) := hnonempty_iff
    _ ↔ ¬ ∃ H, HyperplaneSeparatesProperly n H (L : Set (Fin n → ℝ)) domf := hsep_iff'
    _ ↔
        ¬ ∃ xStar : Fin n → ℝ,
          xStar ∈ orthogonalComplement n L ∧
            recessionFunction (fenchelConjugate n f) xStar ≤ (0 : EReal) ∧
              recessionFunction (fenchelConjugate n f) (-xStar) > (0 : EReal) := by
      simpa using (not_congr horth_iff)

/-- Coordinate form of a Euclidean linear map, viewed as a map into `Fin m → ℝ`. -/
noncomputable def section16_coordLinearMap {n m : Nat}
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] (Fin m → ℝ) :=
  (EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ)).toLinearMap ∘ₗ A

/-- Convert the range-preimage intersection into an explicit witness. -/
lemma section16_nonempty_preimage_range_inter_ri_effectiveDomain_iff {n m : Nat}
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) (g : (Fin m → ℝ) → EReal) :
    Set.Nonempty
        (((fun z : EuclideanSpace ℝ (Fin m) => (z : Fin m → ℝ)) ⁻¹'
              (LinearMap.range (section16_coordLinearMap A) : Set (Fin m → ℝ))) ∩
          euclideanRelativeInterior m
            ((fun z : EuclideanSpace ℝ (Fin m) => (z : Fin m → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin m → ℝ)) g)) ↔
      ∃ x : EuclideanSpace ℝ (Fin n),
        A x ∈
          euclideanRelativeInterior m
            ((fun z : EuclideanSpace ℝ (Fin m) => (z : Fin m → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin m → ℝ)) g) := by
  constructor
  · rintro ⟨z, hz⟩
    have hzA :
        (z : Fin m → ℝ) ∈ (LinearMap.range (section16_coordLinearMap A) : Set (Fin m → ℝ)) :=
      (Set.mem_preimage).1 hz.1
    rcases (LinearMap.mem_range).1 hzA with ⟨x, hx⟩
    have hx' : A x = z := by
      have hx' := congrArg (WithLp.toLp 2) hx
      simpa [section16_coordLinearMap] using hx'
    refine ⟨x, ?_⟩
    simpa [hx'] using hz.2
  · rintro ⟨x, hx⟩
    refine ⟨A x, ?_⟩
    constructor
    · refine (Set.mem_preimage).2 ?_
      exact (LinearMap.mem_range).2 ⟨x, rfl⟩
    · exact hx

/-- Characterize the orthogonal complement of a range via the adjoint. -/
lemma section16_mem_orthogonalComplement_range_iff_adjoint_eq_zero {n m : Nat}
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (yStar : EuclideanSpace ℝ (Fin m)) :
    (yStar : Fin m → ℝ) ∈
        orthogonalComplement m (LinearMap.range (section16_coordLinearMap A)) ↔
      ((LinearMap.adjoint :
              (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ≃ₗ⋆[ℝ]
                (EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))
            A)
          yStar = 0 := by
  classical
  let Aadj :
      EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    ((LinearMap.adjoint :
            (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ≃ₗ⋆[ℝ]
              (EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))
          A)
  constructor
  · intro hy
    change Aadj yStar = 0
    apply (ext_inner_left ℝ)
    intro x
    have hx :
        (section16_coordLinearMap A x : Fin m → ℝ) ∈
          LinearMap.range (section16_coordLinearMap A) := ⟨x, rfl⟩
    have hdot :
        (yStar : Fin m → ℝ) ⬝ᵥ (section16_coordLinearMap A x : Fin m → ℝ) = 0 := hy _ hx
    calc
      inner ℝ x (Aadj yStar) = inner ℝ (A x) yStar := by
        simpa [Aadj] using
          (LinearMap.adjoint_inner_right (A := A) (x := x) (y := yStar))
      _ = ((yStar : Fin m → ℝ) ⬝ᵥ (A x : Fin m → ℝ) : ℝ) := by
        simp [EuclideanSpace.inner_eq_star_dotProduct]
      _ = 0 := by simpa [section16_coordLinearMap] using hdot
      _ = inner ℝ x 0 := by simp
  · intro hAadj
    have hAadj' : Aadj yStar = 0 := by simpa [Aadj] using hAadj
    intro y hy
    rcases hy with ⟨x, rfl⟩
    have hinner :
        inner ℝ (A x) yStar = inner ℝ x (Aadj yStar) := by
      simpa [Aadj] using
        (LinearMap.adjoint_inner_right (A := A) (x := x) (y := yStar)).symm
    have hzero : inner ℝ (A x) yStar = 0 := by
      calc
        inner ℝ (A x) yStar = inner ℝ x (Aadj yStar) := hinner
        _ = inner ℝ x 0 := by simp [hAadj']
        _ = 0 := by simp
    simpa [EuclideanSpace.inner_eq_star_dotProduct, section16_coordLinearMap] using hzero

/-- Rewrite orthogonality over the range in an existential statement. -/
lemma section16_exists_orthogonalComplement_range_recession_iff_exists_adjoint_eq_zero_recession
    {n m : Nat} (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (g : (Fin m → ℝ) → EReal) :
    (∃ xStar : Fin m → ℝ,
        xStar ∈ orthogonalComplement m (LinearMap.range (section16_coordLinearMap A)) ∧
          recessionFunction (fenchelConjugate m g) xStar ≤ (0 : EReal) ∧
            recessionFunction (fenchelConjugate m g) (-xStar) > (0 : EReal)) ↔
      ∃ yStar : EuclideanSpace ℝ (Fin m),
        ((LinearMap.adjoint :
                (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ≃ₗ⋆[ℝ]
                  (EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))
              A)
            yStar = 0 ∧
          recessionFunction (fenchelConjugate m g) (yStar : Fin m → ℝ) ≤ (0 : EReal) ∧
            recessionFunction (fenchelConjugate m g) (-yStar : Fin m → ℝ) > (0 : EReal) := by
  constructor
  · rintro ⟨xStar, hxorth, hle, hgt⟩
    refine ⟨WithLp.toLp 2 xStar, ?_⟩
    have hAdj :
        ((LinearMap.adjoint :
                (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ≃ₗ⋆[ℝ]
                  (EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))
              A)
            (WithLp.toLp 2 xStar) = 0 := by
      refine
        (section16_mem_orthogonalComplement_range_iff_adjoint_eq_zero
              (A := A) (yStar := WithLp.toLp 2 xStar)).1 ?_
      exact hxorth
    refine ⟨hAdj, ?_, ?_⟩
    · simpa using hle
    · simpa using hgt
  · rintro ⟨yStar, hAdj, hle, hgt⟩
    refine ⟨(yStar : Fin m → ℝ), ?_⟩
    have hxorth :
        (yStar : Fin m → ℝ) ∈
          orthogonalComplement m (LinearMap.range (section16_coordLinearMap A)) :=
      (section16_mem_orthogonalComplement_range_iff_adjoint_eq_zero (A := A) (yStar := yStar)).2
        hAdj
    exact ⟨hxorth, hle, hgt⟩

end Section16
end Chap03
