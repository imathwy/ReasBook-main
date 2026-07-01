/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yijie Wang, Yunxi Duan, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part17
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part6
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section04_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section05_part8
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section12_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section14_part10
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section07_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section07_part3
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section07_part6

section Chap03
section Section15

open scoped BigOperators
open scoped Pointwise
open scoped Topology


/-- Fenchel–Young inequality from the conjugate definition, using `f 0 = 0`. -/
lemma dotProduct_le_add_fenchelConjugate {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf0 : f 0 = 0) :
    ∀ x y : Fin n → ℝ,
      ((x ⬝ᵥ y : ℝ) : EReal) ≤ f x + fenchelConjugate n f y := by
  intro x y
  have hsub : ((x ⬝ᵥ y : ℝ) : EReal) - f x ≤ fenchelConjugate n f y := by
    unfold fenchelConjugate
    exact le_sSup ⟨x, rfl⟩
  have hxbot : f x ≠ (⊥ : EReal) := by
    intro hbot
    have h0le : (0 : EReal) ≤ (⊥ : EReal) := by simpa [hbot] using (hf_nonneg x)
    have hbotlt : (⊥ : EReal) < (0 : EReal) := by
      simp
    exact (not_le_of_gt hbotlt) h0le
  have hstar_ne_bot : fenchelConjugate n f y ≠ (⊥ : EReal) := by
    intro hbot
    have hmem :
        (0 : EReal) ∈ Set.range (fun x : Fin n → ℝ => ((x ⬝ᵥ y : ℝ) : EReal) - f x) := by
      refine ⟨0, ?_⟩
      simp [hf0]
    have hle : (0 : EReal) ≤ fenchelConjugate n f y := by
      unfold fenchelConjugate
      exact le_sSup hmem
    have h0le : (0 : EReal) ≤ (⊥ : EReal) := by
      simp [hbot] at hle
    have hbotlt : (⊥ : EReal) < (0 : EReal) := by
      simp
    exact (not_le_of_gt hbotlt) h0le
  have h1 : f x ≠ (⊥ : EReal) ∨ fenchelConjugate n f y ≠ ⊤ := Or.inl hxbot
  have h2 : f x ≠ ⊤ ∨ fenchelConjugate n f y ≠ (⊥ : EReal) := Or.inr hstar_ne_bot
  have hle : ((x ⬝ᵥ y : ℝ) : EReal) ≤ fenchelConjugate n f y + f x :=
    (EReal.sub_le_iff_le_add h1 h2).1 hsub
  simpa [add_comm, add_left_comm, add_assoc] using hle

/-- Nonnegativity and `f 0 = 0` give properness on `univ` for a closed convex function. -/
lemma properConvexFunctionOn_of_nonneg_closedConvex_zero {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_closed : ClosedConvexFunction f) (hf0 : f 0 = 0) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f := by
  have hconv : ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f := by
    simpa [ConvexFunction] using hf_closed.1
  have hne : Set.Nonempty (epigraph (S := (Set.univ : Set (Fin n → ℝ))) f) := by
    refine ⟨(0, 0), ?_⟩
    have : f (0 : Fin n → ℝ) ≤ (0 : EReal) := by simp [hf0]
    simpa [mem_epigraph_univ_iff] using this
  have hbot : ∀ x ∈ (Set.univ : Set (Fin n → ℝ)), f x ≠ (⊥ : EReal) := by
    intro x hx
    intro hbot
    have h0le : (0 : EReal) ≤ (⊥ : EReal) := by simpa [hbot] using (hf_nonneg x)
    have hbotlt : (⊥ : EReal) < (0 : EReal) := by
      simp
    exact (not_le_of_gt hbotlt) h0le
  exact ⟨hconv, hne, hbot⟩

/-- Biconjugation reduces to the original function under closedness and nonnegativity. -/
lemma fenchelConjugate_biconjugate_eq_of_nonneg_closedConvex_zero {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (hf_nonneg : ∀ x, 0 ≤ f x) (hf_closed : ClosedConvexFunction f)
    (hf0 : f 0 = 0) :
    fenchelConjugate n (fenchelConjugate n f) = f := by
  have hproper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f :=
    properConvexFunctionOn_of_nonneg_closedConvex_zero (f := f) hf_nonneg hf_closed hf0
  have hcl : clConv n f = f := by
    exact clConv_eq_of_closedProperConvex (n := n) (f := f) hf_closed.2 hproper
  have hbiconj : fenchelConjugate n (fenchelConjugate n f) = clConv n f :=
    fenchelConjugate_biconjugate_eq_clConv (n := n) (f := f)
  simpa [hcl] using hbiconj

/-- Nonnegativity and `f 0 = 0` make the Fenchel conjugate nonnegative. -/
lemma fenchelConjugate_nonneg_of_nonneg_zero {n : ℕ} (f : (Fin n → ℝ) → EReal) (hf0 : f 0 = 0) :
    ∀ y : Fin n → ℝ, (0 : EReal) ≤ fenchelConjugate n f y := by
  intro y
  unfold fenchelConjugate
  have hmem :
      (0 : EReal) ∈
        Set.range (fun x : Fin n → ℝ => ((x ⬝ᵥ y : ℝ) : EReal) - f x) := by
    refine ⟨0, ?_⟩
    simp [hf0]
  exact le_sSup hmem

/-- Dilation feasibility yields the polar inequality for a positive scale. -/
lemma dilation_le_one_pos_imp_polar_feasible {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf0 : f 0 = 0) {x : Fin n → ℝ} {t : ℝ} (ht : 0 < t)
    (hle : (t : EReal) * f ((t⁻¹) • x) ≤ (1 : EReal)) :
    ∀ y, ((y ⬝ᵥ x : ℝ) : EReal) ≤ (1 : EReal) + (t : EReal) * fenchelConjugate n f y := by
  intro y
  have hfy :
      ((y ⬝ᵥ (t⁻¹ • x) : ℝ) : EReal) ≤ f ((t⁻¹) • x) + fenchelConjugate n f y := by
    have h := dotProduct_le_add_fenchelConjugate f hf_nonneg hf0 (t⁻¹ • x) y
    simpa [dotProduct_comm] using h
  have hmul :
      (t : EReal) * ((y ⬝ᵥ (t⁻¹ • x) : ℝ) : EReal) ≤
        (t : EReal) * (f ((t⁻¹) • x) + fenchelConjugate n f y) :=
    mul_le_mul_of_nonneg_left hfy (by exact_mod_cast (le_of_lt ht))
  have hleft :
      (t : EReal) * ((y ⬝ᵥ (t⁻¹ • x) : ℝ) : EReal) = ((y ⬝ᵥ x : ℝ) : EReal) := by
    have htne : (t : ℝ) ≠ 0 := by linarith
    have hreal :
        t * (y ⬝ᵥ (t⁻¹ • x) : ℝ) = (y ⬝ᵥ x : ℝ) := by
      calc
        t * (y ⬝ᵥ (t⁻¹ • x) : ℝ) = t * (t⁻¹ * (y ⬝ᵥ x : ℝ)) := by
          simp [dotProduct_smul, smul_eq_mul, mul_comm]
        _ = (t * t⁻¹) * (y ⬝ᵥ x : ℝ) := by ring
        _ = (1 : ℝ) * (y ⬝ᵥ x : ℝ) := by simp [htne]
        _ = (y ⬝ᵥ x : ℝ) := by ring
    exact_mod_cast hreal
  have hright :
      (t : EReal) * (f ((t⁻¹) • x) + fenchelConjugate n f y) =
        (t : EReal) * f ((t⁻¹) • x) + (t : EReal) * fenchelConjugate n f y := by
    have hf_nonneg' : (0 : EReal) ≤ f ((t⁻¹) • x) := hf_nonneg _
    have hfc_nonneg : (0 : EReal) ≤ fenchelConjugate n f y :=
      fenchelConjugate_nonneg_of_nonneg_zero f hf0 y
    exact EReal.left_distrib_of_nonneg hf_nonneg' hfc_nonneg
  have hmul' : ((y ⬝ᵥ x : ℝ) : EReal) ≤ (t : EReal) * f ((t⁻¹) • x) +
        (t : EReal) * fenchelConjugate n f y := by
    have hmul' := hmul
    rw [hleft] at hmul'
    rw [hright] at hmul'
    exact hmul'
  have hmul'' :
      (t : EReal) * f ((t⁻¹) • x) + (t : EReal) * fenchelConjugate n f y ≤
        (1 : EReal) + (t : EReal) * fenchelConjugate n f y := by
    have h := add_le_add_right hle ((t : EReal) * fenchelConjugate n f y)
    simpa [add_comm, add_left_comm, add_assoc] using h
  exact le_trans hmul' (by
    simpa [add_comm, add_left_comm, add_assoc] using hmul'')

/-- Polar feasibility implies the dilation inequality for a positive scale. -/
lemma polar_feasible_imp_dilation_le_one_pos {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_closed : ClosedConvexFunction f) (hf0 : f 0 = 0)
    {x : Fin n → ℝ} {t : ℝ} (ht : 0 < t)
    (hfeas :
      ∀ y, ((y ⬝ᵥ x : ℝ) : EReal) ≤ (1 : EReal) + (t : EReal) * fenchelConjugate n f y) :
    (t : EReal) * f ((t⁻¹) • x) ≤ (1 : EReal) := by
  have ht_inv_pos : 0 < t⁻¹ := by exact inv_pos.mpr ht
  let tInv : EReal := (t⁻¹ : ℝ)
  have hscale :
      ∀ y,
        ((y ⬝ᵥ (t⁻¹ • x) : ℝ) : EReal) ≤
          tInv + fenchelConjugate n f y := by
    intro y
    have hmul :
        tInv * ((y ⬝ᵥ x : ℝ) : EReal) ≤
          tInv * ((1 : EReal) + (t : EReal) * fenchelConjugate n f y) :=
      mul_le_mul_of_nonneg_left (hfeas y) (by
        have : (0 : EReal) ≤ ((t⁻¹ : ℝ) : EReal) := by
          exact_mod_cast (le_of_lt ht_inv_pos)
        simpa [tInv] using this)
    have hleft :
        tInv * ((y ⬝ᵥ x : ℝ) : EReal) =
          ((y ⬝ᵥ (t⁻¹ • x) : ℝ) : EReal) := by
      simp [tInv, EReal.coe_mul, dotProduct_smul, smul_eq_mul, mul_comm]
    have hright :
        tInv * ((1 : EReal) + (t : EReal) * fenchelConjugate n f y) =
          tInv + fenchelConjugate n f y := by
      have htne : (t : ℝ) ≠ 0 := by linarith
      have hfc_nonneg : (0 : EReal) ≤ fenchelConjugate n f y :=
        fenchelConjugate_nonneg_of_nonneg_zero f hf0 y
      have hmul_nonneg : (0 : EReal) ≤ (t : EReal) * fenchelConjugate n f y := by
        have ht_nonneg : (0 : EReal) ≤ (t : EReal) := by exact_mod_cast (le_of_lt ht)
        have h := mul_le_mul_of_nonneg_left hfc_nonneg ht_nonneg
        simpa using h
      have hdist :
          tInv * ((1 : EReal) + (t : EReal) * fenchelConjugate n f y) =
            tInv * (1 : EReal) + tInv * ((t : EReal) * fenchelConjugate n f y) := by
        exact EReal.left_distrib_of_nonneg (show (0 : EReal) ≤ (1 : EReal) by simp) hmul_nonneg
      have hmul' :
          tInv * ((t : EReal) * fenchelConjugate n f y) = fenchelConjugate n f y := by
        have htne' : (t : ℝ) ≠ 0 := by linarith
        calc
          tInv * ((t : EReal) * fenchelConjugate n f y) =
              (tInv * (t : EReal)) * fenchelConjugate n f y := by
                simp [mul_assoc]
          _ = (1 : EReal) * fenchelConjugate n f y := by
                have hmul_tt : tInv * (t : EReal) = (1 : EReal) := by
                  dsimp [tInv]
                  rw [← EReal.coe_mul]
                  simp [htne']
                simp [hmul_tt]
          _ = fenchelConjugate n f y := by simp
      have h1 : tInv * (1 : EReal) = tInv := by
        simp [tInv]
      calc
        tInv * ((1 : EReal) + (t : EReal) * fenchelConjugate n f y) =
            tInv * (1 : EReal) + tInv * ((t : EReal) * fenchelConjugate n f y) := hdist
        _ = tInv + fenchelConjugate n f y := by
            simp [h1, hmul']
    simpa [hleft, hright] using hmul
  have hsub :
      ∀ y,
        ((y ⬝ᵥ (t⁻¹ • x) : ℝ) : EReal) - fenchelConjugate n f y ≤ tInv := by
    intro y
    refine (EReal.sub_le_iff_le_add (Or.inr (by simp [tInv])) (Or.inr (by simp [tInv]))).2 ?_
    exact hscale y
  have hsup :
      fenchelConjugate n (fenchelConjugate n f) ((t⁻¹) • x) ≤ tInv := by
    unfold fenchelConjugate
    refine sSup_le ?_
    rintro _ ⟨y, rfl⟩
    exact hsub y
  have hbiconj :
      fenchelConjugate n (fenchelConjugate n f) = f :=
    fenchelConjugate_biconjugate_eq_of_nonneg_closedConvex_zero f hf_nonneg hf_closed hf0
  have hf_le : f ((t⁻¹) • x) ≤ tInv := by
    simpa [hbiconj] using hsup
  have hnonneg : (0 : EReal) ≤ (t : EReal) := by exact_mod_cast (le_of_lt ht)
  have hmul :
      (t : EReal) * f ((t⁻¹) • x) ≤ (t : EReal) * tInv :=
    mul_le_mul_of_nonneg_left hf_le hnonneg
  have htne : (t : ℝ) ≠ 0 := by linarith
  have hmul_tt : (t : EReal) * tInv = (1 : EReal) := by
    dsimp [tInv]
    rw [← EReal.coe_mul]
    simp [htne]
  calc
    (t : EReal) * f ((t⁻¹) • x) ≤ (t : EReal) * tInv := hmul
    _ = (1 : EReal) := hmul_tt

/-- Nonzero vectors admit a dual witness with dot product exceeding `1`. -/
lemma exists_dotProduct_gt_one_of_ne_zero {n : ℕ} {x : Fin n → ℝ} (hx : x ≠ 0) :
    ∃ y : Fin n → ℝ, (1 : ℝ) < (y ⬝ᵥ x : ℝ) := by
  have hxx_ne : x ⬝ᵥ x ≠ 0 := dotProduct_self_ne_zero x hx
  refine ⟨(2 / (x ⬝ᵥ x)) • x, ?_⟩
  have hdot :
      ((2 / (x ⬝ᵥ x)) • x ⬝ᵥ x : ℝ) =
        (2 / (x ⬝ᵥ x)) * (x ⬝ᵥ x) := by
    simp
  have hdot' :
      (2 / (x ⬝ᵥ x)) * (x ⬝ᵥ x) = (2 : ℝ) := by
    field_simp [hxx_ne]
  have hdot'' : ((2 / (x ⬝ᵥ x)) • x ⬝ᵥ x : ℝ) = (2 : ℝ) := by
    simpa [hdot] using hdot'
  linarith

/-- The infimum of positive real coefficients in `EReal` is zero. -/
lemma sInf_pos_real_eq_zero :
    let S : Set EReal := {μ | ∃ t : ℝ, 0 < t ∧ μ = (t : EReal)}
    sInf S = (0 : EReal) := by
  classical
  intro S
  have h0le : (0 : EReal) ≤ sInf S := by
    refine le_sInf ?_
    intro μ hμ
    rcases hμ with ⟨t, ht, rfl⟩
    exact_mod_cast (le_of_lt ht)
  cases h : sInf S using EReal.rec with
  | bot =>
      have h0le' : (0 : EReal) ≤ (⊥ : EReal) := by
        simp [h] at h0le
      have h0eq : (0 : EReal) = (⊥ : EReal) := (le_bot_iff).1 h0le'
      have h0eq' : False := by
        simp at h0eq
      exact (False.elim h0eq')
  | top =>
      have hle : sInf S ≤ (1 : EReal) := by
        refine sInf_le ?_
        exact ⟨1, by norm_num, rfl⟩
      have htop_le : (⊤ : EReal) ≤ (1 : EReal) := by simpa [h] using hle
      exact (False.elim (not_top_le_coe 1 htop_le))
  | coe r =>
      have hle_eps : ∀ ε : ℝ, ε > 0 → r ≤ ε := by
        intro ε hε
        have hle : sInf S ≤ (ε : EReal) := by
          exact sInf_le ⟨ε, hε, rfl⟩
        have hle' : (r : EReal) ≤ (ε : EReal) := by simpa [h] using hle
        exact (EReal.coe_le_coe_iff).1 hle'
      have hle0 : r ≤ 0 := by
        refine le_of_forall_pos_le_add ?_
        intro ε hε
        simpa using (hle_eps ε hε)
      have h0le_r : 0 ≤ r := by
        have h0le' : (0 : EReal) ≤ (r : EReal) := by simpa [h] using h0le
        exact (EReal.coe_le_coe_iff).1 h0le'
      have hr0 : r = 0 := le_antisymm hle0 h0le_r
      simp [hr0]

/-- Text 15.0.31: Let `f : ℝⁿ → [0, +∞]` be a nonnegative closed convex function with `f 0 = 0`,
and define `g := f^{*∘}`. For `λ > 0`, define the dilation `f_λ x := λ * f (λ⁻¹ • x)`. Then for
every `x ∈ ℝⁿ` one has the representation

`g x = inf { λ > 0 | f_λ x ≤ 1 }`.

In this development, we model `[0, +∞]` by `EReal` together with nonnegativity assumptions, define
`g` as `polarConvex (fenchelConjugate n f)`, and represent the infimum as `sInf` in `EReal`. -/
theorem polarFenchelConjugate_eq_sInf_dilation_le_one {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_closed : ClosedConvexFunction f) (hf0 : f 0 = 0) :
    let g : (Fin n → ℝ) → EReal := polarConvex (fenchelConjugate n f)
    let fDil : ℝ → (Fin n → ℝ) → EReal := fun t x => (t : EReal) * f ((t⁻¹) • x)
    ∀ x : Fin n → ℝ,
      g x =
        sInf {μ : EReal | ∃ t : ℝ, 0 < t ∧ μ = (t : EReal) ∧ fDil t x ≤ (1 : EReal)} := by
  classical
  intro g fDil x
  let fStar : (Fin n → ℝ) → EReal := fenchelConjugate n f
  let A : Set EReal :=
    {μStar : EReal |
      0 ≤ μStar ∧
        ∀ y : Fin n → ℝ,
          ((y ⬝ᵥ x : ℝ) : EReal) ≤ (1 : EReal) + μStar * fStar y}
  let B : Set EReal :=
    {μ : EReal | ∃ t : ℝ, 0 < t ∧ μ = (t : EReal) ∧ fDil t x ≤ (1 : EReal)}
  have hg : g x = sInf A := by
    simp [g, polarConvex, A, fStar]
  have hBA : B ⊆ A := by
    intro μ hμ
    rcases hμ with ⟨t, ht, rfl, hle⟩
    refine ⟨?_, ?_⟩
    · exact_mod_cast (le_of_lt ht)
    · intro y
      exact dilation_le_one_pos_imp_polar_feasible (f := f) hf_nonneg hf0 (x := x) ht hle y
  have hle1 : sInf A ≤ sInf B := by
    refine le_sInf ?_
    intro μ hμ
    exact sInf_le (hBA hμ)
  have hle2 : sInf B ≤ sInf A := by
    by_cases hx : x = 0
    · have hB : sInf B = (0 : EReal) := by
        have hB' : B = {μ : EReal | ∃ t : ℝ, 0 < t ∧ μ = (t : EReal)} := by
          ext μ
          constructor
          · intro hμ
            rcases hμ with ⟨t, ht, rfl, -⟩
            exact ⟨t, ht, rfl⟩
          · intro hμ
            rcases hμ with ⟨t, ht, rfl⟩
            have hle : fDil t x ≤ (1 : EReal) := by
              have hzero : fDil t x = (0 : EReal) := by
                simp [fDil, hx, hf0]
              simp [hzero]
            exact ⟨t, ht, rfl, hle⟩
        simpa [hB'] using (sInf_pos_real_eq_zero)
      have hA : (0 : EReal) ≤ sInf A := by
        refine le_sInf ?_
        intro μ hμ
        exact hμ.1
      simpa [hB] using hA
    · refine le_sInf ?_
      intro μ hμ
      rcases hμ with ⟨hμ_nonneg, hμineq⟩
      cases hμ' : μ using EReal.rec with
      | bot =>
          have h0le : (0 : EReal) ≤ (⊥ : EReal) := by
            simp [hμ'] at hμ_nonneg
          have h0eq : (0 : EReal) = (⊥ : EReal) := (le_bot_iff).1 h0le
          have h0eq' : False := by
            simp at h0eq
          exact (False.elim h0eq')
      | top =>
          exact le_top
      | coe t =>
          have ht_nonneg : 0 ≤ t := by
            have hμ_nonneg' := hμ_nonneg
            simp [hμ'] at hμ_nonneg'
            exact hμ_nonneg'
          have htne : t ≠ 0 := by
            intro ht0
            have hμ0 : μ = (0 : EReal) := by simp [hμ', ht0]
            rcases exists_dotProduct_gt_one_of_ne_zero (x := x) hx with ⟨y, hy⟩
            have hineq' :
                ((y ⬝ᵥ x : ℝ) : EReal) ≤ (1 : EReal) + (0 : EReal) := by
              have hineq'' :
                  ((y ⬝ᵥ x : ℝ) : EReal) ≤ (1 : EReal) + μ * fStar y := by
                simpa [hμ'] using hμineq y
              simpa [hμ0] using hineq''
            have hineqR :
                (y ⬝ᵥ x : ℝ) ≤ (1 : ℝ) := by
              have hineqR' :
                  ((y ⬝ᵥ x : ℝ) : EReal) ≤ ((1 : ℝ) : EReal) := by
                simpa using hineq'
              exact (EReal.coe_le_coe_iff).1 hineqR'
            exact (not_lt_of_ge hineqR hy)
          have htpos : 0 < t := lt_of_le_of_ne ht_nonneg (Ne.symm htne)
          have hμineq' :
              ∀ y, ((y ⬝ᵥ x : ℝ) : EReal) ≤ (1 : EReal) + (t : EReal) * fStar y := by
            simpa [hμ'] using hμineq
          have hle :
              (t : EReal) * f ((t⁻¹) • x) ≤ (1 : EReal) :=
            polar_feasible_imp_dilation_le_one_pos (f := f) hf_nonneg hf_closed hf0
              (x := x) htpos hμineq'
          have hmemB : μ ∈ B := by
            exact ⟨t, htpos, hμ', hle⟩
          have hmemB' : (t : EReal) ∈ B := by
            simpa [hμ'] using hmemB
          simpa [hμ'] using (sInf_le hmemB')
  have hEq : sInf A = sInf B := le_antisymm hle1 hle2
  simpa [hg, A, B, fStar] using hEq

/-- Text 15.0.32: Let `f : ℝⁿ → [0, +∞]` be a nonnegative closed convex function with `f(0) = 0`.
For `λ > 0`, define the scaled (perspective) function `f_λ x := λ * f (x / λ)`. The obverse of
`f` is the function `g : ℝⁿ → [0, +∞]` given by
`g x := inf {λ > 0 | f_λ x ≤ 1}`.

If `f = δ(· | C)` for a closed convex set `C` containing `0`, then `g = γ(· | C)` is the gauge of
`C`. If `f = γ(· | C)` is the gauge of such a set `C`, then `g = δ(· | C)`. Thus the gauge and
indicator functions of `C` are obverses of each other.

In this development, `ℝⁿ` is `Fin n → ℝ`, `[0, +∞]` is modeled by `EReal` with nonnegativity
assumptions, `δ(· | C)` is `erealIndicator C`, and `γ(· | C)` is represented by
`fun x => (gaugeFunction C x : EReal)`. -/
noncomputable def obverseConvex {n : ℕ} (f : (Fin n → ℝ) → EReal) : (Fin n → ℝ) → EReal :=
  fun x =>
    sInf
      {μ : EReal |
        ∃ t : ℝ,
          0 < t ∧
            μ = (t : EReal) ∧
              (t : EReal) * f ((t⁻¹) • x) ≤ (1 : EReal)}

/-- The obverse constraint for an indicator reduces to scaled membership. -/
lemma obverseConvex_erealIndicator_apply_simp {n : ℕ} {C : Set (Fin n → ℝ)} {t : ℝ}
    (ht : 0 < t) (x : Fin n → ℝ) :
    ((t : EReal) * erealIndicator C ((t⁻¹) • x) ≤ (1 : EReal)) ↔ x ∈ t • C := by
  have htne : (t : ℝ) ≠ 0 := ne_of_gt ht
  have hxmem : x ∈ t • C ↔ (t⁻¹) • x ∈ C := by
    constructor
    · intro hx
      rcases hx with ⟨y, hyC, rfl⟩
      simpa [smul_smul, htne] using hyC
    · intro hx
      refine ⟨(t⁻¹) • x, hx, ?_⟩
      simp [smul_smul, htne]
  by_cases hx : (t⁻¹) • x ∈ C
  · simp [erealIndicator, hx, hxmem]
  · have hxmem' : x ∉ t • C := by
      intro hxmem'
      exact hx ((hxmem).1 hxmem')
    have hne : ((1 : ℝ) : EReal) ≠ (⊤ : EReal) := by
      simpa using (EReal.coe_ne_top (1 : ℝ))
    have hfalse :
        ¬ ((t : EReal) * erealIndicator C ((t⁻¹) • x) ≤ (1 : EReal)) := by
      intro hle
      have hle' := hle
      simp [erealIndicator, hx, EReal.coe_mul_top_of_pos ht] at hle'
      exact hne hle'
    constructor
    · intro hle
      exact (hfalse hle).elim
    · intro hxmem
      exact (hxmem' hxmem).elim

/-- Text 15.0.32 (indicator case): if `f = δ(· | C)` for a closed convex absorbing set `C`
containing `0`, then its obverse is `γ(· | C)`. -/
lemma obverseConvex_erealIndicator_eq_gaugeFunction {n : ℕ} (C : Set (Fin n → ℝ))
    (h0C : (0 : Fin n → ℝ) ∈ C)
    (hCabs : ∀ x : Fin n → ℝ, ∃ lam : ℝ, 0 ≤ lam ∧ x ∈ (fun y => lam • y) '' C) :
    obverseConvex (erealIndicator C) = fun x => (gaugeFunction C x : EReal) := by
  classical
  funext x
  let A : Set ℝ := {t : ℝ | 0 ≤ t ∧ x ∈ t • C}
  let T : Set ℝ := {t : ℝ | 0 < t ∧ x ∈ t • C}
  have hA_nonempty : A.Nonempty := by
    rcases hCabs x with ⟨lam, hlam, hxmem⟩
    have hxmem' : x ∈ lam • C := by simpa using hxmem
    exact ⟨lam, ⟨hlam, hxmem'⟩⟩
  have hA_bdd : BddBelow A := by
    refine ⟨0, ?_⟩
    intro r hr
    exact hr.1
  have hSet :
      {μ : EReal |
          ∃ t : ℝ,
            0 < t ∧ μ = (t : EReal) ∧
              (t : EReal) * erealIndicator C ((t⁻¹) • x) ≤ (1 : EReal)} =
        (fun t : ℝ => (t : EReal)) '' T := by
    ext μ
    constructor
    · rintro ⟨t, ht, rfl, hle⟩
      have hxmem : x ∈ t • C :=
        (obverseConvex_erealIndicator_apply_simp (C := C) (t := t) ht x).1 hle
      exact ⟨t, ⟨ht, hxmem⟩, rfl⟩
    · rintro ⟨t, ⟨ht, hxmem⟩, rfl⟩
      have hle :
          (t : EReal) * erealIndicator C ((t⁻¹) • x) ≤ (1 : EReal) :=
        (obverseConvex_erealIndicator_apply_simp (C := C) (t := t) ht x).2 hxmem
      exact ⟨t, ht, rfl, hle⟩
  have hObv :
      obverseConvex (erealIndicator C) x =
        sInf ((fun t : ℝ => (t : EReal)) '' T) := by
    simp [obverseConvex, hSet]
  have hA_eq : {r : ℝ | 0 ≤ r ∧ ∃ y ∈ C, x = r • y} = A := by
    ext r
    constructor
    · rintro ⟨hr0, y, hyC, hxy⟩
      exact ⟨hr0, ⟨y, hyC, hxy.symm⟩⟩
    · rintro ⟨hr0, ⟨y, hyC, hxy⟩⟩
      exact ⟨hr0, y, hyC, hxy.symm⟩
  have hGauge_real : gaugeFunction C x = sInf A := by
    simp [gaugeFunction, hA_eq]
  have hGauge : (gaugeFunction C x : EReal) = ((sInf A : ℝ) : EReal) := by
    exact_mod_cast hGauge_real
  by_cases hx0 : x = 0
  · have hT : T = {t : ℝ | 0 < t} := by
      ext t
      constructor
      · intro ht
        exact ht.1
      · intro ht
        refine ⟨ht, ?_⟩
        have hmem0 : (0 : Fin n → ℝ) ∈ t • C := by
          refine ⟨0, h0C, ?_⟩
          simp
        simpa [hx0] using hmem0
    have hTimg :
        (fun t : ℝ => (t : EReal)) '' T =
          {μ : EReal | ∃ t : ℝ, 0 < t ∧ μ = (t : EReal)} := by
      ext μ
      constructor
      · rintro ⟨t, ht, rfl⟩
        have ht' : 0 < t := by simpa [hT] using ht
        exact ⟨t, ht', rfl⟩
      · rintro ⟨t, ht, rfl⟩
        have ht' : t ∈ T := by
          simpa [hT] using ht
        exact ⟨t, ht', rfl⟩
    have hObv0 : obverseConvex (erealIndicator C) x = (0 : EReal) := by
      have hpos : sInf ((fun t : ℝ => (t : EReal)) '' T) = (0 : EReal) := by
        simpa [hTimg] using (sInf_pos_real_eq_zero)
      simp [hObv, hpos]
    have hA0 : sInf A = 0 := by
      have hmem0 : (0 : ℝ) ∈ A := by
        refine ⟨le_rfl, ?_⟩
        have hmem0' : (0 : Fin n → ℝ) ∈ (0 : ℝ) • C := by
          refine ⟨0, h0C, ?_⟩
          simp
        simpa [hx0] using hmem0'
      have hle : sInf A ≤ 0 := csInf_le hA_bdd hmem0
      have hge : 0 ≤ sInf A := le_csInf hA_nonempty (by intro r hr; exact hr.1)
      exact le_antisymm hle hge
    have hGauge0 : (gaugeFunction C x : EReal) = (0 : EReal) := by
      simpa [hA0] using hGauge
    simp [hObv0, hGauge0]
  · have hAT : A = T := by
      ext t
      constructor
      · rintro ⟨ht0, hmem⟩
        have htne : t ≠ 0 := by
          intro ht0'
          subst ht0'
          rcases hmem with ⟨y, hyC, hxy⟩
          have hxeq : x = 0 := by
            simpa using hxy.symm
          exact hx0 hxeq
        exact ⟨lt_of_le_of_ne ht0 (Ne.symm htne), hmem⟩
      · rintro ⟨ht, hmem⟩
        exact ⟨le_of_lt ht, hmem⟩
    have hInf :
        sInf ((fun t : ℝ => (t : EReal)) '' T) = ((sInf A : ℝ) : EReal) := by
      have hInfA := sInf_coe_image_eq_sInf_real (A := A) hA_nonempty hA_bdd
      have hAT' :
          (fun t : ℝ => (t : EReal)) '' T =
            (fun t : ℝ => (t : EReal)) '' A := by
        simp [hAT]
      simpa [hAT'] using hInfA
    simp [hObv, hInf, hGauge]

/-- Text 15.0.32 (gauge case): if `f = γ(· | C)` for a closed convex absorbing set `C` containing
`0`, then its obverse is `δ(· | C)`. -/
lemma obverseConvex_gaugeFunction_eq_erealIndicator {n : ℕ} (C : Set (Fin n → ℝ))
    (hC_closed : IsClosed C) (hC_conv : Convex ℝ C) (h0C : (0 : Fin n → ℝ) ∈ C)
    (hCabs : ∀ x : Fin n → ℝ, ∃ lam : ℝ, 0 ≤ lam ∧ x ∈ (fun y => lam • y) '' C) :
    obverseConvex (fun x => (gaugeFunction C x : EReal)) = erealIndicator C := by
  classical
  funext x
  let k : (Fin n → ℝ) → EReal := fun x => (gaugeFunction C x : EReal)
  have hk : IsGauge k :=
    gaugeFunctionEReal_isGauge_of_closed_convex_zeroMem_absorbing
      (C := C) hC_closed hC_conv h0C hCabs
  have hmul : ∀ {t : ℝ}, 0 < t → (t : EReal) * k ((t⁻¹) • x) = k x := by
    intro t ht
    have hhom :
        k (t • ((t⁻¹) • x)) = (t : EReal) * k ((t⁻¹) • x) :=
      hk.2.2.1 ((t⁻¹) • x) t (le_of_lt ht)
    calc
      (t : EReal) * k ((t⁻¹) • x) = k (t • ((t⁻¹) • x)) := by
        simpa using hhom.symm
      _ = k x := by
        simp [k, smul_smul, (ne_of_gt ht)]
  have hCset : C = {x : Fin n → ℝ | k x ≤ (1 : EReal)} := by
    simpa [k] using
      (set_eq_gaugeFunction_sublevel_one (n := n) (D := C) hC_closed hC_conv h0C hCabs)
  by_cases hx : k x ≤ (1 : EReal)
  · have hset :
        {μ : EReal |
            ∃ t : ℝ,
              0 < t ∧ μ = (t : EReal) ∧ (t : EReal) * k ((t⁻¹) • x) ≤ (1 : EReal)} =
          {μ : EReal | ∃ t : ℝ, 0 < t ∧ μ = (t : EReal)} := by
        ext μ
        constructor
        · rintro ⟨t, ht, rfl, -⟩
          exact ⟨t, ht, rfl⟩
        · rintro ⟨t, ht, rfl⟩
          have hle : (t : EReal) * k ((t⁻¹) • x) ≤ (1 : EReal) := by
            have hmul' : (t : EReal) * k ((t⁻¹) • x) = k x := hmul ht
            simpa [hmul'] using hx
          exact ⟨t, ht, rfl, hle⟩
    have hObv : obverseConvex k x = (0 : EReal) := by
      have hpos : sInf {μ : EReal | ∃ t : ℝ, 0 < t ∧ μ = (t : EReal)} = (0 : EReal) := by
        simpa using (sInf_pos_real_eq_zero)
      simp [obverseConvex, hset, hpos]
    have hxC : x ∈ C := by
      have hx' : x ∈ {x : Fin n → ℝ | k x ≤ (1 : EReal)} := by
        simpa using hx
      simpa [hCset] using hx'
    simp [hObv, erealIndicator, hxC, k]
  · have hset_empty :
        {μ : EReal |
            ∃ t : ℝ,
              0 < t ∧ μ = (t : EReal) ∧ (t : EReal) * k ((t⁻¹) • x) ≤ (1 : EReal)} =
          (∅ : Set EReal) := by
        ext μ
        constructor
        · rintro ⟨t, ht, rfl, hle⟩
          have hmul' : (t : EReal) * k ((t⁻¹) • x) = k x := hmul ht
          have hx' : k x ≤ (1 : EReal) := by
            simpa [hmul'] using hle
          exact (hx hx').elim
        · intro hμ
          exact hμ.elim
    have hObv : obverseConvex k x = (⊤ : EReal) := by
      simp [obverseConvex, hset_empty]
    have hxC : x ∉ C := by
      intro hxC
      have hx' : k x ≤ (1 : EReal) := by
        have hx' : x ∈ {x : Fin n → ℝ | k x ≤ (1 : EReal)} := by
          simpa [hCset] using hxC
        simpa using hx'
      exact hx hx'
    simp [hObv, erealIndicator, hxC, k]

/-- The obverse `sInf` set is the image of its positive real parameters. -/
lemma obverseConvex_set_eq_image_pos {n : ℕ} (f : (Fin n → ℝ) → EReal) (x : Fin n → ℝ) :
    {μ : EReal |
        ∃ t : ℝ,
          0 < t ∧ μ = (t : EReal) ∧
            (t : EReal) * f ((t⁻¹) • x) ≤ (1 : EReal)} =
      (fun t : ℝ => (t : EReal)) ''
        {t : ℝ | 0 < t ∧ (t : EReal) * f ((t⁻¹) • x) ≤ (1 : EReal)} := by
  ext μ
  constructor
  · rintro ⟨t, ht, rfl, hle⟩
    exact ⟨t, ⟨ht, hle⟩, rfl⟩
  · rintro ⟨t, ⟨ht, hle⟩, rfl⟩
    exact ⟨t, ht, rfl, hle⟩

/-- Feasibility at a positive scalar gives an upper bound for the obverse. -/
lemma obverseConvex_le_coe_pos_of_perspective_le_one {n : ℕ} (f : (Fin n → ℝ) → EReal)
    {t : ℝ} (ht : 0 < t) (x : Fin n → ℝ)
    (hle : (t : EReal) * f ((t⁻¹) • x) ≤ (1 : EReal)) :
    obverseConvex f x ≤ (t : EReal) := by
  unfold obverseConvex
  refine sInf_le ?_
  exact ⟨t, ht, rfl, hle⟩

/-- The obverse is always nonnegative. -/
lemma obverseConvex_nonneg {n : ℕ} (f : (Fin n → ℝ) → EReal) (x : Fin n → ℝ) :
    (0 : EReal) ≤ obverseConvex f x := by
  unfold obverseConvex
  refine le_sInf ?_
  intro μ hμ
  rcases hμ with ⟨t, ht, rfl, -⟩
  exact_mod_cast (le_of_lt ht)

/-- An element below a strict upper bound for `sInf` exists in a nonempty real set. -/
lemma exists_lt_of_sInf_lt {S : Set ℝ} (hne : S.Nonempty) {a : ℝ} (h : sInf S < a) :
    ∃ s ∈ S, s < a := by
  classical
  by_contra hcontra
  have hle : a ≤ sInf S := by
    refine le_csInf hne ?_
    intro s hs
    by_contra hlt
    have hlt' : s < a := lt_of_not_ge hlt
    exact hcontra ⟨s, hs, hlt'⟩
  exact (not_le_of_gt h) hle

/-- For positive `t`, scaling inequality is equivalent to a reciprocal bound. -/
lemma mul_le_one_iff_le_inv_pos {t : ℝ} {a : EReal} (ht : 0 < t) (ha : 0 ≤ a) :
    (t : EReal) * a ≤ (1 : EReal) ↔ a ≤ (t⁻¹ : EReal) := by
  by_cases htop : a = (⊤ : EReal)
  · subst htop
    constructor
    · intro hle
      have hle' : (1 : EReal) = ⊤ := by
        simpa [EReal.coe_mul_top_of_pos ht] using hle
      have hne : (1 : EReal) ≠ ⊤ := by
        simpa using (EReal.coe_ne_top (1 : ℝ))
      exact (hne hle').elim
    · intro hle
      have hle' : ((t⁻¹ : ℝ) : EReal) = ⊤ := (top_le_iff).1 hle
      have hne : ((t⁻¹ : ℝ) : EReal) ≠ ⊤ := by
        simp
      exact (hne hle').elim
  · have hbot : a ≠ (⊥ : EReal) := by
      intro hbot
      have h0le : (0 : EReal) ≤ (⊥ : EReal) := by
        simp [hbot] at ha
      have hbotlt : (⊥ : EReal) < (0 : EReal) := by simp
      exact (not_le_of_gt hbotlt) h0le
    set r : ℝ := a.toReal
    have hr : (r : EReal) = a := EReal.coe_toReal htop hbot
    constructor
    · intro hle
      have hle' : (t * r : ℝ) ≤ 1 := by
        have hle'' : (t : EReal) * (r : EReal) ≤ (1 : EReal) := by
          simpa [hr] using hle
        have hle''' : ((t * r : ℝ) : EReal) ≤ (1 : EReal) := by
          simpa [EReal.coe_mul] using hle''
        exact (EReal.coe_le_coe_iff).1 hle'''
      have htne : t ≠ 0 := by linarith
      have hmul :
          (t⁻¹) * (t * r) ≤ (t⁻¹) * (1 : ℝ) :=
        mul_le_mul_of_nonneg_left hle' (le_of_lt (inv_pos.mpr ht))
      have hmul' : (t⁻¹) * (t * r) = r := by
        field_simp [htne]
      have hmul'' : (t⁻¹) * (1 : ℝ) = t⁻¹ := by ring
      have hle_real : r ≤ t⁻¹ := by
        simpa [hmul', hmul''] using hmul
      have hle_ereal : (r : EReal) ≤ (t : EReal)⁻¹ := by
        have hle' : (r : EReal) ≤ (t⁻¹ : EReal) := by
          exact (EReal.coe_le_coe_iff).2 hle_real
        simpa [EReal.coe_inv] using hle'
      have hle_final : a ≤ (t : EReal)⁻¹ := by
        calc
          a = (r : EReal) := hr.symm
          _ ≤ (t : EReal)⁻¹ := hle_ereal
      simpa [EReal.coe_inv] using hle_final
    · intro hle
      have hle_real : r ≤ t⁻¹ := by
        have hle' : (r : EReal) ≤ (t⁻¹ : EReal) := by
          simpa [hr] using hle
        exact (EReal.coe_le_coe_iff).1 hle'
      have hmul_real : t * r ≤ 1 := by
        have hmul := mul_le_mul_of_nonneg_left hle_real (le_of_lt ht)
        have htne : t ≠ 0 := by linarith
        have hmul' : t * t⁻¹ = (1 : ℝ) := by
          field_simp [htne]
        simpa [hmul'] using hmul
      have hmul_ereal : (t : EReal) * (r : EReal) ≤ (1 : EReal) := by
        have hmul' : ((t * r : ℝ) : EReal) ≤ (1 : EReal) := by
          exact_mod_cast hmul_real
        simpa [EReal.coe_mul] using hmul'
      simpa [hr] using hmul_ereal

/-- Feasibility at a smaller scale implies feasibility at a larger scale. -/
lemma perspective_isUpperSet {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_conv : ConvexFunctionOn (S := (Set.univ : Set (Fin n → ℝ))) f) (hf0 : f 0 = 0)
    {x : Fin n → ℝ} {s t : ℝ} (hs : 0 < s) (hst : s ≤ t)
    (hle : (s : EReal) * f ((s⁻¹) • x) ≤ (1 : EReal)) :
    (t : EReal) * f ((t⁻¹) • x) ≤ (1 : EReal) := by
  by_cases hst' : s = t
  · subst hst'
    simpa using hle
  have htpos : 0 < t := lt_of_lt_of_le hs hst
  set a : ℝ := s / t
  have ha_pos : 0 < a := by
    dsimp [a]
    exact div_pos hs htpos
  have ha_lt : a < 1 := by
    have hstlt : s < t := lt_of_le_of_ne hst hst'
    dsimp [a]
    exact (div_lt_one htpos).2 hstlt
  have hnotbot : ∀ x ∈ (Set.univ : Set (Fin n → ℝ)), f x ≠ (⊥ : EReal) := by
    intro x hx hbot
    have h0le : (0 : EReal) ≤ (⊥ : EReal) := by
      simpa [hbot] using (hf_nonneg x)
    have hbotlt : (⊥ : EReal) < (0 : EReal) := by simp
    exact (not_le_of_gt hbotlt) h0le
  have hseg :
      f ((1 - a) • (0 : Fin n → ℝ) + a • ((s⁻¹) • x)) ≤
        ((1 - a : ℝ) : EReal) * f (0 : Fin n → ℝ) + ((a : ℝ) : EReal) * f ((s⁻¹) • x) :=
    (convexFunctionOn_iff_segment_inequality (C := (Set.univ : Set (Fin n → ℝ))) (f := f)
        (hC := convex_univ) (hnotbot := hnotbot)).1 hf_conv
      (0 : Fin n → ℝ) (by simp) ((s⁻¹) • x) (by simp) a ha_pos ha_lt
  have hsmul : a • ((s⁻¹) • x) = (t⁻¹) • x := by
    have hsne : (s : ℝ) ≠ 0 := by linarith
    have htne : (t : ℝ) ≠ 0 := by linarith
    calc
      a • ((s⁻¹) • x) = (a * s⁻¹) • x := by simp [smul_smul]
      _ = (t⁻¹) • x := by
        dsimp [a]
        field_simp [hsne, htne]
  have hineq :
      f ((t⁻¹) • x) ≤ ((a : ℝ) : EReal) * f ((s⁻¹) • x) := by
    simpa [hsmul, hf0, smul_zero, zero_add] using hseg
  have ht_nonneg : (0 : EReal) ≤ (t : EReal) := by exact_mod_cast (le_of_lt htpos)
  have hmul :
      (t : EReal) * f ((t⁻¹) • x) ≤
        (t : EReal) * (((a : ℝ) : EReal) * f ((s⁻¹) • x)) :=
    mul_le_mul_of_nonneg_left hineq ht_nonneg
  have htne : (t : ℝ) ≠ 0 := by linarith
  have hmul_ta : (t : EReal) * ((a : ℝ) : EReal) = (s : EReal) := by
    dsimp [a]
    rw [← EReal.coe_mul]
    field_simp [htne]
  have hmul' :
      (t : EReal) * (((a : ℝ) : EReal) * f ((s⁻¹) • x)) =
        (s : EReal) * f ((s⁻¹) • x) := by
    calc
      (t : EReal) * (((a : ℝ) : EReal) * f ((s⁻¹) • x)) =
          ((t : EReal) * ((a : ℝ) : EReal)) * f ((s⁻¹) • x) := by
            simp [mul_assoc]
      _ = (s : EReal) * f ((s⁻¹) • x) := by simp [hmul_ta]
  have hfinal :
      (t : EReal) * f ((t⁻¹) • x) ≤ (s : EReal) * f ((s⁻¹) • x) := by
    simpa [hmul'] using hmul
  exact le_trans hfinal hle

/-- Obverse at a positive scalar equals the perspective sublevel inequality. -/
lemma obverseConvex_le_coe_pos_iff_perspective_le_one {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_closed : ClosedConvexFunction f) (hf0 : f 0 = 0)
    {x : Fin n → ℝ} {lam : ℝ} (hlam : 0 < lam) :
    obverseConvex f x ≤ (lam : EReal) ↔ (lam : EReal) * f ((lam⁻¹) • x) ≤ (1 : EReal) := by
  classical
  let T : Set ℝ :=
    {t : ℝ | 0 < t ∧ (t : EReal) * f ((t⁻¹) • x) ≤ (1 : EReal)}
  have hT_bdd : BddBelow T := by
    refine ⟨0, ?_⟩
    intro t ht
    exact le_of_lt ht.1
  have hset :
      {μ : EReal |
          ∃ t : ℝ,
            0 < t ∧ μ = (t : EReal) ∧
              (t : EReal) * f ((t⁻¹) • x) ≤ (1 : EReal)} =
        (fun t : ℝ => (t : EReal)) '' T := by
    simpa [T] using (obverseConvex_set_eq_image_pos f x)
  constructor
  · intro hle
    have hT_ne : T.Nonempty := by
      by_contra hT_ne
      have hT_empty : T = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.2
        intro t ht
        exact hT_ne ⟨t, ht⟩
      have hObv : obverseConvex f x = ⊤ := by
        simp [obverseConvex, hset, hT_empty]
      have hcontr : ¬ (⊤ : EReal) ≤ (lam : EReal) := not_top_le_coe lam
      have hle' := hle
      simp [hObv] at hle'
    have hObv :
        obverseConvex f x = ((sInf T : ℝ) : EReal) := by
      calc
        obverseConvex f x =
            sInf ((fun t : ℝ => (t : EReal)) '' T) := by
              simp [obverseConvex, hset]
        _ = ((sInf T : ℝ) : EReal) :=
            sInf_coe_image_eq_sInf_real (A := T) hT_ne hT_bdd
    have hle_real : sInf T ≤ lam := by
      have hle' : ((sInf T : ℝ) : EReal) ≤ (lam : EReal) := by
        simpa [hObv] using hle
      exact (EReal.coe_le_coe_iff).1 hle'
    have hUpper :
        ∀ {s t : ℝ}, 0 < s → s ≤ t →
          (s : EReal) * f ((s⁻¹) • x) ≤ (1 : EReal) →
            (t : EReal) * f ((t⁻¹) • x) ≤ (1 : EReal) := by
      intro s t hs hst hle
      have hf_conv : ConvexFunctionOn (S := (Set.univ : Set (Fin n → ℝ))) f := by
        simpa [ConvexFunction] using hf_closed.1
      exact perspective_isUpperSet (f := f) hf_nonneg hf_conv hf0 (x := x) hs hst hle
    have hsub :
        ∀ α : ℝ, IsClosed {y | f y ≤ (α : EReal)} :=
      (lowerSemicontinuous_iff_closed_sublevel_iff_closed_epigraph (f := f)).1.1 hf_closed.2
    have hmem_eps : ∀ ε : ℝ, 0 < ε → (lam + ε) ∈ T := by
      intro ε hε
      have hlt : sInf T < lam + ε := by linarith
      rcases exists_lt_of_sInf_lt hT_ne hlt with ⟨t, htT, htlt⟩
      have hle' : t ≤ lam + ε := le_of_lt htlt
      have hpos : 0 < t := htT.1
      have hle_pers :
          (lam + ε : EReal) * f (((lam + ε)⁻¹) • x) ≤ (1 : EReal) :=
        hUpper hpos hle' htT.2
      exact ⟨by linarith, hle_pers⟩
    set tSeq : ℕ → ℝ := fun n => lam + (n : ℝ)⁻¹
    have htend : Filter.Tendsto tSeq Filter.atTop (𝓝 lam) := by
      simpa [tSeq] using
        (tendsto_const_nhds.add (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)))
    have htend_inv : Filter.Tendsto (fun n => (tSeq n)⁻¹) Filter.atTop (𝓝 (lam⁻¹)) :=
      (Filter.Tendsto.inv₀ htend (ne_of_gt hlam))
    have hcont_smul : Continuous (fun r : ℝ => r • x) := by
      have hpair : Continuous fun r : ℝ => (r, x) := continuous_id.prodMk continuous_const
      simpa using (continuous_smul.comp hpair)
    have htend_smul :
        Filter.Tendsto (fun n => (tSeq n)⁻¹ • x) Filter.atTop (𝓝 ((lam⁻¹) • x)) :=
      (hcont_smul.tendsto (lam⁻¹)).comp htend_inv
    have hmem_sublevel :
        ∀ᶠ n in Filter.atTop, (tSeq n)⁻¹ • x ∈ {y | f y ≤ (lam⁻¹ : EReal)} := by
      refine Filter.eventually_atTop.2 ?_
      refine ⟨1, ?_⟩
      intro n hn
      have hnpos : 0 < (n : ℝ) := by
        exact_mod_cast (Nat.succ_le_iff.mp hn)
      have htn : tSeq n ∈ T := hmem_eps ((n : ℝ)⁻¹) (by
        simpa using (inv_pos.mpr hnpos))
      have hle_t :
          f ((tSeq n)⁻¹ • x) ≤ ((tSeq n)⁻¹ : EReal) :=
        (mul_le_one_iff_le_inv_pos (t := tSeq n) htn.1 (hf_nonneg _)).1 htn.2
      have hle_inv : (tSeq n)⁻¹ ≤ lam⁻¹ := by
        have hle_tseq : lam ≤ tSeq n := by
          dsimp [tSeq]
          have hpos : 0 ≤ (n : ℝ)⁻¹ := by
            exact inv_nonneg.mpr (le_of_lt hnpos)
          exact le_add_of_nonneg_right hpos
        simpa [one_div] using (one_div_le_one_div_of_le hlam hle_tseq)
      have hle_inv' : ((tSeq n)⁻¹ : EReal) ≤ (lam⁻¹ : EReal) := by
        exact (EReal.coe_le_coe_iff).2 hle_inv
      exact le_trans hle_t hle_inv'
    have hmem_lim :
        (lam⁻¹) • x ∈ {y | f y ≤ (lam⁻¹ : EReal)} :=
      (hsub (lam⁻¹)).mem_of_tendsto htend_smul hmem_sublevel
    have hle_inv : f ((lam⁻¹) • x) ≤ (lam⁻¹ : EReal) := by
      simpa using hmem_lim
    exact (mul_le_one_iff_le_inv_pos (t := lam) hlam (hf_nonneg _)).2 hle_inv
  · intro hle
    exact obverseConvex_le_coe_pos_of_perspective_le_one (f := f) hlam x hle


end Section15
end Chap03
