/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yijie Wang, Yunxi Duan, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section12_part9
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part22
section Chap03
section Section15

open scoped BigOperators
open scoped Pointwise

/-- Corollary 15.4.1: The polarity mapping `f ↦ fᵒ` induces a symmetric one-to-one correspondence
on the class of all nonnegative closed convex functions on `ℝⁿ` that vanish at the origin.

In this development, `fᵒ` is `polarConvex f`. -/
noncomputable def polarConvexEquiv_nonneg_closedConvex_zero {n : ℕ} :
    {f : (Fin n → ℝ) → EReal //
        (∀ x, 0 ≤ f x) ∧ ClosedConvexFunction f ∧ f 0 = 0} ≃
      {f : (Fin n → ℝ) → EReal //
        (∀ x, 0 ≤ f x) ∧ ClosedConvexFunction f ∧ f 0 = 0} := by
  classical
  refine
    { toFun := fun f =>
        ⟨polarConvex f.1, by
          exact polarConvex_mem_subtype_nonneg_closedConvex_zero (n := n) f⟩
      invFun := fun f =>
        ⟨polarConvex f.1, by
          exact polarConvex_mem_subtype_nonneg_closedConvex_zero (n := n) f⟩
      left_inv := by
        intro f
        apply Subtype.ext
        funext x
        have h := polarConvex_involutive_on_subtype (n := n) f
        simpa using congrArg (fun g => g x) h
      right_inv := by
        intro f
        apply Subtype.ext
        funext x
        have h := polarConvex_involutive_on_subtype (n := n) f
        simpa using congrArg (fun g => g x) h }

/-- The obverse is the polar of the Fenchel conjugate under nonnegativity and closedness. -/
lemma obverseConvex_eq_polarConvex_fenchelConjugate {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_closed : ClosedConvexFunction f) (hf0 : f 0 = 0) :
    obverseConvex f = polarConvex (fenchelConjugate n f) := by
  classical
  funext x
  have h :=
    polarFenchelConjugate_eq_sInf_dilation_le_one (f := f) hf_nonneg hf_closed hf0
  simpa [obverseConvex] using (h x).symm

/-- Nonnegativity and `f 0 = 0` force the Fenchel conjugate to vanish at `0`. -/
lemma fenchelConjugate_zero_eq_zero_of_nonneg_zero {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf0 : f 0 = 0) : fenchelConjugate n f 0 = 0 := by
  have h0le : (0 : EReal) ≤ iInf fun x : Fin n → ℝ => f x := by
    refine le_iInf ?_
    intro x
    exact hf_nonneg x
  have hle0 : (iInf fun x : Fin n → ℝ => f x) ≤ (0 : EReal) := by
    simpa [hf0] using (iInf_le (fun x : Fin n → ℝ => f x) (0 : Fin n → ℝ))
  have hInf : (iInf fun x : Fin n → ℝ => f x) = (0 : EReal) := le_antisymm hle0 h0le
  simpa [hInf] using (fenchelConjugate_zero_eq_neg_iInf (n := n) (f := f))

/-- The polar of the obverse recovers the Fenchel conjugate. -/
lemma polarConvex_obverseConvex_eq_fenchelConjugate {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_closed : ClosedConvexFunction f) (hf0 : f 0 = 0) :
    polarConvex (obverseConvex f) = fenchelConjugate n f := by
  have hStar_nonneg : ∀ x, 0 ≤ fenchelConjugate n f x :=
    fenchelConjugate_nonneg_of_nonneg_zero f hf0
  have hStar_closed : ClosedConvexFunction (fenchelConjugate n f) := by
    have h := fenchelConjugate_closedConvex (n := n) (f := f)
    exact ⟨h.2, h.1⟩
  have hStar0 : fenchelConjugate n f 0 = 0 :=
    fenchelConjugate_zero_eq_zero_of_nonneg_zero (f := f) hf_nonneg hf0
  have h_invol :=
    polarConvex_involutive_on_subtype (n := n)
      (⟨fenchelConjugate n f, ⟨hStar_nonneg, hStar_closed, hStar0⟩⟩ :
        {g : (Fin n → ℝ) → EReal //
          (∀ x, 0 ≤ g x) ∧ ClosedConvexFunction g ∧ g 0 = 0})
  rw [obverseConvex_eq_polarConvex_fenchelConjugate (f := f) hf_nonneg hf_closed hf0]
  simpa using h_invol

/-- The obverse vanishes at `0` under nonnegativity and `f 0 = 0`. -/
lemma obverseConvex_zero_of_nonneg_zero {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hf0 : f 0 = 0) : obverseConvex f 0 = 0 := by
  classical
  unfold obverseConvex
  have hset :
      {μ : EReal |
          ∃ t : ℝ,
            0 < t ∧ μ = (t : EReal) ∧
              (t : EReal) * f (0 : Fin n → ℝ) ≤ (1 : EReal)} =
        {μ : EReal | ∃ t : ℝ, 0 < t ∧ μ = (t : EReal)} := by
    ext μ
    constructor
    · rintro ⟨t, ht, rfl, -⟩
      exact ⟨t, ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      have hle : (t : EReal) * f (0 : Fin n → ℝ) ≤ (1 : EReal) := by
        simp [hf0]
      exact ⟨t, ht, rfl, hle⟩
  have hpos :
      sInf {μ : EReal | ∃ t : ℝ, 0 < t ∧ μ = (t : EReal)} = (0 : EReal) := by
    simpa using (sInf_pos_real_eq_zero)
  simp [smul_zero, hset, hpos]

/-- A feasible dilation inequality bounds the obverse at a scaled point. -/
lemma obverseConvex_smul_le_coe_of_mul_le_one {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_closed : ClosedConvexFunction f) (hf0 : f 0 = 0)
    {t : ℝ} (ht : 0 < t) {y : Fin n → ℝ} :
    ((t : EReal) * f y ≤ (1 : EReal)) → obverseConvex f (t • y) ≤ (t : EReal) := by
  intro hle
  have hiff :=
    (obverseConvex_le_coe_pos_iff_perspective_le_one (f := f) hf_nonneg hf_closed hf0
      (x := t • y) (lam := t) ht)
  have htne : (t : ℝ) ≠ 0 := ne_of_gt ht
  have hle' : (t : EReal) * f ((t⁻¹) • (t • y)) ≤ (1 : EReal) := by
    simpa [smul_smul, htne] using hle
  exact hiff.mpr hle'

/-- A polar-feasible `μ⋆` bounds the Fenchel conjugate of the obverse. -/
lemma fenchelConjugate_obverseConvex_le_of_polar_feasible {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hf_nonneg : ∀ x, 0 ≤ f x)
    {xStar : Fin n → ℝ} {μStar : EReal}
    (hμ : 0 ≤ μStar ∧
      ∀ y, ((y ⬝ᵥ xStar : ℝ) : EReal) ≤ (1 : EReal) + μStar * f y) :
    fenchelConjugate n (obverseConvex f) xStar ≤ μStar := by
  classical
  by_cases htop : μStar = ⊤
  · subst htop
    exact le_top
  cases hμ' : μStar using EReal.rec with
  | bot =>
      have h0le : (0 : EReal) ≤ (⊥ : EReal) := by simpa [hμ'] using hμ.1
      have hbotlt : (⊥ : EReal) < (0 : EReal) := by simp
      exact (False.elim (not_le_of_gt hbotlt h0le))
  | top =>
      exact (False.elim (htop hμ'))
  | coe μ =>
      have hμ_nonneg : (0 : EReal) ≤ (μ : EReal) := by
        simpa [hμ'] using hμ.1
      unfold fenchelConjugate
      refine sSup_le ?_
      rintro z ⟨x, rfl⟩
      have hlower :
          ((x ⬝ᵥ xStar : ℝ) : EReal) - (μ : EReal) ≤ obverseConvex f x := by
        unfold obverseConvex
        refine le_sInf ?_
        intro μ' hμ'
        rcases hμ' with ⟨t, ht, rfl, hle_t⟩
        have hμineq :
            ((t⁻¹ • x ⬝ᵥ xStar : ℝ) : EReal) ≤
              (1 : EReal) + (μ : EReal) * f ((t⁻¹) • x) := by
          simpa [hμ'] using hμ.2 ((t⁻¹) • x)
        have hmul :
            (t : EReal) * ((t⁻¹ • x ⬝ᵥ xStar : ℝ) : EReal) ≤
              (t : EReal) * ((1 : EReal) + (μ : EReal) * f ((t⁻¹) • x)) :=
          mul_le_mul_of_nonneg_left hμineq (by exact_mod_cast (le_of_lt ht))
        have hleft :
            (t : EReal) * ((t⁻¹ • x ⬝ᵥ xStar : ℝ) : EReal) =
              ((x ⬝ᵥ xStar : ℝ) : EReal) := by
          have hreal :
              (t : ℝ) * ((t⁻¹ • x ⬝ᵥ xStar : ℝ) : ℝ) = (x ⬝ᵥ xStar : ℝ) := by
            have hdot :
                ((t⁻¹ • x ⬝ᵥ xStar : ℝ) : ℝ) = (t⁻¹) * (x ⬝ᵥ xStar : ℝ) := by
              simp [smul_eq_mul, smul_dotProduct]
            calc
              (t : ℝ) * ((t⁻¹ • x ⬝ᵥ xStar : ℝ) : ℝ) =
                  (t : ℝ) * ((t⁻¹) * (x ⬝ᵥ xStar : ℝ)) := by
                    simp [hdot]
              _ = (t * t⁻¹) * (x ⬝ᵥ xStar : ℝ) := by ring
              _ = (x ⬝ᵥ xStar : ℝ) := by simp [ht.ne']
          have hreal' :
              ((t * ((t⁻¹ • x ⬝ᵥ xStar : ℝ) : ℝ) : ℝ) : EReal) =
                ((x ⬝ᵥ xStar : ℝ) : EReal) := by
            exact_mod_cast hreal
          simpa [EReal.coe_mul] using hreal'
        have hmul' :
            ((x ⬝ᵥ xStar : ℝ) : EReal) ≤
              (t : EReal) * ((1 : EReal) + (μ : EReal) * f ((t⁻¹) • x)) := by
          calc
            ((x ⬝ᵥ xStar : ℝ) : EReal) =
                (t : EReal) * ((t⁻¹ • x ⬝ᵥ xStar : ℝ) : EReal) := by
                  simpa using hleft.symm
            _ ≤ (t : EReal) * ((1 : EReal) + (μ : EReal) * f ((t⁻¹) • x)) := hmul
        have hfy_nonneg : (0 : EReal) ≤ f ((t⁻¹) • x) := hf_nonneg _
        have hfy_le : f ((t⁻¹) • x) ≤ (t⁻¹ : EReal) := by
          have h := (mul_le_one_iff_le_inv_pos (ht := ht) (a := f ((t⁻¹) • x)) hfy_nonneg)
          exact (h.mp hle_t)
        have hmul_f :
            (μ : EReal) * f ((t⁻¹) • x) ≤ (μ : EReal) * (t⁻¹ : EReal) := by
          exact mul_le_mul_of_nonneg_left hfy_le hμ_nonneg
        have hright_le :
            (t : EReal) * ((1 : EReal) + (μ : EReal) * f ((t⁻¹) • x)) ≤
              (t : EReal) * ((1 : EReal) + (μ : EReal) * (t⁻¹ : EReal)) := by
          have hle_add :
              (1 : EReal) + (μ : EReal) * f ((t⁻¹) • x) ≤
                (1 : EReal) + (μ : EReal) * (t⁻¹ : EReal) :=
            add_le_add_right hmul_f (1 : EReal)
          exact mul_le_mul_of_nonneg_left
            hle_add
            (by exact_mod_cast (le_of_lt ht))
        have hright :
            (t : EReal) * ((1 : EReal) + (μ : EReal) * (t⁻¹ : EReal)) =
              ((t + μ : ℝ) : EReal) := by
          have hreal :
              (t : ℝ) * (1 + μ * t⁻¹) = t + μ := by
            field_simp [ht.ne']
          have hreal' :
              ((t * (1 + μ * t⁻¹) : ℝ) : EReal) = ((t + μ : ℝ) : EReal) := by
            exact_mod_cast hreal
          simpa [EReal.coe_add, EReal.coe_mul] using hreal'
        have hle_add :
            ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ ((t + μ : ℝ) : EReal) :=
          le_trans hmul' (by simpa [hright] using hright_le)
        have hsub :
            ((x ⬝ᵥ xStar : ℝ) : EReal) - (μ : EReal) ≤ (t : EReal) := by
          have h1 : (μ : EReal) ≠ (⊥ : EReal) ∨ (t : EReal) ≠ (⊤ : EReal) := by
            exact Or.inl (by simp)
          have h2 : (μ : EReal) ≠ (⊤ : EReal) ∨ (t : EReal) ≠ (⊥ : EReal) := by
            exact Or.inr (by simp)
          have hle_add' :
              ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ (t : EReal) + (μ : EReal) := by
            simpa [EReal.coe_add, add_comm, add_left_comm, add_assoc] using hle_add
          exact (EReal.sub_le_iff_le_add h1 h2).2 hle_add'
        exact hsub
      have hfinal :
          ((x ⬝ᵥ xStar : ℝ) : EReal) - obverseConvex f x ≤ (μ : EReal) := by
        have h1 : (μ : EReal) ≠ (⊥ : EReal) ∨ obverseConvex f x ≠ (⊤ : EReal) := by
          exact Or.inl (by
            intro hbot
            have h0le : (0 : EReal) ≤ (⊥ : EReal) := by
              simp [hbot] at hμ_nonneg
            have hbotlt : (⊥ : EReal) < (0 : EReal) := by simp
            exact (not_le_of_gt hbotlt h0le))
        have h2 : (μ : EReal) ≠ (⊤ : EReal) ∨ obverseConvex f x ≠ (⊥ : EReal) := by
          exact Or.inl (by simp)
        have hle_add :
            ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ (μ : EReal) + obverseConvex f x := by
          have hle' :
              ((x ⬝ᵥ xStar : ℝ) : EReal) - (μ : EReal) ≤ obverseConvex f x := hlower
          have hle'' : ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ obverseConvex f x + (μ : EReal) :=
            (EReal.sub_le_iff_le_add h1 h2).1 hle'
          simpa [add_comm, add_left_comm, add_assoc] using hle''
        have h1' : obverseConvex f x ≠ (⊥ : EReal) ∨ (μ : EReal) ≠ (⊤ : EReal) := by
          exact Or.inl (by
            intro hbot
            have h0le : (0 : EReal) ≤ (⊥ : EReal) := by
              simpa [hbot] using (obverseConvex_nonneg f x)
            have hbotlt : (⊥ : EReal) < (0 : EReal) := by simp
            exact (not_le_of_gt hbotlt h0le))
        have h2' : obverseConvex f x ≠ (⊤ : EReal) ∨ (μ : EReal) ≠ (⊥ : EReal) := by
          exact Or.inr (by simp)
        exact (EReal.sub_le_iff_le_add h1' h2').2 (by
          simpa [add_comm, add_left_comm, add_assoc] using hle_add)
      simpa [hμ'] using hfinal

/-- Positive finite values of `f` yield a polar-feasible inner bound. -/
lemma inner_le_one_add_mul_of_fenchelConjugate_obverse_of_pos {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_closed : ClosedConvexFunction f) (hf0 : f 0 = 0)
    {xStar : Fin n → ℝ} {μ ε : ℝ}
    (hμ : fenchelConjugate n (obverseConvex f) xStar = (μ : EReal)) (hε : 0 < ε)
    {y : Fin n → ℝ} {r : ℝ} (hfy : f y = (r : EReal)) (hr : 0 < r) :
    ((y ⬝ᵥ xStar : ℝ) : EReal) ≤ (1 : EReal) + ((μ + ε : ℝ) : EReal) * f y := by
  classical
  let t : ℝ := r⁻¹
  have ht : 0 < t := inv_pos.mpr hr
  have hle : (t : EReal) * f y ≤ (1 : EReal) := by
    have htr : (t : EReal) * (r : EReal) = (1 : EReal) := by
      exact_mod_cast (by simp [t, hr.ne'])
    simpa [hfy] using (le_of_eq htr)
  have h_obv : obverseConvex f (t • y) ≤ (t : EReal) :=
    obverseConvex_smul_le_coe_of_mul_le_one (f := f) hf_nonneg hf_closed hf0 ht hle
  have hfenchel :
      ((t • y ⬝ᵥ xStar : ℝ) : EReal) ≤
        obverseConvex f (t • y) + fenchelConjugate n (obverseConvex f) xStar := by
    exact
      dotProduct_le_add_fenchelConjugate (f := obverseConvex f)
        (fun x => obverseConvex_nonneg f x)
        (obverseConvex_zero_of_nonneg_zero (f := f) hf0) (t • y) xStar
  have hdot :
      ((t • y ⬝ᵥ xStar : ℝ) : EReal) ≤ (t : EReal) + (μ : EReal) := by
    have h' :
        obverseConvex f (t • y) + fenchelConjugate n (obverseConvex f) xStar ≤
          (t : EReal) + (μ : EReal) := by
      simpa [hμ, add_comm, add_left_comm, add_assoc] using
        (add_le_add_right h_obv (fenchelConjugate n (obverseConvex f) xStar))
    exact le_trans hfenchel h'
  have hdot' :
      ((t * (y ⬝ᵥ xStar : ℝ) : ℝ) : EReal) ≤ ((t + μ : ℝ) : EReal) := by
    simpa [smul_eq_mul, smul_dotProduct, EReal.coe_add, EReal.coe_mul] using hdot
  have hdot_real : t * (y ⬝ᵥ xStar : ℝ) ≤ t + μ :=
    (EReal.coe_le_coe_iff).1 hdot'
  have hmul :
      r * (t * (y ⬝ᵥ xStar : ℝ)) ≤ r * (t + μ) :=
    mul_le_mul_of_nonneg_left hdot_real (le_of_lt hr)
  have hleft : r * (t * (y ⬝ᵥ xStar : ℝ)) = (y ⬝ᵥ xStar : ℝ) := by
    have hrt : r * t = 1 := by
      simp [t, hr.ne']
    calc
      r * (t * (y ⬝ᵥ xStar : ℝ)) = (r * t) * (y ⬝ᵥ xStar : ℝ) := by ring
      _ = (y ⬝ᵥ xStar : ℝ) := by simp [hrt]
  have hright : r * (t + μ) = 1 + μ * r := by
    calc
      r * (t + μ) = r * t + r * μ := by ring
      _ = 1 + μ * r := by
        simp [t, hr.ne', mul_comm]
  have hdot_real' : (y ⬝ᵥ xStar : ℝ) ≤ 1 + μ * r := by
    simpa [hleft, hright] using hmul
  have hineqE' :
      ((y ⬝ᵥ xStar : ℝ) : EReal) ≤ ((1 + μ * r : ℝ) : EReal) := by
    exact_mod_cast hdot_real'
  have hineqE :
      ((y ⬝ᵥ xStar : ℝ) : EReal) ≤ (1 : EReal) + (μ : EReal) * f y := by
    simpa [hfy, EReal.coe_add, EReal.coe_mul, mul_comm, mul_left_comm, mul_assoc] using hineqE'
  have hμle : (μ : EReal) ≤ ((μ + ε : ℝ) : EReal) := by
    exact_mod_cast (by linarith)
  have hmul' : (μ : EReal) * f y ≤ ((μ + ε : ℝ) : EReal) * f y := by
    have hmul'' : f y * (μ : EReal) ≤ f y * ((μ + ε : ℝ) : EReal) :=
      mul_le_mul_of_nonneg_left hμle (hf_nonneg y)
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul''
  have hineqE'' :
      ((y ⬝ᵥ xStar : ℝ) : EReal) ≤ (1 : EReal) + ((μ + ε : ℝ) : EReal) * f y := by
    have h := add_le_add_left hmul' (1 : EReal)
    exact le_trans hineqE (by
      simpa [add_comm, add_left_comm, add_assoc] using h)
  exact hineqE''

/-- A zero value of `f` forces the inner product to be at most one. -/
lemma inner_le_one_of_f_eq_zero_of_fenchelConjugate_obverse_finite {n : ℕ}
    {f : (Fin n → ℝ) → EReal} (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_closed : ClosedConvexFunction f) (hf0 : f 0 = 0)
    {xStar : Fin n → ℝ} {μ : ℝ}
    (hμ : fenchelConjugate n (obverseConvex f) xStar = (μ : EReal))
    {y : Fin n → ℝ} (hfy : f y = (0 : EReal)) :
    ((y ⬝ᵥ xStar : ℝ) : EReal) ≤ (1 : EReal) := by
  classical
  by_contra hle
  have hlt : (1 : EReal) < ((y ⬝ᵥ xStar : ℝ) : EReal) := lt_of_not_ge hle
  have hlt_real : (1 : ℝ) < (y ⬝ᵥ xStar : ℝ) := (EReal.coe_lt_coe_iff).1 hlt
  have hμ_nonneg : (0 : EReal) ≤ (μ : EReal) := by
    have h :=
      fenchelConjugate_nonneg_of_nonneg_zero (f := obverseConvex f)
        (obverseConvex_zero_of_nonneg_zero (f := f) hf0) xStar
    simpa [hμ] using h
  have hμ_nonneg_real : 0 ≤ μ := (EReal.coe_le_coe_iff).1 hμ_nonneg
  set a : ℝ := (y ⬝ᵥ xStar : ℝ) - 1 with ha_def
  have ha_pos : 0 < a := by linarith
  set t : ℝ := (μ + 1) / a with ht_def
  have ht : 0 < t := by
    have hpos : 0 < μ + 1 := by linarith
    exact div_pos hpos ha_pos
  have hle' : (t : EReal) * f y ≤ (1 : EReal) := by
    simp [hfy]
  have h_obv : obverseConvex f (t • y) ≤ (t : EReal) :=
    obverseConvex_smul_le_coe_of_mul_le_one (f := f) hf_nonneg hf_closed hf0 ht hle'
  have hfenchel :
      ((t • y ⬝ᵥ xStar : ℝ) : EReal) ≤
        obverseConvex f (t • y) + fenchelConjugate n (obverseConvex f) xStar := by
    exact
      dotProduct_le_add_fenchelConjugate (f := obverseConvex f)
        (fun x => obverseConvex_nonneg f x)
        (obverseConvex_zero_of_nonneg_zero (f := f) hf0) (t • y) xStar
  have hdot :
      ((t • y ⬝ᵥ xStar : ℝ) : EReal) ≤ (t : EReal) + (μ : EReal) := by
    have h' :
        obverseConvex f (t • y) + fenchelConjugate n (obverseConvex f) xStar ≤
          (t : EReal) + (μ : EReal) := by
      simpa [hμ, add_comm, add_left_comm, add_assoc] using
        (add_le_add_right h_obv (fenchelConjugate n (obverseConvex f) xStar))
    exact le_trans hfenchel h'
  have hdot' :
      ((t * (y ⬝ᵥ xStar : ℝ) : ℝ) : EReal) ≤ ((t + μ : ℝ) : EReal) := by
    simpa [smul_eq_mul, smul_dotProduct, EReal.coe_add, EReal.coe_mul] using hdot
  have hdot_real : t * (y ⬝ᵥ xStar : ℝ) ≤ t + μ :=
    (EReal.coe_le_coe_iff).1 hdot'
  have hdot_real' : t * a ≤ μ := by
    have htmp : t * (y ⬝ᵥ xStar : ℝ) - t ≤ μ := by linarith
    simpa [ha_def, mul_sub, mul_one] using htmp
  have ht_mul : t * a = μ + 1 := by
    have ha_ne : a ≠ 0 := ne_of_gt ha_pos
    calc
      t * a = ((μ + 1) / a) * a := by simp [t]
      _ = (μ + 1) * a / a := by
        simpa using (div_mul_eq_mul_div (μ + 1) a a)
      _ = μ + 1 := by
        simpa using (mul_div_cancel_right₀ (μ + 1) ha_ne)
  have hcontr : μ + 1 ≤ μ := by
    simpa [ht_mul] using hdot_real'
  linarith

/-- The Fenchel conjugate value yields a polar-feasible bound with `μ + ε`. -/
lemma polar_feasible_of_fenchelConjugate_obverse_add_pos {n : ℕ}
    {f : (Fin n → ℝ) → EReal} (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_closed : ClosedConvexFunction f) (hf0 : f 0 = 0)
    {xStar : Fin n → ℝ} {μ ε : ℝ}
    (hμ : fenchelConjugate n (obverseConvex f) xStar = (μ : EReal)) (hε : 0 < ε) :
    0 ≤ ((μ + ε : ℝ) : EReal) ∧
      ∀ y, ((y ⬝ᵥ xStar : ℝ) : EReal) ≤ (1 : EReal) + ((μ + ε : ℝ) : EReal) * f y := by
  have hμ_nonneg : (0 : EReal) ≤ (μ : EReal) := by
    have h :=
      fenchelConjugate_nonneg_of_nonneg_zero (f := obverseConvex f)
        (obverseConvex_zero_of_nonneg_zero (f := f) hf0) xStar
    simpa [hμ] using h
  have hμ_nonneg_real : 0 ≤ μ := (EReal.coe_le_coe_iff).1 hμ_nonneg
  have hμeps_nonneg : (0 : EReal) ≤ ((μ + ε : ℝ) : EReal) := by
    exact_mod_cast (by linarith)
  refine ⟨hμeps_nonneg, ?_⟩
  intro y
  cases hfy : f y using EReal.rec with
  | bot =>
      have h0le : (0 : EReal) ≤ (⊥ : EReal) := by
        simpa [hfy] using hf_nonneg y
      have hbotlt : (⊥ : EReal) < (0 : EReal) := by simp
      exact (False.elim (not_le_of_gt hbotlt h0le))
  | top =>
      have hpos : 0 < μ + ε := by linarith
      have htop : ((μ + ε : ℝ) : EReal) * (⊤ : EReal) = (⊤ : EReal) := by
        simpa using (EReal.coe_mul_top_of_pos hpos)
      have htop' :
          ((μ : EReal) + (ε : EReal)) * (⊤ : EReal) = (⊤ : EReal) := by
        simpa [EReal.coe_add] using htop
      have hright :
          (1 : EReal) + ((μ : EReal) + (ε : EReal)) * (⊤ : EReal) = (⊤ : EReal) := by
        calc
          (1 : EReal) + ((μ : EReal) + (ε : EReal)) * (⊤ : EReal) = (1 : EReal) + ⊤ := by
            simp [htop']
          _ = ⊤ + (1 : EReal) := by
            simp [add_comm]
          _ = (⊤ : EReal) := by
            have hne : (1 : EReal) ≠ (⊥ : EReal) := by
              exact EReal.coe_ne_bot (1 : ℝ)
            exact EReal.top_add_of_ne_bot hne
      simp [hright]
  | coe r =>
      by_cases hr0 : r = 0
      · have hinner :
            ((y ⬝ᵥ xStar : ℝ) : EReal) ≤ (1 : EReal) := by
          apply
            inner_le_one_of_f_eq_zero_of_fenchelConjugate_obverse_finite (f := f)
              hf_nonneg hf_closed hf0 (xStar := xStar) (μ := μ) hμ
          simpa [hr0] using hfy
        simpa [hfy, hr0] using hinner
      · have hr0E : (0 : EReal) ≤ (r : EReal) := by
          simpa [hfy] using hf_nonneg y
        have hr0' : 0 ≤ r := (EReal.coe_le_coe_iff).1 hr0E
        have hrpos : 0 < r := lt_of_le_of_ne hr0' (Ne.symm hr0)
        have hinner :
            ((y ⬝ᵥ xStar : ℝ) : EReal) ≤
              (1 : EReal) + ((μ + ε : ℝ) : EReal) * f y :=
          inner_le_one_add_mul_of_fenchelConjugate_obverse_of_pos (f := f)
            hf_nonneg hf_closed hf0 (xStar := xStar) (μ := μ) (ε := ε) hμ hε
            (y := y) (r := r) hfy hrpos
        simpa [hfy] using hinner

/-- The polar is bounded above by the Fenchel conjugate of the obverse. -/
lemma polarConvex_le_fenchelConjugate_obverseConvex {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_closed : ClosedConvexFunction f) (hf0 : f 0 = 0)
    (xStar : Fin n → ℝ) :
    polarConvex f xStar ≤ fenchelConjugate n (obverseConvex f) xStar := by
  classical
  by_cases htop : fenchelConjugate n (obverseConvex f) xStar = ⊤
  · simp [htop]
  · cases hμ : fenchelConjugate n (obverseConvex f) xStar using EReal.rec with
    | bot =>
        have h0le :
            (0 : EReal) ≤ fenchelConjugate n (obverseConvex f) xStar := by
          exact
            fenchelConjugate_nonneg_of_nonneg_zero (f := obverseConvex f)
              (obverseConvex_zero_of_nonneg_zero (f := f) hf0) xStar
        have h0le' : (0 : EReal) ≤ (⊥ : EReal) := by
          simp [hμ] at h0le
        have hbotlt : (⊥ : EReal) < (0 : EReal) := by simp
        exact (False.elim (not_le_of_gt hbotlt h0le'))
    | top =>
        exact (False.elim (htop hμ))
    | coe μ =>
        have hle_pos :
            ∀ ε : ℝ, 0 < ε → polarConvex f xStar ≤ ((μ + ε : ℝ) : EReal) := by
          intro ε hε
          have hfeasible :
              0 ≤ ((μ + ε : ℝ) : EReal) ∧
                ∀ y, ((y ⬝ᵥ xStar : ℝ) : EReal) ≤
                  (1 : EReal) + ((μ + ε : ℝ) : EReal) * f y :=
            polar_feasible_of_fenchelConjugate_obverse_add_pos (f := f) hf_nonneg hf_closed hf0
              (xStar := xStar) (μ := μ) (ε := ε) (by simp [hμ]) hε
          have hmem :
              ((μ + ε : ℝ) : EReal) ∈
                {μStar : EReal |
                  0 ≤ μStar ∧
                    ∀ y, ((y ⬝ᵥ xStar : ℝ) : EReal) ≤ (1 : EReal) + μStar * f y} :=
            hfeasible
          unfold polarConvex
          exact sInf_le hmem
        have hleμ : polarConvex f xStar ≤ (μ : EReal) := by
          by_cases htop' : polarConvex f xStar = ⊤
          · have h := hle_pos 1 (by norm_num)
            have htop_le : (⊤ : EReal) ≤ ((μ + 1 : ℝ) : EReal) := by
              simpa [htop'] using h
            exact (False.elim (not_top_le_coe (μ + 1) htop_le))
          · cases hpolar : polarConvex f xStar using EReal.rec with
            | bot =>
                have h0le : (0 : EReal) ≤ polarConvex f xStar :=
                  polarConvex_nonneg f xStar
                have h0le' : (0 : EReal) ≤ (⊥ : EReal) := by
                  simp [hpolar] at h0le
                have hbotlt : (⊥ : EReal) < (0 : EReal) := by simp
                exact (False.elim (not_le_of_gt hbotlt h0le'))
            | top =>
                exact (False.elim (htop' hpolar))
            | coe r =>
                have hle_r : ∀ ε : ℝ, 0 < ε → r ≤ μ + ε := by
                  intro ε hε
                  have hle' : (r : EReal) ≤ ((μ + ε : ℝ) : EReal) := by
                    simpa [hpolar] using hle_pos ε hε
                  exact (EReal.coe_le_coe_iff).1 hle'
                have hle_rμ : r ≤ μ := by
                  refine le_of_forall_pos_le_add ?_
                  intro ε hε
                  simpa [add_comm, add_left_comm, add_assoc] using (hle_r ε hε)
                simpa [hpolar] using (EReal.coe_le_coe_iff).2 hle_rμ
        simpa [hμ] using hleμ

/-- The Fenchel conjugate of the obverse is the polar (core symmetry). -/
lemma fenchelConjugate_obverseConvex_eq_polarConvex {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_closed : ClosedConvexFunction f) (hf0 : f 0 = 0) :
    fenchelConjugate n (obverseConvex f) = polarConvex f := by
  classical
  funext xStar
  apply le_antisymm
  · refine le_sInf ?_
    intro μStar hμStar
    exact
      fenchelConjugate_obverseConvex_le_of_polar_feasible (f := f) hf_nonneg
        (xStar := xStar) hμStar
  · exact polarConvex_le_fenchelConjugate_obverseConvex (f := f) hf_nonneg hf_closed hf0 xStar

/-- The obverse of the Fenchel conjugate is the polar. -/
lemma obverseConvex_fenchelConjugate_eq_polarConvex {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_closed : ClosedConvexFunction f) (hf0 : f 0 = 0) :
    obverseConvex (fenchelConjugate n f) = polarConvex f := by
  have hStar_nonneg : ∀ x, 0 ≤ fenchelConjugate n f x :=
    fenchelConjugate_nonneg_of_nonneg_zero f hf0
  have hStar_closed : ClosedConvexFunction (fenchelConjugate n f) := by
    have h := fenchelConjugate_closedConvex (n := n) (f := f)
    exact ⟨h.2, h.1⟩
  have hStar0 : fenchelConjugate n f 0 = 0 :=
    fenchelConjugate_zero_eq_zero_of_nonneg_zero (f := f) hf_nonneg hf0
  have h_obv :
      obverseConvex (fenchelConjugate n f) =
        polarConvex (fenchelConjugate n (fenchelConjugate n f)) :=
    obverseConvex_eq_polarConvex_fenchelConjugate (f := fenchelConjugate n f)
      hStar_nonneg hStar_closed hStar0
  have hbiconj :=
    fenchelConjugate_biconjugate_eq_of_nonneg_closedConvex_zero (f := f) hf_nonneg hf_closed hf0
  simpa [hbiconj] using h_obv

/-- Theorem 15.5: Let `f` be a nonnegative closed convex function with `f(0)=0`, and let `g` be the
obverse of `f`.

Then `g` is also a nonnegative closed convex function with `g(0)=0`, and `f` is the obverse of
`g`. Moreover,

`f^∘ = g^*` and `f^* = g^∘`,

and `f^∘` and `f^*` are obverses of each other. In this development, the obverse is
`obverseConvex`, the polar is `polarConvex`, and the Fenchel conjugate is `fenchelConjugate n ·`. -/
theorem obverseConvex_nonneg_closedConvex_zero_and_polar_eq_conjugate {n : ℕ}
    {f g : (Fin n → ℝ) → EReal} (hf_nonneg : ∀ x, 0 ≤ f x) (hf_closed : ClosedConvexFunction f)
    (hf0 : f 0 = 0) (hg : g = obverseConvex f) :
    (∀ x, 0 ≤ g x) ∧
      ClosedConvexFunction g ∧
        g 0 = 0 ∧
          obverseConvex g = f ∧
            polarConvex f = fenchelConjugate n g ∧
              fenchelConjugate n f = polarConvex g ∧
    obverseConvex (polarConvex f) = fenchelConjugate n f ∧
      obverseConvex (fenchelConjugate n f) = polarConvex f := by
  classical
  subst hg
  let fStar : (Fin n → ℝ) → EReal := fenchelConjugate n f
  have hStar_nonneg : ∀ x, 0 ≤ fStar x := fenchelConjugate_nonneg_of_nonneg_zero f hf0
  have hStar_closed : ClosedConvexFunction fStar := by
    have h := fenchelConjugate_closedConvex (n := n) (f := f)
    exact ⟨h.2, h.1⟩
  have hStar0 : fStar 0 = 0 :=
    fenchelConjugate_zero_eq_zero_of_nonneg_zero (f := f) hf_nonneg hf0
  have h_g_props :=
    polarConvex_mem_subtype_nonneg_closedConvex_zero (n := n)
      (⟨fStar, ⟨hStar_nonneg, hStar_closed, hStar0⟩⟩ :
        {g : (Fin n → ℝ) → EReal //
          (∀ x, 0 ≤ g x) ∧ ClosedConvexFunction g ∧ g 0 = 0})
  have h_obv_eq :
      obverseConvex f = polarConvex fStar :=
    obverseConvex_eq_polarConvex_fenchelConjugate (f := f) hf_nonneg hf_closed hf0
  have h_g_nonneg : ∀ x, 0 ≤ obverseConvex f x := by
    simpa [h_obv_eq] using h_g_props.1
  have h_g_closed : ClosedConvexFunction (obverseConvex f) := by
    simpa [h_obv_eq] using h_g_props.2.1
  have h_g0 : obverseConvex f 0 = 0 := by
    simpa [h_obv_eq] using h_g_props.2.2
  have h_polar_g :
      polarConvex (obverseConvex f) = fenchelConjugate n f :=
    polarConvex_obverseConvex_eq_fenchelConjugate (f := f) hf_nonneg hf_closed hf0
  have h_conj_g :
      fenchelConjugate n (obverseConvex f) = polarConvex f :=
    fenchelConjugate_obverseConvex_eq_polarConvex (f := f) hf_nonneg hf_closed hf0
  have h_invol_f :=
    polarConvex_involutive_on_subtype (n := n)
      (⟨f, ⟨hf_nonneg, hf_closed, hf0⟩⟩ :
        {g : (Fin n → ℝ) → EReal //
          (∀ x, 0 ≤ g x) ∧ ClosedConvexFunction g ∧ g 0 = 0})
  have h_obv_obv : obverseConvex (obverseConvex f) = f := by
    have h_obv_obv' :
        obverseConvex (obverseConvex f) =
          polarConvex (fenchelConjugate n (obverseConvex f)) :=
      obverseConvex_eq_polarConvex_fenchelConjugate (f := obverseConvex f)
        h_g_nonneg h_g_closed h_g0
    calc
      obverseConvex (obverseConvex f) =
          polarConvex (fenchelConjugate n (obverseConvex f)) := h_obv_obv'
      _ = polarConvex (polarConvex f) := by simp [h_conj_g]
      _ = f := by simpa using h_invol_f
  have h_obv_fStar :
      obverseConvex (fenchelConjugate n f) = polarConvex f :=
    obverseConvex_fenchelConjugate_eq_polarConvex (f := f) hf_nonneg hf_closed hf0
  have h_obv_polar : obverseConvex (polarConvex f) = fenchelConjugate n f := by
    have h_obv_conj_g :
        obverseConvex (fenchelConjugate n (obverseConvex f)) =
          polarConvex (obverseConvex f) :=
      obverseConvex_fenchelConjugate_eq_polarConvex (f := obverseConvex f)
        h_g_nonneg h_g_closed h_g0
    simpa [h_conj_g, h_polar_g] using h_obv_conj_g
  refine ⟨h_g_nonneg, h_g_closed, h_g0, ?_, ?_, ?_, h_obv_polar, h_obv_fStar⟩
  · simpa using h_obv_obv
  · simpa using h_conj_g.symm
  · simpa using h_polar_g.symm

/-- Corollary 15.5.1: If `f` is a nonnegative closed convex function on `ℝⁿ` with `f(0)=0`, then
`f^{∘*} = f^{*∘}`; i.e. the Fenchel conjugate of the polar equals the polar of the Fenchel
conjugate.

In this development, `fᵒ` is `polarConvex f` and `f*` is `fenchelConjugate n f`. -/
theorem fenchelConjugate_polarConvex_eq_polarConvex_fenchelConjugate {n : ℕ}
    {f : (Fin n → ℝ) → EReal} (hf_nonneg : ∀ x, 0 ≤ f x) (hf_closed : ClosedConvexFunction f)
    (hf0 : f 0 = 0) :
    fenchelConjugate n (polarConvex f) = polarConvex (fenchelConjugate n f) := by
  let g : (Fin n → ℝ) → EReal := obverseConvex f
  rcases
      obverseConvex_nonneg_closedConvex_zero_and_polar_eq_conjugate (n := n) (f := f) (g := g)
        hf_nonneg hf_closed hf0 rfl with
    ⟨hg_nonneg, hg_closed, hg0, -, h_polar, h_star, -, -⟩
  have h_biconj : fenchelConjugate n (polarConvex f) = g := by
    have hbiconj :=
      fenchelConjugate_biconjugate_eq_of_nonneg_closedConvex_zero (n := n) (f := g) hg_nonneg
        hg_closed hg0
    calc
      fenchelConjugate n (polarConvex f) =
          fenchelConjugate n (fenchelConjugate n g) := by
            simp [h_polar]
      _ = g := by simpa using hbiconj
  have h_bipolar : polarConvex (fenchelConjugate n f) = g := by
    have h_invol :=
      polarConvex_involutive_on_subtype (n := n)
        (⟨g, ⟨hg_nonneg, hg_closed, hg0⟩⟩ :
          {f : (Fin n → ℝ) → EReal //
            (∀ x, 0 ≤ f x) ∧ ClosedConvexFunction f ∧ f 0 = 0})
    calc
      polarConvex (fenchelConjugate n f) = polarConvex (polarConvex g) := by
        simp [h_star]
      _ = g := by simpa using h_invol
  calc
    fenchelConjugate n (polarConvex f) = g := h_biconj
    _ = polarConvex (fenchelConjugate n f) := by
      simpa using h_bipolar.symm

/-- Obverse sublevel inequality is equivalent to a reciprocal bound on `f`. -/
lemma obverseConvex_le_coe_pos_iff_f_le_inv {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_closed : ClosedConvexFunction f) (hf0 : f 0 = 0)
    {x : Fin n → ℝ} {α : ℝ} (hα : 0 < α) :
    obverseConvex f x ≤ (α : EReal) ↔ f ((α⁻¹) • x) ≤ ((α⁻¹ : ℝ) : EReal) := by
  have hiff :=
    (obverseConvex_le_coe_pos_iff_perspective_le_one (f := f) hf_nonneg hf_closed hf0
      (x := x) (lam := α) hα)
  have hnonneg : (0 : EReal) ≤ f ((α⁻¹) • x) := hf_nonneg _
  have hmul :=
    (mul_le_one_iff_le_inv_pos (t := α) (a := f ((α⁻¹) • x)) hα hnonneg)
  exact hiff.trans hmul

/-- Text 15.0.36: Let `f` be as in Theorem 15.5 and let `g` be its obverse. For `α > 0`,
`{x | g x ≤ α} = α • {x | f x ≤ α⁻¹}`. In particular, the sublevel sets of `g` are homothetic to
those of `f` with reciprocal levels. -/
theorem sublevelSet_obverseConvex_eq_smul_sublevelSet {n : ℕ} {f g : (Fin n → ℝ) → EReal}
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_closed : ClosedConvexFunction f) (hf0 : f 0 = 0)
    (hg : g = obverseConvex f) {α : ℝ} (hα : 0 < α) :
    {x | g x ≤ (α : EReal)} = α • {x | f x ≤ ((α⁻¹ : ℝ) : EReal)} := by
  classical
  subst hg
  ext x
  constructor
  · intro hx
    have hx' :
        f ((α⁻¹) • x) ≤ ((α⁻¹ : ℝ) : EReal) :=
      (obverseConvex_le_coe_pos_iff_f_le_inv (f := f) hf_nonneg hf_closed hf0 (x := x) hα).1
        hx
    have hx'' : (α⁻¹) • x ∈ {x | f x ≤ ((α⁻¹ : ℝ) : EReal)} := by
      simpa using hx'
    have hαne : (α : ℝ) ≠ 0 := ne_of_gt hα
    exact
      (Set.mem_smul_set_iff_inv_smul_mem₀ (ha := hαne) {x | f x ≤ ((α⁻¹ : ℝ) : EReal)} x).2
        hx''
  · intro hx
    have hαne : (α : ℝ) ≠ 0 := ne_of_gt hα
    have hx' :
        (α⁻¹) • x ∈ {x | f x ≤ ((α⁻¹ : ℝ) : EReal)} :=
      (Set.mem_smul_set_iff_inv_smul_mem₀ (ha := hαne) {x | f x ≤ ((α⁻¹ : ℝ) : EReal)} x).1
        hx
    have hx'' : f ((α⁻¹) • x) ≤ ((α⁻¹ : ℝ) : EReal) := by
      simpa using hx'
    exact
      (obverseConvex_le_coe_pos_iff_f_le_inv (f := f) hf_nonneg hf_closed hf0 (x := x) hα).2
        hx''

/-- Text 15.0.36: Since `polarConvex f` is the obverse of `fenchelConjugate n f` (Theorem 15.5),
for every `α > 0`,
`{x⋆ | polarConvex f x⋆ ≤ α⁻¹} = α⁻¹ • {x⋆ | fenchelConjugate n f x⋆ ≤ α}`. The set on the left is
the “middle” set appearing in Theorem 14.7. -/
theorem sublevelSet_polarConvex_le_inv_eq_inv_smul_sublevelSet_fenchelConjugate {n : ℕ}
    {f : (Fin n → ℝ) → EReal} (hf_nonneg : ∀ x, 0 ≤ f x) (hf_closed : ClosedConvexFunction f)
    (hf0 : f 0 = 0) {α : ℝ} (hα : 0 < α) :
    {xStar | polarConvex f xStar ≤ ((α⁻¹ : ℝ) : EReal)} =
      (α⁻¹) • {xStar | fenchelConjugate n f xStar ≤ (α : EReal)} := by
  have hStar_nonneg : ∀ x, 0 ≤ fenchelConjugate n f x :=
    fenchelConjugate_nonneg_of_nonneg_zero f hf0
  have hStar_closed : ClosedConvexFunction (fenchelConjugate n f) := by
    have h := fenchelConjugate_closedConvex (n := n) (f := f)
    exact ⟨h.2, h.1⟩
  have hStar0 : fenchelConjugate n f 0 = 0 :=
    fenchelConjugate_zero_eq_zero_of_nonneg_zero (f := f) hf_nonneg hf0
  have h_obv :
      polarConvex f = obverseConvex (fenchelConjugate n f) := by
    simpa using
      (obverseConvex_fenchelConjugate_eq_polarConvex (f := f) hf_nonneg hf_closed hf0).symm
  have hαinv : 0 < (α⁻¹) := inv_pos.2 hα
  simpa [inv_inv] using
    (sublevelSet_obverseConvex_eq_smul_sublevelSet (n := n) (f := fenchelConjugate n f)
      (g := polarConvex f) hStar_nonneg hStar_closed hStar0 h_obv (α := α⁻¹) hαinv)

/-- Normalize a dilation inequality in `EReal` to a `≤ 1` form. -/
lemma dilation_le_iff_scaled_le_one {lam mu : ℝ} (hmu : 0 < mu) (A : EReal) :
    ((lam : EReal) * A ≤ (mu : EReal)) ↔
      (((lam / mu) : ℝ) : EReal) * A ≤ (1 : EReal) := by
  have hmu0 : (mu : ℝ) ≠ 0 := ne_of_gt hmu
  have hmu_inv_nonneg : (0 : EReal) ≤ ((mu⁻¹ : ℝ) : EReal) := by
    exact_mod_cast (le_of_lt (inv_pos.2 hmu))
  have hmu_nonneg : (0 : EReal) ≤ (mu : EReal) := by
    exact_mod_cast (le_of_lt hmu)
  have hmu_inv_mul : ((mu⁻¹ : ℝ) : EReal) * ((mu : ℝ) : EReal) = (1 : EReal) := by
    have hmu_mul_inv :
        ((mu : ℝ) : EReal) * ((mu⁻¹ : ℝ) : EReal) = (1 : EReal) := by
      calc
        ((mu : ℝ) : EReal) * ((mu⁻¹ : ℝ) : EReal) = ((mu * mu⁻¹ : ℝ) : EReal) := by
          simp [← EReal.coe_mul]
        _ = (1 : EReal) := by
          simp [hmu0]
    simpa [mul_comm] using hmu_mul_inv
  have hcoeff : ((mu : ℝ) : EReal) * (((lam / mu) : ℝ) : EReal) = (lam : EReal) := by
    calc
      ((mu : ℝ) : EReal) * (((lam / mu) : ℝ) : EReal) =
          ((mu * (lam / mu) : ℝ) : EReal) := by
        simp [← EReal.coe_mul]
      _ = (lam : EReal) := by
        simp [div_eq_mul_inv, hmu0, mul_left_comm]
  constructor
  · intro h
    have hmul := mul_le_mul_of_nonneg_left h hmu_inv_nonneg
    simpa
        [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, ← EReal.coe_mul, hmu0, hmu_inv_mul]
      using hmul
  · intro h
    have hmul := mul_le_mul_of_nonneg_left h hmu_nonneg
    simpa [hcoeff, mul_assoc, mul_left_comm, mul_comm] using hmul

/-- Divide a dilated obverse inequality by a positive scalar. -/
lemma obverse_dilation_le_iff_obverse_le_div {n : ℕ} {f : (Fin n → ℝ) → EReal}
    {x : Fin n → ℝ} {lam mu : ℝ} (hmu : 0 < mu) :
    ((mu : EReal) * obverseConvex f ((mu⁻¹) • x) ≤ (lam : EReal)) ↔
      obverseConvex f ((mu⁻¹) • x) ≤ (((lam / mu) : ℝ) : EReal) := by
  have hmu0 : (mu : ℝ) ≠ 0 := ne_of_gt hmu
  have hmu_inv_nonneg : (0 : EReal) ≤ ((mu⁻¹ : ℝ) : EReal) := by
    exact_mod_cast (le_of_lt (inv_pos.2 hmu))
  have hmu_nonneg : (0 : EReal) ≤ (mu : EReal) := by
    exact_mod_cast (le_of_lt hmu)
  have hmu_inv_mul : ((mu⁻¹ : ℝ) : EReal) * ((mu : ℝ) : EReal) = (1 : EReal) := by
    have hmu_mul_inv :
        ((mu : ℝ) : EReal) * ((mu⁻¹ : ℝ) : EReal) = (1 : EReal) := by
      calc
        ((mu : ℝ) : EReal) * ((mu⁻¹ : ℝ) : EReal) = ((mu * mu⁻¹ : ℝ) : EReal) := by
          simp [← EReal.coe_mul]
        _ = (1 : EReal) := by
          simp [hmu0]
    simpa [mul_comm] using hmu_mul_inv
  have hcoeff : ((mu : ℝ) : EReal) * (((lam / mu) : ℝ) : EReal) = (lam : EReal) := by
    calc
      ((mu : ℝ) : EReal) * (((lam / mu) : ℝ) : EReal) =
          ((mu * (lam / mu) : ℝ) : EReal) := by
        simp [← EReal.coe_mul]
      _ = (lam : EReal) := by
        simp [div_eq_mul_inv, hmu0, mul_left_comm]
  constructor
  · intro h
    have hmul := mul_le_mul_of_nonneg_left h hmu_inv_nonneg
    have hmul' :
        ((mu⁻¹ : ℝ) : EReal) * ((mu : ℝ) : EReal) *
            obverseConvex f ((mu⁻¹) • x) ≤
          ((mu⁻¹ : ℝ) : EReal) * (lam : EReal) := by
      simpa [← mul_assoc] using hmul
    simpa [hmu_inv_mul, div_eq_mul_inv, mul_left_comm, mul_comm, ← EReal.coe_mul] using hmul'
  · intro h
    have hmul := mul_le_mul_of_nonneg_left h hmu_nonneg
    simpa [hcoeff, mul_assoc, mul_left_comm, mul_comm] using hmul

/-- Combine reciprocal scalings in a nested `smul`. -/
lemma inv_div_inv_smul_smul_eq_inv_smul {n : ℕ} {x : Fin n → ℝ} {lam mu : ℝ}
    (hmu : 0 < mu) :
    (((lam / mu)⁻¹ : ℝ) • ((mu⁻¹) • x)) = (lam⁻¹) • x := by
  have hmu0 : (mu : ℝ) ≠ 0 := ne_of_gt hmu
  have hcoeff : ((mu / lam) : ℝ) * mu⁻¹ = lam⁻¹ := by
    calc
      ((mu / lam) : ℝ) * mu⁻¹ = (mu * lam⁻¹) * mu⁻¹ := by
        simp [div_eq_mul_inv]
      _ = (mu * lam⁻¹) * mu⁻¹ := by
        rfl
      _ = lam⁻¹ * (mu * mu⁻¹) := by
        ac_rfl
      _ = lam⁻¹ := by
        simp [hmu0]
  calc
    (((lam / mu)⁻¹ : ℝ) • ((mu⁻¹) • x)) =
        ((mu / lam : ℝ) • ((mu⁻¹) • x)) := by
          simp [inv_div]
    _ = (((mu / lam) : ℝ) * mu⁻¹) • x := by
          simp [smul_smul]
    _ = (lam⁻¹) • x := by
          simp [hcoeff]

/-- Text 15.0.37: For the obverse `g` of `f`, one has `(f_λ)(x) ≤ μ` if and only if `(g_μ)(x) ≤ λ`,
assuming `λ > 0` and `μ > 0`.

Here `f_λ x := λ * f (λ⁻¹ • x)` and `g_μ x := μ * g (μ⁻¹ • x)`. -/
lemma dilation_le_iff_obverse_dilation_le {n : ℕ} {f g : (Fin n → ℝ) → EReal}
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_closed : ClosedConvexFunction f) (hf0 : f 0 = 0)
    (hg : g = obverseConvex f) (x : Fin n → ℝ) {lam mu : ℝ} (hlam : 0 < lam) (hmu : 0 < mu) :
    ((lam : EReal) * f ((lam⁻¹) • x) ≤ (mu : EReal)) ↔
      ((mu : EReal) * g ((mu⁻¹) • x) ≤ (lam : EReal)) := by
  classical
  subst hg
  have ht : 0 < lam / mu := div_pos hlam hmu
  have hscale :
      ((lam : EReal) * f ((lam⁻¹) • x) ≤ (mu : EReal)) ↔
        (((lam / mu) : ℝ) : EReal) * f ((lam⁻¹) • x) ≤ (1 : EReal) :=
    dilation_le_iff_scaled_le_one (lam := lam) (mu := mu) hmu (A := f ((lam⁻¹) • x))
  have hobv :
      obverseConvex f ((mu⁻¹) • x) ≤ (((lam / mu) : ℝ) : EReal) ↔
        (((lam / mu) : ℝ) : EReal) *
            f ((((lam / mu)⁻¹ : ℝ) • ((mu⁻¹) • x))) ≤ (1 : EReal) := by
    simpa using
      (obverseConvex_le_coe_pos_iff_perspective_le_one (f := f) hf_nonneg hf_closed hf0
        (x := (mu⁻¹) • x) (lam := lam / mu) ht)
  have hsmul :
      (((lam / mu)⁻¹ : ℝ) • ((mu⁻¹) • x)) = (lam⁻¹) • x :=
    inv_div_inv_smul_smul_eq_inv_smul (x := x) (lam := lam) (mu := mu) hmu
  have hdiv :
      ((mu : EReal) * obverseConvex f ((mu⁻¹) • x) ≤ (lam : EReal)) ↔
        obverseConvex f ((mu⁻¹) • x) ≤ (((lam / mu) : ℝ) : EReal) :=
    obverse_dilation_le_iff_obverse_le_div (f := f) (x := x) (lam := lam) (mu := mu) hmu
  calc
    ((lam : EReal) * f ((lam⁻¹) • x) ≤ (mu : EReal)) ↔
        (((lam / mu) : ℝ) : EReal) * f ((lam⁻¹) • x) ≤ (1 : EReal) := hscale
    _ ↔ (((lam / mu) : ℝ) : EReal) *
          f ((((lam / mu)⁻¹ : ℝ) • ((mu⁻¹) • x))) ≤ (1 : EReal) := by
        -- rewrite the argument of `f` using the scaling identity
        rw [← hsmul]
    _ ↔ obverseConvex f ((mu⁻¹) • x) ≤ (((lam / mu) : ℝ) : EReal) := hobv.symm
    _ ↔ ((mu : EReal) * obverseConvex f ((mu⁻¹) • x) ≤ (lam : EReal)) := hdiv.symm

/-- Sublevel sets of the obverse match those of the perspective. -/
lemma sublevelSet_obverseConvex_eq_sublevelSet_perspective {n : ℕ} {f g : (Fin n → ℝ) → EReal}
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_closed : ClosedConvexFunction f) (hf0 : f 0 = 0)
    (hg : g = obverseConvex f) {α : ℝ} (hα : 0 < α) :
    {x | g x ≤ (α : EReal)} =
      {x | ((α : EReal) * f ((α⁻¹) • x)) ≤ (1 : EReal)} := by
  classical
  subst hg
  ext x
  simpa using
    (obverseConvex_le_coe_pos_iff_perspective_le_one (f := f) hf_nonneg hf_closed hf0
      (x := x) (lam := α) hα)

/-- Perspective sublevel sets are homothetic to those of `f`. -/
lemma sublevelSet_perspective_eq_smul_sublevelSet {n : ℕ} {f g : (Fin n → ℝ) → EReal}
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_closed : ClosedConvexFunction f) (hf0 : f 0 = 0)
    (hg : g = obverseConvex f) {α : ℝ} (hα : 0 < α) :
    {x | ((α : EReal) * f ((α⁻¹) • x)) ≤ (1 : EReal)} =
      α • {x | f x ≤ ((α⁻¹ : ℝ) : EReal)} := by
  have hpersp :=
    sublevelSet_obverseConvex_eq_sublevelSet_perspective (n := n) (f := f) (g := g) hf_nonneg
      hf_closed hf0 hg (α := α) hα
  have hsmul :=
    sublevelSet_obverseConvex_eq_smul_sublevelSet (n := n) (f := f) (g := g) hf_nonneg hf_closed
      hf0 hg (α := α) hα
  exact hpersp.symm.trans hsmul

/-- Text 15.0.38: Let `f : ℝⁿ → [0, +∞]` be a nonnegative closed convex function with `f 0 = 0`,
and let `g` be the obverse of `f`. For `λ > 0` define `(f_λ)(x) := λ * f (λ⁻¹ • x)`. Then for every
`α > 0`,
`{x | g x ≤ α} = {x | (f_α) x ≤ 1} = α • {x | f x ≤ α⁻¹}`. -/
theorem sublevelSet_obverseConvex_eq_sublevelSet_dilation_eq_smul_sublevelSet {n : ℕ}
    {f g : (Fin n → ℝ) → EReal} (hf_nonneg : ∀ x, 0 ≤ f x) (hf_closed : ClosedConvexFunction f)
    (hf0 : f 0 = 0) (hg : g = obverseConvex f) {α : ℝ} (hα : 0 < α) :
    let fα : (Fin n → ℝ) → EReal := fun x => (α : EReal) * f ((α⁻¹) • x)
    {x | g x ≤ (α : EReal)} = {x | fα x ≤ (1 : EReal)} ∧
      {x | fα x ≤ (1 : EReal)} = α • {x | f x ≤ ((α⁻¹ : ℝ) : EReal)} := by
  have hpersp :
      {x | g x ≤ (α : EReal)} =
        {x | ((α : EReal) * f ((α⁻¹) • x)) ≤ (1 : EReal)} :=
    sublevelSet_obverseConvex_eq_sublevelSet_perspective (n := n) (f := f) (g := g) hf_nonneg
      hf_closed hf0 hg (α := α) hα
  have hsmul :
      {x | ((α : EReal) * f ((α⁻¹) • x)) ≤ (1 : EReal)} =
        α • {x | f x ≤ ((α⁻¹ : ℝ) : EReal)} :=
    sublevelSet_perspective_eq_smul_sublevelSet (n := n) (f := f) (g := g) hf_nonneg hf_closed
      hf0 hg (α := α) hα
  simpa (config := { zeta := true }) using And.intro hpersp hsmul

/-- Text 15.0.39: Let `f : ℝⁿ → [0, +∞]` be a nonnegative closed convex function with `f 0 = 0`.
Then the polar `f^∘` is the obverse of the Fenchel conjugate `f*`. Consequently, for every `α > 0`,
`{x⋆ | f^∘ x⋆ ≤ α⁻¹} = α⁻¹ • {x⋆ | f* x⋆ ≤ α}`.

In this development, `f^∘` is `polarConvex f` and `f*` is `fenchelConjugate n f`. -/
theorem polarConvex_eq_obverseConvex_fenchelConjugate_and_sublevelSet {n : ℕ}
    {f : (Fin n → ℝ) → EReal} (hf_nonneg : ∀ x, 0 ≤ f x) (hf_closed : ClosedConvexFunction f)
    (hf0 : f 0 = 0) {α : ℝ} (hα : 0 < α) :
    polarConvex f = obverseConvex (fenchelConjugate n f) ∧
      {xStar | polarConvex f xStar ≤ ((α⁻¹ : ℝ) : EReal)} =
        (α⁻¹) • {xStar | fenchelConjugate n f xStar ≤ (α : EReal)} := by
  refine ⟨?_, ?_⟩
  · simpa using
      (obverseConvex_fenchelConjugate_eq_polarConvex (f := f) hf_nonneg hf_closed hf0).symm
  · simpa using
      (sublevelSet_polarConvex_le_inv_eq_inv_smul_sublevelSet_fenchelConjugate (f := f) hf_nonneg
        hf_closed hf0 (α := α) hα)

end Section15
end Chap03
