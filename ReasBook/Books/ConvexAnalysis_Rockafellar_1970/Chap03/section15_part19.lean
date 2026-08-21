/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yijie Wang, Yunxi Duan, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section15_part18

section Chap03
section Section15

open scoped BigOperators
open scoped Pointwise
open scoped Topology

/-- The obverse at `0` equals the recession function sublevel. -/
lemma obverseConvex_le_zero_iff_recessionFunction_le_one {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_closed : ClosedConvexFunction f) (hf0 : f 0 = 0)
    (x : Fin n → ℝ) :
    obverseConvex f x ≤ (0 : EReal) ↔ recessionFunction f x ≤ (1 : EReal) := by
  classical
  let fStar : (Fin n → ℝ) → EReal := fenchelConjugate n f
  have hproper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f :=
    properConvexFunctionOn_of_nonneg_closedConvex_zero (f := f) hf_nonneg hf_closed hf0
  have hsupp :
      supportFunctionEReal (effectiveDomain (Set.univ : Set (Fin n → ℝ)) fStar) =
        recessionFunction f :=
    section13_supportFunctionEReal_dom_fenchelConjugate_eq_recessionFunction (f := f)
      hf_closed hproper
  have hpolar :
      obverseConvex f = polarConvex fStar := by
    funext y
    have h :=
      polarFenchelConjugate_eq_sInf_dilation_le_one (f := f) hf_nonneg hf_closed hf0 y
    simpa [obverseConvex, fStar] using h.symm
  have hA_nonneg : ∀ y, (0 : EReal) ≤ fStar y :=
    fenchelConjugate_nonneg_of_nonneg_zero f hf0
  have hnonneg_polar : (0 : EReal) ≤ polarConvex fStar x := by
    unfold polarConvex
    refine le_sInf ?_
    intro μ hμ
    exact hμ.1
  have hdom_iff :
      recessionFunction f x ≤ (1 : EReal) ↔
        ∀ y ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) fStar,
          (y ⬝ᵥ x : ℝ) ≤ (1 : ℝ) := by
    constructor
    · intro hrec'
      have hrec'' :
          supportFunctionEReal
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) fStar) x ≤ (1 : EReal) := by
        simpa [hsupp] using hrec'
      exact
        (section13_supportFunctionEReal_le_coe_iff
            (C := effectiveDomain (Set.univ : Set (Fin n → ℝ)) fStar) (y := x) (μ := (1 : ℝ))).1
          hrec''
    · intro hrec'
      have hrec'' :
          supportFunctionEReal
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) fStar) x ≤ (1 : EReal) :=
        (section13_supportFunctionEReal_le_coe_iff
            (C := effectiveDomain (Set.univ : Set (Fin n → ℝ)) fStar) (y := x) (μ := (1 : ℝ))).2
          hrec'
      simpa [hsupp] using hrec''
  constructor
  · intro hle
    have hle' : polarConvex fStar x ≤ (0 : EReal) := by
      simpa [hpolar] using hle
    have hzero : polarConvex fStar x = (0 : EReal) :=
      le_antisymm hle' hnonneg_polar
    let hA : Set EReal :=
      {μStar : EReal |
        0 ≤ μStar ∧
          ∀ y : Fin n → ℝ,
            ((y ⬝ᵥ x : ℝ) : EReal) ≤ (1 : EReal) + μStar * fStar y}
    have hA_upper :
        ∀ {μ μ' : EReal}, μ ∈ hA → μ ≤ μ' → μ' ∈ hA := by
      intro μ μ' hμ hle
      refine ⟨le_trans hμ.1 hle, ?_⟩
      intro y
      have hineq := hμ.2 y
      have hmul :
          μ * fStar y ≤ μ' * fStar y :=
        mul_le_mul_of_nonneg_right hle (hA_nonneg y)
      have hsum : (1 : EReal) + μ * fStar y ≤ (1 : EReal) + μ' * fStar y := by
        simpa [add_comm, add_left_comm, add_assoc] using (add_le_add_left hmul (1 : EReal))
      exact le_trans hineq hsum
    have hforall_eps :
        ∀ ε : ℝ, 0 < ε →
          ∀ y : Fin n → ℝ,
            ((y ⬝ᵥ x : ℝ) : EReal) ≤
              (1 : EReal) + (ε : EReal) * fStar y := by
      intro ε hε y
      have hlt : (sInf hA) < (ε : EReal) := by
        have hε' : (0 : EReal) < (ε : EReal) := by exact_mod_cast hε
        have hzero' : sInf hA = (0 : EReal) := by
          simpa [polarConvex, hA] using hzero
        simpa [hzero'] using hε'
      have hmem : ∃ μ ∈ hA, μ < (ε : EReal) := by
        classical
        by_contra hcontra
        have hle' : (ε : EReal) ≤ sInf hA := by
          refine le_sInf ?_
          intro μ hμ
          by_contra hlt'
          have hlt'' : μ < (ε : EReal) := lt_of_not_ge hlt'
          exact hcontra ⟨μ, hμ, hlt''⟩
        exact (not_le_of_gt hlt) hle'
      rcases hmem with ⟨μ, hμA, hμlt⟩
      have hεA : (ε : EReal) ∈ hA :=
        hA_upper hμA (le_of_lt hμlt)
      exact hεA.2 y
    have hrec : ∀ y ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) fStar,
        (y ⬝ᵥ x : ℝ) ≤ (1 : ℝ) := by
      intro y hy
      have hy_top : fStar y ≠ (⊤ : EReal) := by
        have hy_lt : fStar y < (⊤ : EReal) := by
          simpa [effectiveDomain_eq] using hy
        exact (lt_top_iff_ne_top).1 hy_lt
      have hy_bot : fStar y ≠ (⊥ : EReal) := by
        intro hbot
        have h0le' : (0 : EReal) ≤ (⊥ : EReal) := by
          simpa [hbot] using (hA_nonneg y)
        have hbotlt : (⊥ : EReal) < (0 : EReal) := by simp
        exact (not_le_of_gt hbotlt) h0le'
      set r : ℝ := (fStar y).toReal
      have hr_eq : (r : EReal) = fStar y := by
        exact (EReal.coe_toReal hy_top hy_bot)
      have hr_nonneg : 0 ≤ r := by
        have h0le : (0 : EReal) ≤ (r : EReal) := by
          simpa [hr_eq] using (hA_nonneg y)
        exact (EReal.coe_le_coe_iff).1 h0le
      have hreal_ineq :
          ∀ ε : ℝ, 0 < ε → (y ⬝ᵥ x : ℝ) ≤ 1 + ε * r := by
        intro ε hε
        have hineq := hforall_eps ε hε y
        have hineq' :
            ((y ⬝ᵥ x : ℝ) : EReal) ≤
              ((1 + ε * r : ℝ) : EReal) := by
          simpa [hr_eq, EReal.coe_add, EReal.coe_mul, add_comm, add_left_comm, add_assoc] using hineq
        exact (EReal.coe_le_coe_iff).1 hineq'
      have hle_one : (y ⬝ᵥ x : ℝ) ≤ (1 : ℝ) := by
        by_cases hr0 : r = 0
        · have hineq := hreal_ineq 1 (by linarith)
          simpa [hr0] using hineq
        · have hrpos : 0 < r := lt_of_le_of_ne hr_nonneg (Ne.symm hr0)
          have hforall :
              ∀ δ : ℝ, 0 < δ → (y ⬝ᵥ x : ℝ) ≤ 1 + δ := by
            intro δ hδ
            have hεpos : 0 < δ / r := by exact div_pos hδ hrpos
            have hineq := hreal_ineq (δ / r) hεpos
            have hcalc : (δ / r) * r = δ := by
              field_simp [hr0]
            simpa [hcalc] using hineq
          exact le_of_forall_pos_le_add hforall
      exact hle_one
    exact (hdom_iff.mpr hrec)
  · intro hrec
    have hrec' : ∀ y ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) fStar,
        (y ⬝ᵥ x : ℝ) ≤ (1 : ℝ) :=
      (hdom_iff.mp hrec)
    have hA :
        {μ : EReal |
            ∃ t : ℝ, 0 < t ∧ μ = (t : EReal)} ⊆
          {μStar : EReal |
            0 ≤ μStar ∧
              ∀ y : Fin n → ℝ,
                ((y ⬝ᵥ x : ℝ) : EReal) ≤ (1 : EReal) + μStar * fStar y} := by
      intro μ hμ
      rcases hμ with ⟨t, ht, rfl⟩
      refine ⟨by exact_mod_cast (le_of_lt ht), ?_⟩
      intro y
      by_cases hy : y ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) fStar
      · have hy_le : (y ⬝ᵥ x : ℝ) ≤ (1 : ℝ) := hrec' y hy
        have hy_le' : ((y ⬝ᵥ x : ℝ) : EReal) ≤ (1 : EReal) := by
          exact_mod_cast hy_le
        have hnonneg : (0 : EReal) ≤ (t : EReal) * fStar y := by
          have ht_nonneg : (0 : EReal) ≤ (t : EReal) := by exact_mod_cast (le_of_lt ht)
          have hf_nonneg' : (0 : EReal) ≤ fStar y := hA_nonneg y
          have hmul := mul_le_mul_of_nonneg_left hf_nonneg' ht_nonneg
          simpa using hmul
        have hsum : (1 : EReal) ≤ (1 : EReal) + (t : EReal) * fStar y := by
          simpa [add_comm, add_left_comm, add_assoc] using (add_le_add_left hnonneg (1 : EReal))
        exact le_trans hy_le' hsum
      · have hy_top : fStar y = (⊤ : EReal) := by
          by_contra hne
          have hlt : fStar y < (⊤ : EReal) := (lt_top_iff_ne_top).2 hne
          have hy_mem : y ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) fStar := by
            have : y ∈ (Set.univ : Set (Fin n → ℝ)) ∧ fStar y < (⊤ : EReal) :=
              ⟨by simp, hlt⟩
            simpa [effectiveDomain_eq] using this
          exact hy hy_mem
        have htop :
            (1 : EReal) + (t : EReal) * fStar y = (⊤ : EReal) := by
          have hne : (1 : EReal) ≠ (⊥ : EReal) := by
            simpa using (EReal.coe_ne_bot (1 : ℝ))
          have htop' : (1 : EReal) + (⊤ : EReal) = (⊤ : EReal) := by
            simpa using (EReal.add_top_of_ne_bot (x := (1 : EReal)) hne)
          simpa [hy_top, EReal.coe_mul_top_of_pos ht] using htop'
        simp [htop]
    have hA_sInf : sInf
        {μStar : EReal |
            0 ≤ μStar ∧
              ∀ y : Fin n → ℝ,
                ((y ⬝ᵥ x : ℝ) : EReal) ≤ (1 : EReal) + μStar * fStar y} =
        (0 : EReal) := by
      have hle : sInf
          {μStar : EReal |
              0 ≤ μStar ∧
                ∀ y : Fin n → ℝ,
                  ((y ⬝ᵥ x : ℝ) : EReal) ≤ (1 : EReal) + μStar * fStar y} ≤ (0 : EReal) := by
        have hS :
            sInf
                {μ : EReal | ∃ t : ℝ, 0 < t ∧ μ = (t : EReal)} = (0 : EReal) :=
          sInf_pos_real_eq_zero
        have hsubset :
            {μ : EReal | ∃ t : ℝ, 0 < t ∧ μ = (t : EReal)} ⊆
                {μStar : EReal |
                    0 ≤ μStar ∧
                      ∀ y : Fin n → ℝ,
                        ((y ⬝ᵥ x : ℝ) : EReal) ≤
                          (1 : EReal) + μStar * fStar y} := hA
        have hle' :
            sInf
                {μStar : EReal |
                    0 ≤ μStar ∧
                      ∀ y : Fin n → ℝ,
                        ((y ⬝ᵥ x : ℝ) : EReal) ≤
                          (1 : EReal) + μStar * fStar y} ≤
              sInf {μ : EReal | ∃ t : ℝ, 0 < t ∧ μ = (t : EReal)} :=
          sInf_le_sInf hsubset
        simpa [hS] using hle'
      exact le_antisymm hle hnonneg_polar
    have hpol : polarConvex fStar x = (0 : EReal) := by
      unfold polarConvex
      simpa using hA_sInf
    simp [hpolar, hpol]
/-- Text 15.0.33: Let `f : ℝⁿ → [0, +∞]` and let `g` be the function defined by the obverse formula
`g x = inf {λ > 0 | f_λ x ≤ 1}`, where `f_λ x := λ * f (x / λ)` for `λ > 0`. Then the epigraph of
`g` admits the geometric representation

`epi g = {(x, λ) | h (λ, x) ≤ 1}`,

where

`h (λ, x) = f_λ x` if `λ > 0`, `h (0, x) = (f₀⁺) x` (the recession function), and `h (λ, x) = +∞`
if `λ < 0`. -/
lemma epigraph_obverseConvex_eq_sublevel_one {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_closed : ClosedConvexFunction f) (hf0 : f 0 = 0) :
    let g : (Fin n → ℝ) → EReal := obverseConvex f
    let h : ℝ → (Fin n → ℝ) → EReal :=
      fun t x =>
        if 0 < t then
          (t : EReal) * f ((t⁻¹) • x)
        else if t = 0 then
          recessionFunction f x
        else
          ⊤
    epigraph (S := (Set.univ : Set (Fin n → ℝ))) g = {p : (Fin n → ℝ) × ℝ | h p.2 p.1 ≤ 1} := by
  classical
  intro g h
  ext p
  cases p with
  | mk x μ =>
      simp [mem_epigraph_univ_iff, g, h]
      by_cases hpos : 0 < μ
      ·
        have hiff :=
          obverseConvex_le_coe_pos_iff_perspective_le_one (f := f) hf_nonneg hf_closed hf0
            (x := x) (lam := μ) hpos
        simpa [hpos] using hiff
      · have hμle : μ ≤ 0 := le_of_not_gt hpos
        by_cases hzero : μ = 0
        ·
          have hiff :=
            obverseConvex_le_zero_iff_recessionFunction_le_one (f := f) hf_nonneg hf_closed hf0 x
          simpa [hpos, hzero] using hiff
        · have hneg : μ < 0 := lt_of_le_of_ne hμle hzero
          constructor
          · intro hle
            have h0le : (0 : EReal) ≤ obverseConvex f x :=
              obverseConvex_nonneg f x
            have hneg' : (μ : EReal) < (0 : EReal) := by exact_mod_cast hneg
            have hlt : (μ : EReal) < obverseConvex f x := lt_of_lt_of_le hneg' h0le
            exact (not_le_of_gt hlt hle).elim
          · intro hle
            have hle' : (⊤ : EReal) ≤ (1 : EReal) := by
              simpa [hpos, hzero] using hle
            exact (not_top_le_coe 1 hle').elim

/-- At `λ = 1`, the auxiliary function `h` agrees with `f`. -/
lemma h_at_one_simp {n : ℕ} (f : (Fin n → ℝ) → EReal) :
    let h : ℝ → (Fin n → ℝ) → EReal :=
      fun t x =>
        if 0 < t then
          (t : EReal) * f ((t⁻¹) • x)
        else if t = 0 then
          recessionFunction f x
        else
          ⊤
    ∀ x, h 1 x = f x := by
  intro h x
  simp [h, zero_lt_one]

/-- The `λ = 1` slice of `P = epi h` projects to `epi f`. -/
lemma image_P_slice_lambda_one_eq_epigraph_f {n : ℕ} (f : (Fin n → ℝ) → EReal) :
    let h : ℝ → (Fin n → ℝ) → EReal :=
      fun t x =>
        if 0 < t then
          (t : EReal) * f ((t⁻¹) • x)
        else if t = 0 then
          recessionFunction f x
        else
          ⊤
    let P : Set ((ℝ × (Fin n → ℝ)) × ℝ) := {q | h q.1.1 q.1.2 ≤ (q.2 : EReal)}
    ((fun q : ((ℝ × (Fin n → ℝ)) × ℝ) => (q.1.2, q.2)) '' (P ∩ {q | q.1.1 = (1 : ℝ)}) =
        epigraph (S := (Set.univ : Set (Fin n → ℝ))) f) := by
  classical
  intro h P
  have h_one : ∀ x, h 1 x = f x := by
    intro x
    simp [h, zero_lt_one]
  ext p
  constructor
  · rintro ⟨q, ⟨hqP, hq1⟩, rfl⟩
    have hqP' : h q.1.1 q.1.2 ≤ (q.2 : EReal) := by
      simpa [P] using hqP
    have hq1' : q.1.1 = (1 : ℝ) := by
      simpa using hq1
    have hqP'' : h 1 q.1.2 ≤ (q.2 : EReal) := by
      simpa [hq1'] using hqP'
    have hqP''' : f q.1.2 ≤ (q.2 : EReal) := by
      simpa [h_one q.1.2] using hqP''
    simpa [mem_epigraph_univ_iff] using hqP'''
  · intro hp
    rcases p with ⟨x, μ⟩
    have hμ : f x ≤ (μ : EReal) := by
      simpa [mem_epigraph_univ_iff] using hp
    refine ⟨(((1 : ℝ), x), μ), ?_, rfl⟩
    refine ⟨?_, rfl⟩
    have hμ' : h 1 x ≤ (μ : EReal) := by
      simpa [h_one x] using hμ
    simpa using hμ'

/-- The `μ = 1` slice of `P = epi h` projects to the `h ≤ 1` sublevel set. -/
lemma image_P_slice_mu_one_eq_sublevel_h {n : ℕ} (f : (Fin n → ℝ) → EReal) :
    let h : ℝ → (Fin n → ℝ) → EReal :=
      fun t x =>
        if 0 < t then
          (t : EReal) * f ((t⁻¹) • x)
        else if t = 0 then
          recessionFunction f x
        else
          ⊤
    let P : Set ((ℝ × (Fin n → ℝ)) × ℝ) := {q | h q.1.1 q.1.2 ≤ (q.2 : EReal)}
    ((fun q : ((ℝ × (Fin n → ℝ)) × ℝ) => (q.1.2, q.1.1)) '' (P ∩ {q | q.2 = (1 : ℝ)}) =
        {p : (Fin n → ℝ) × ℝ | h p.2 p.1 ≤ (1 : EReal)}) := by
  classical
  intro h P
  ext p
  constructor
  · rintro ⟨q, ⟨hqP, hq1⟩, rfl⟩
    have hqP' : h q.1.1 q.1.2 ≤ (q.2 : EReal) := by
      simpa [P] using hqP
    have hq1' : q.2 = (1 : ℝ) := by
      simpa using hq1
    have hqP'' : h q.1.1 q.1.2 ≤ (1 : EReal) := by
      simpa [hq1'] using hqP'
    simpa using hqP''
  · intro hp
    refine ⟨((p.2, p.1), (1 : ℝ)), ?_, rfl⟩
    refine ⟨?_, rfl⟩
    simpa [P] using hp

/-- The sublevel set `h ≤ 1` is the epigraph of `obverseConvex f`. -/
lemma sublevel_h_one_eq_epigraph_obverseConvex {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_closed : ClosedConvexFunction f) (hf0 : f 0 = 0) :
    let g : (Fin n → ℝ) → EReal := obverseConvex f
    let h : ℝ → (Fin n → ℝ) → EReal :=
      fun t x =>
        if 0 < t then
          (t : EReal) * f ((t⁻¹) • x)
        else if t = 0 then
          recessionFunction f x
        else
          ⊤
    {p : (Fin n → ℝ) × ℝ | h p.2 p.1 ≤ (1 : EReal)} =
      epigraph (S := (Set.univ : Set (Fin n → ℝ))) g := by
  classical
  intro g h
  simpa [g, h] using
    (epigraph_obverseConvex_eq_sublevel_one (f := f) hf_nonneg hf_closed hf0).symm

/-- Text 15.0.34: Let `P = epi h ⊆ ℝ^{n+2}` be the (closed convex) cone given as the epigraph of the
function `h (λ, x)` from Text 15.0.33; it is the smallest closed convex cone containing the points
`(1, x, μ)` with `μ ≥ f x`.

Then the slice of `P` by the hyperplane `λ = 1` corresponds to the epigraph `epi f`, and the slice
by the hyperplane `μ = 1` corresponds to the epigraph `epi g` of the obverse `g`. -/
lemma epigraph_h_slice_hyperplanes_correspond {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_closed : ClosedConvexFunction f) (hf0 : f 0 = 0) :
    let g : (Fin n → ℝ) → EReal := obverseConvex f
    let h : ℝ → (Fin n → ℝ) → EReal :=
      fun t x =>
        if 0 < t then
          (t : EReal) * f ((t⁻¹) • x)
        else if t = 0 then
          recessionFunction f x
        else
          ⊤
    let P : Set ((ℝ × (Fin n → ℝ)) × ℝ) := {q | h q.1.1 q.1.2 ≤ (q.2 : EReal)}
    ((fun q : ((ℝ × (Fin n → ℝ)) × ℝ) => (q.1.2, q.2)) '' (P ∩ {q | q.1.1 = (1 : ℝ)}) =
        epigraph (S := (Set.univ : Set (Fin n → ℝ))) f) ∧
      ((fun q : ((ℝ × (Fin n → ℝ)) × ℝ) => (q.1.2, q.1.1)) '' (P ∩ {q | q.2 = (1 : ℝ)}) =
        epigraph (S := (Set.univ : Set (Fin n → ℝ))) g) := by
  classical
  intro g h P
  refine ⟨?_, ?_⟩
  · simpa using (image_P_slice_lambda_one_eq_epigraph_f (f := f))
  ·
    calc
      ((fun q : ((ℝ × (Fin n → ℝ)) × ℝ) => (q.1.2, q.1.1)) '' (P ∩ {q | q.2 = (1 : ℝ)}))
          =
          {p : (Fin n → ℝ) × ℝ | h p.2 p.1 ≤ (1 : EReal)} := by
            simpa using (image_P_slice_mu_one_eq_sublevel_h (f := f))
      _ = epigraph (S := (Set.univ : Set (Fin n → ℝ))) g := by
            simpa using
              (sublevel_h_one_eq_epigraph_obverseConvex (f := f) hf_nonneg hf_closed hf0)

/-- The recession function is nonnegative when `f ≥ 0` and `f 0 = 0`. -/
lemma recessionFunction_nonneg_of_nonneg_zero {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf0 : f 0 = 0) :
    ∀ y, (0 : EReal) ≤ recessionFunction f y := by
  intro y
  unfold recessionFunction
  have h0mem :
      (0 : Fin n → ℝ) ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f := by
    have hlt : f (0 : Fin n → ℝ) < (⊤ : EReal) := by
      have h0ne : (0 : EReal) ≠ (⊤ : EReal) := by simp
      have : f (0 : Fin n → ℝ) ≠ (⊤ : EReal) := by simp [hf0]
      exact (lt_top_iff_ne_top).2 this
    have :
        (0 : Fin n → ℝ) ∈
          {x | x ∈ (Set.univ : Set (Fin n → ℝ)) ∧ f x < (⊤ : EReal)} := by
      exact ⟨by simp, hlt⟩
    simpa [effectiveDomain_eq] using this
  have hmem :
      f y ∈
        {r : EReal |
          ∃ x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f, r = f (x + y) - f x} := by
    refine ⟨0, h0mem, ?_⟩
    simp [hf0]
  have hle :
      f y ≤
        sSup
          {r : EReal |
            ∃ x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f, r = f (x + y) - f x} :=
    le_sSup hmem
  exact le_trans (hf_nonneg y) hle

/-- The recession function is positively homogeneous under closedness and nonnegativity. -/
lemma recessionFunction_posHom_of_nonneg_closedConvex_zero {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_closed : ClosedConvexFunction f) (hf0 : f 0 = 0) :
    PositivelyHomogeneous (recessionFunction f) := by
  classical
  set C : Set (Fin n → ℝ) :=
    effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)
  have hproper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f :=
    properConvexFunctionOn_of_nonneg_closedConvex_zero (f := f) hf_nonneg hf_closed hf0
  have hproperStar :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) :=
    proper_fenchelConjugate_of_proper (n := n) (f := f) hproper
  have hCne : Set.Nonempty C :=
    section13_effectiveDomain_nonempty_of_proper (n := n) (f := fenchelConjugate n f) hproperStar
  have hCconv : Convex ℝ C := by
    have hconvStar : ConvexFunction (fenchelConjugate n f) :=
      (fenchelConjugate_closedConvex (n := n) (f := f)).2
    have hconvOn :
        ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) := by
      simpa [ConvexFunction] using hconvStar
    simpa [C] using
      (effectiveDomain_convex (S := (Set.univ : Set (Fin n → ℝ)))
        (f := fenchelConjugate n f) (hf := hconvOn))
  have hsupp :
      supportFunctionEReal C = recessionFunction f := by
    simpa [C] using
      section13_supportFunctionEReal_dom_fenchelConjugate_eq_recessionFunction (n := n) (f := f)
        hf_closed hproper
  have hpos :
      PositivelyHomogeneous (supportFunctionEReal C) :=
    (section13_supportFunctionEReal_closedProperConvex_posHom (n := n) (C := C) hCne hCconv).2.2
  simpa [hsupp] using hpos

/-- Normalizing the `h`-inequality at positive `μ`. -/
lemma h_div_mu_le_one_of_h_le_mu {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_closed : ClosedConvexFunction f) (hf0 : f 0 = 0) :
    let h : ℝ → (Fin n → ℝ) → EReal :=
      fun t x =>
        if 0 < t then
          (t : EReal) * f ((t⁻¹) • x)
        else if t = 0 then
          recessionFunction f x
        else
          ⊤
    ∀ {lam μ : ℝ} {x : Fin n → ℝ}, 0 < μ →
      h lam x ≤ (μ : EReal) →
        h (lam / μ) ((μ⁻¹) • x) ≤ (1 : EReal) := by
  classical
  intro h lam μ x hμ hle
  by_cases hlam_pos : 0 < lam
  · have hlam_div_pos : 0 < lam / μ := div_pos hlam_pos hμ
    have hle' :
        (lam : EReal) * f ((lam⁻¹) • x) ≤ (μ : EReal) := by
      simpa [h, hlam_pos] using hle
    have hmul :
        ((μ⁻¹ : ℝ) : EReal) * ((lam : EReal) * f ((lam⁻¹) • x)) ≤
          ((μ⁻¹ : ℝ) : EReal) * (μ : EReal) := by
      have hμnonneg : 0 ≤ (μ⁻¹ : ℝ) := inv_nonneg.mpr (le_of_lt hμ)
      exact mul_le_mul_of_nonneg_left hle' (by exact_mod_cast hμnonneg)
    have hscalar : (μ / lam) * μ⁻¹ = lam⁻¹ := by
      have hμne : μ ≠ 0 := ne_of_gt hμ
      have hlamne : lam ≠ 0 := ne_of_gt hlam_pos
      calc
        (μ / lam) * μ⁻¹ = (μ * μ⁻¹) / lam := by
          field_simp [hμne, hlamne]
        _ = (1 : ℝ) / lam := by simp [hμne]
        _ = lam⁻¹ := by simp [div_eq_mul_inv]
    have hsmul :
        (lam / μ)⁻¹ • ((μ⁻¹) • x) = (lam⁻¹) • x := by
      calc
        (lam / μ)⁻¹ • ((μ⁻¹) • x) = ((μ / lam) * μ⁻¹) • x := by
          simp [smul_smul, inv_div]
        _ = (lam⁻¹) • x := by simp [hscalar]
    have hsmul' :
        (μ / lam) • ((μ⁻¹) • x) = (lam⁻¹) • x := by
      simpa [inv_div] using hsmul
    have hscale :
        ((μ⁻¹ : ℝ) : EReal) * ((lam : EReal) * f ((lam⁻¹) • x)) =
          ((lam / μ : ℝ) : EReal) * f (((lam / μ)⁻¹) • ((μ⁻¹) • x)) := by
      calc
        ((μ⁻¹ : ℝ) : EReal) * ((lam : EReal) * f ((lam⁻¹) • x)) =
            ((lam / μ : ℝ) : EReal) * f ((lam⁻¹) • x) := by
              simp [div_eq_mul_inv, mul_left_comm, mul_assoc]
        _ = ((lam / μ : ℝ) : EReal) * f (((lam / μ)⁻¹) • ((μ⁻¹) • x)) := by
              simp [hsmul']
    have hright :
        ((μ⁻¹ : ℝ) : EReal) * (μ : EReal) = (1 : EReal) := by
      have h :=
        section13_mul_inv_mul_cancel_pos_real (a := μ) hμ (z := (1 : EReal))
      simpa [mul_assoc] using h
    have hle'' :
        ((lam / μ : ℝ) : EReal) * f (((lam / μ)⁻¹) • ((μ⁻¹) • x)) ≤ (1 : EReal) := by
      have hmul' :
          ((lam / μ : ℝ) : EReal) * f (((lam / μ)⁻¹) • ((μ⁻¹) • x)) ≤
            ((μ⁻¹ : ℝ) : EReal) * (μ : EReal) := by
        simpa [hscale] using hmul
      simpa [hright] using hmul'
    have hrepr :
        h (lam / μ) ((μ⁻¹) • x) =
          ((lam / μ : ℝ) : EReal) * f (((lam / μ)⁻¹) • ((μ⁻¹) • x)) := by
      simp [h, hlam_div_pos]
    simpa [hrepr] using hle''
  · have hlam_nonpos : lam ≤ 0 := le_of_not_gt hlam_pos
    by_cases hlam_zero : lam = 0
    · have hposHom : PositivelyHomogeneous (recessionFunction f) :=
        recessionFunction_posHom_of_nonneg_closedConvex_zero (f := f) hf_nonneg hf_closed hf0
      have hle' : recessionFunction f x ≤ (μ : EReal) := by
        simpa [h, hlam_zero] using hle
      have hmul :
          ((μ⁻¹ : ℝ) : EReal) * recessionFunction f x ≤
            ((μ⁻¹ : ℝ) : EReal) * (μ : EReal) := by
        have hμnonneg : 0 ≤ (μ⁻¹ : ℝ) := inv_nonneg.mpr (le_of_lt hμ)
        exact mul_le_mul_of_nonneg_left hle' (by exact_mod_cast hμnonneg)
      have hright :
          ((μ⁻¹ : ℝ) : EReal) * (μ : EReal) = (1 : EReal) := by
        have h :=
          section13_mul_inv_mul_cancel_pos_real (a := μ) hμ (z := (1 : EReal))
        simpa [mul_assoc] using h
      have hle'' :
          recessionFunction f ((μ⁻¹) • x) ≤ (1 : EReal) := by
        have hhom : recessionFunction f ((μ⁻¹) • x) =
            ((μ⁻¹ : ℝ) : EReal) * recessionFunction f x :=
          hposHom x (μ⁻¹) (inv_pos.2 hμ)
        simpa [hhom, hright] using hmul
      simpa [h, hlam_zero] using hle''
    · have hlam_neg : lam < 0 := lt_of_le_of_ne hlam_nonpos hlam_zero
      have hle' : (⊤ : EReal) ≤ (μ : EReal) := by
        convert hle using 1; simp [h, hlam_pos, hlam_zero]
      exact (False.elim ((not_top_le_coe μ) hle'))

/-- Points in `P` have nonnegative `λ`. -/
lemma mem_P_imp_lam_nonneg {n : ℕ} {f : (Fin n → ℝ) → EReal} :
    let h : ℝ → (Fin n → ℝ) → EReal :=
      fun t x =>
        if 0 < t then
          (t : EReal) * f ((t⁻¹) • x)
        else if t = 0 then
          recessionFunction f x
        else
          ⊤
    let P : Set ((ℝ × (Fin n → ℝ)) × ℝ) := {q | h q.1.1 q.1.2 ≤ (q.2 : EReal)}
    ∀ {q}, q ∈ P → 0 ≤ q.1.1 := by
  classical
  intro h P q hq
  by_contra hneg
  have hlt : q.1.1 < 0 := lt_of_not_ge hneg
  have htop : h q.1.1 q.1.2 = ⊤ := by
    have hnotpos : ¬ 0 < q.1.1 := by exact not_lt.mpr (le_of_lt hlt)
    have hneq : q.1.1 ≠ 0 := ne_of_lt hlt
    simp [h, hnotpos, hneq]
  have hq' : (⊤ : EReal) ≤ (q.2 : EReal) := by
    convert hq using 1; simp [P, htop]
  have : (⊤ : EReal) ≤ (q.2 : EReal) := hq'
  exact (not_top_le_coe q.2 this).elim

/-- The auxiliary function `h` is nonnegative when `λ ≥ 0`. -/
lemma h_nonneg_of_lam_nonneg {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf0 : f 0 = 0) :
    let h : ℝ → (Fin n → ℝ) → EReal :=
      fun t x =>
        if 0 < t then
          (t : EReal) * f ((t⁻¹) • x)
        else if t = 0 then
          recessionFunction f x
        else
          ⊤
    ∀ {lam x}, 0 ≤ lam → (0 : EReal) ≤ h lam x := by
  classical
  intro h lam x hlam
  by_cases hpos : 0 < lam
  · have hlam' : (0 : EReal) ≤ (lam : EReal) := by exact_mod_cast (le_of_lt hpos)
    have hf' : (0 : EReal) ≤ f ((lam⁻¹) • x) := hf_nonneg _
    have hmul :
        (0 : EReal) ≤ (lam : EReal) * f ((lam⁻¹) • x) := by
      have hle :
          (lam : EReal) * (0 : EReal) ≤ (lam : EReal) * f ((lam⁻¹) • x) :=
        mul_le_mul_of_nonneg_left (by simpa using hf') hlam'
      simpa using hle
    simpa [h, hpos] using hmul
  · have hzero : lam = 0 := le_antisymm (le_of_not_gt hpos) hlam
    have hrecc : (0 : EReal) ≤ recessionFunction f x :=
      recessionFunction_nonneg_of_nonneg_zero (f := f) hf_nonneg hf0 x
    simpa [h, hpos, hzero] using hrecc

/-- Dot-product bound for points in the epigraph set `P`. -/
lemma dotProduct_le_mu_add_lam_mul_fStar_toReal_of_mem_P {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_closed : ClosedConvexFunction f) (hf0 : f 0 = 0) :
    let fStar : (Fin n → ℝ) → EReal := fenchelConjugate n f
    let C : Set (Fin n → ℝ) := effectiveDomain (Set.univ : Set (Fin n → ℝ)) fStar
    let h : ℝ → (Fin n → ℝ) → EReal :=
      fun t x =>
        if 0 < t then
          (t : EReal) * f ((t⁻¹) • x)
        else if t = 0 then
          recessionFunction f x
        else
          ⊤
    let P : Set ((ℝ × (Fin n → ℝ)) × ℝ) := {q | h q.1.1 q.1.2 ≤ (q.2 : EReal)}
    ∀ {q}, q ∈ P → ∀ y ∈ C,
      dotProduct q.1.2 y ≤ q.2 + q.1.1 * (fStar y).toReal := by
  classical
  intro fStar C h P q hq y hy
  rcases q with ⟨⟨lam, x⟩, μ⟩
  have hq' : h lam x ≤ (μ : EReal) := by simpa [P] using hq
  have hlam_nonneg : 0 ≤ lam := by
    have hq'' : ((lam, x), μ) ∈ P := by simpa using hq
    simpa [h, P] using (mem_P_imp_lam_nonneg (f := f) (q := ((lam, x), μ)) hq'')
  have hy_top : fStar y ≠ (⊤ : EReal) := by
    have hy' :
        y ∈ (Set.univ : Set (Fin n → ℝ)) ∧ fStar y < (⊤ : EReal) := by
      simpa [C, effectiveDomain_eq] using hy
    have hy_lt : fStar y < (⊤ : EReal) := hy'.2
    exact (lt_top_iff_ne_top).1 hy_lt
  have hy_bot : fStar y ≠ (⊥ : EReal) := by
    intro hbot
    have h0le : (0 : EReal) ≤ fStar y :=
      fenchelConjugate_nonneg_of_nonneg_zero f hf0 y
    have h0le' : (0 : EReal) ≤ (⊥ : EReal) := by
      convert h0le using 1; simp [hbot]
    have hbotlt : (⊥ : EReal) < (0 : EReal) := by simp
    exact (not_le_of_gt hbotlt) h0le'
  let r : ℝ := (fStar y).toReal
  have hr_eq : (r : EReal) = fStar y := by
    exact (EReal.coe_toReal hy_top hy_bot)
  by_cases hlam_zero : lam = 0
  · have hproper :
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f :=
      properConvexFunctionOn_of_nonneg_closedConvex_zero (f := f) hf_nonneg hf_closed hf0
    have hsupp :
        supportFunctionEReal C = recessionFunction f := by
      simpa [C, fStar] using
        (section13_supportFunctionEReal_dom_fenchelConjugate_eq_recessionFunction (n := n)
          (f := f) hf_closed hproper)
    have hrec : recessionFunction f x ≤ (μ : EReal) := by
      simpa [h, hlam_zero] using hq'
    have hsupp_le : supportFunctionEReal C x ≤ (μ : EReal) := by
      simpa [hsupp] using hrec
    have hdot :
        dotProduct x y ≤ μ := by
      have hdot' :=
        (section13_supportFunctionEReal_le_coe_iff (C := C) (y := x) (μ := μ)).1 hsupp_le
      simpa [dotProduct_comm] using hdot' y hy
    simpa [hlam_zero] using hdot
  · have hlam_pos : 0 < lam := lt_of_le_of_ne hlam_nonneg (Ne.symm hlam_zero)
    have hfenchel :
        (((lam⁻¹) • x ⬝ᵥ y : ℝ) : EReal) ≤ f ((lam⁻¹) • x) + fStar y := by
      exact dotProduct_le_add_fenchelConjugate f hf_nonneg hf0 ((lam⁻¹) • x) y
    have hmul :
        (lam : EReal) * (((lam⁻¹) • x ⬝ᵥ y : ℝ) : EReal) ≤
          (lam : EReal) * (f ((lam⁻¹) • x) + fStar y) :=
      mul_le_mul_of_nonneg_left hfenchel (by exact_mod_cast (le_of_lt hlam_pos))
    have hleft :
        (lam : EReal) * (((lam⁻¹) • x ⬝ᵥ y : ℝ) : EReal) = ((x ⬝ᵥ y : ℝ) : EReal) := by
      have hreal :
          (lam : ℝ) * ((lam⁻¹) • x ⬝ᵥ y : ℝ) = (x ⬝ᵥ y : ℝ) := by
        have hdot :
            ((lam⁻¹) • x ⬝ᵥ y : ℝ) = (lam⁻¹) * (x ⬝ᵥ y : ℝ) := by
          simp [smul_eq_mul, smul_dotProduct]
        calc
          (lam : ℝ) * ((lam⁻¹) • x ⬝ᵥ y : ℝ) =
              (lam : ℝ) * ((lam⁻¹) * (x ⬝ᵥ y : ℝ)) := by
                simp [hdot]
          _ = (lam * lam⁻¹) * (x ⬝ᵥ y : ℝ) := by ring
          _ = (x ⬝ᵥ y : ℝ) := by simp [hlam_pos.ne']
      have hreal' : ((lam * ((lam⁻¹) • x ⬝ᵥ y : ℝ) : ℝ) : EReal) = ((x ⬝ᵥ y : ℝ) : EReal) := by
        exact_mod_cast hreal
      simpa [EReal.coe_mul] using hreal'
    have hmul' :
        ((x ⬝ᵥ y : ℝ) : EReal) ≤ (lam : EReal) * (f ((lam⁻¹) • x) + fStar y) := by
      calc
        ((x ⬝ᵥ y : ℝ) : EReal) =
            (lam : EReal) * (((lam⁻¹) • x ⬝ᵥ y : ℝ) : EReal) := by
              simpa using hleft.symm
        _ ≤ (lam : EReal) * (f ((lam⁻¹) • x) + fStar y) := hmul
    have hlam_le : (lam : EReal) * f ((lam⁻¹) • x) ≤ (μ : EReal) := by
      simpa [h, hlam_pos] using hq'
    have hf_top : f ((lam⁻¹) • x) ≠ (⊤ : EReal) := by
      intro htop
      have htop' : (lam : EReal) * f ((lam⁻¹) • x) = ⊤ := by
        simp [htop, EReal.coe_mul_top_of_pos hlam_pos]
      have hle' : (⊤ : EReal) ≤ (μ : EReal) := by
        convert hlam_le using 1; simp [htop']
      exact (not_top_le_coe μ hle').elim
    have hf_bot : f ((lam⁻¹) • x) ≠ (⊥ : EReal) := by
      intro hbot
      have h0le : (0 : EReal) ≤ f ((lam⁻¹) • x) := hf_nonneg _
      have h0le' : (0 : EReal) ≤ (⊥ : EReal) := by
        convert h0le using 1; simp [hbot]
      have hbotlt : (⊥ : EReal) < (0 : EReal) := by simp
      exact (not_le_of_gt hbotlt) h0le'
    let s : ℝ := (f ((lam⁻¹) • x)).toReal
    have hs_eq : (s : EReal) = f ((lam⁻¹) • x) :=
      EReal.coe_toReal hf_top hf_bot
    have hlam_le' : ((lam * s : ℝ) : EReal) ≤ (μ : EReal) := by
      have hle' := hlam_le
      simp [hs_eq.symm] at hle'
      exact hle'
    have hlam_le_real : lam * s ≤ μ := (EReal.coe_le_coe_iff).1 hlam_le'
    have hmul_real : (x ⬝ᵥ y : ℝ) ≤ lam * (s + r) := by
      have hmul'' :
          ((x ⬝ᵥ y : ℝ) : EReal) ≤ (lam : EReal) * ((s + r : ℝ) : EReal) := by
        simpa [hs_eq, hr_eq, EReal.coe_add] using hmul'
      have hmul''' :
          ((x ⬝ᵥ y : ℝ) : EReal) ≤ ((lam * (s + r) : ℝ) : EReal) := by
        simpa [EReal.coe_mul] using hmul''
      exact (EReal.coe_le_coe_iff).1 hmul'''
    have hreal : (x ⬝ᵥ y : ℝ) ≤ μ + lam * r := by
      have hmul_real' : lam * (s + r) ≤ μ + lam * r := by
        calc
          lam * (s + r) = lam * s + lam * r := by ring
          _ ≤ μ + lam * r := by
                simpa [add_comm, add_left_comm, add_assoc] using
                  (add_le_add_right hlam_le_real (lam * r))
      exact le_trans hmul_real hmul_real'
    simpa [r] using hreal

/-- The epigraph set `P` is closed. -/
lemma isClosed_P {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_closed : ClosedConvexFunction f) (hf0 : f 0 = 0) :
    let h : ℝ → (Fin n → ℝ) → EReal :=
      fun t x =>
        if 0 < t then
          (t : EReal) * f ((t⁻¹) • x)
        else if t = 0 then
          recessionFunction f x
        else
          ⊤
    let P : Set ((ℝ × (Fin n → ℝ)) × ℝ) := {q | h q.1.1 q.1.2 ≤ (q.2 : EReal)}
    IsClosed P := by
  classical
  intro h P
  set fStar : (Fin n → ℝ) → EReal := fenchelConjugate n f
  set C : Set (Fin n → ℝ) := effectiveDomain (Set.univ : Set (Fin n → ℝ)) fStar
  refine (closure_subset_iff_isClosed).1 ?_
  intro q hq
  rcases (mem_closure_iff_seq_limit).1 hq with ⟨u, huP, hu_tendsto⟩
  rcases q with ⟨⟨lam, x⟩, μ⟩
  let lam_n : ℕ → ℝ := fun n => (u n).1.1
  let x_n : ℕ → (Fin n → ℝ) := fun n => (u n).1.2
  let μ_n : ℕ → ℝ := fun n => (u n).2
  have hu_tendsto' :
      Filter.Tendsto u Filter.atTop (𝓝 (lam, x) ×ˢ 𝓝 μ) := by
    simpa [nhds_prod_eq] using hu_tendsto
  have hlim_fst :
      Filter.Tendsto (fun n => (u n).1) Filter.atTop (𝓝 (lam, x)) :=
    (Filter.Tendsto.fst hu_tendsto')
  have hlim_fst' :
      Filter.Tendsto (fun n => (u n).1) Filter.atTop (𝓝 lam ×ˢ 𝓝 x) := by
    simpa [nhds_prod_eq] using hlim_fst
  have hlim_lam : Filter.Tendsto lam_n Filter.atTop (𝓝 lam) := by
    simpa [lam_n] using (Filter.Tendsto.fst hlim_fst')
  have hlim_x : Filter.Tendsto x_n Filter.atTop (𝓝 x) := by
    simpa [x_n] using (Filter.Tendsto.snd hlim_fst')
  have hlim_mu : Filter.Tendsto μ_n Filter.atTop (𝓝 μ) := by
    simpa [μ_n] using (Filter.Tendsto.snd hu_tendsto')
  have hmemP : ∀ n, ((lam_n n, x_n n), μ_n n) ∈ P := by
    intro n
    simpa [lam_n, x_n, μ_n] using huP n
  have hlam_nonneg : 0 ≤ lam := by
    have hmemIci : ∀ n, lam_n n ∈ Set.Ici (0 : ℝ) := by
      intro n
      have hq' : ((lam_n n, x_n n), μ_n n) ∈ P := hmemP n
      have hle : 0 ≤ (lam_n n) := by
        simpa [h, P] using
          (mem_P_imp_lam_nonneg (f := f) (q := ((lam_n n, x_n n), μ_n n)) hq')
      exact hle
    have hclosed : IsClosed (Set.Ici (0 : ℝ)) := isClosed_Ici
    have hmem_lim :
        lam ∈ Set.Ici (0 : ℝ) :=
      hclosed.mem_of_tendsto hlim_lam (Filter.Eventually.of_forall hmemIci)
    exact hmem_lim
  by_cases hlam_pos : 0 < lam
  · have hpos_eventually : ∀ᶠ n : ℕ in Filter.atTop, 0 < lam_n n := by
      have hlim_lower := (tendsto_order.1 hlim_lam).1
      have hlt : lam / 2 < lam := by linarith
      have hlt_event : ∀ᶠ n : ℕ in Filter.atTop, lam / 2 < lam_n n := hlim_lower _ hlt
      have hhalfpos : 0 < lam / 2 := by linarith
      filter_upwards [hlt_event] with n hn
      exact lt_trans hhalfpos hn
    let v : ℕ → (Fin n → ℝ) × ℝ :=
      fun n => ((lam_n n)⁻¹ • x_n n, μ_n n / lam_n n)
    have hlim_inv : Filter.Tendsto (fun n => (lam_n n)⁻¹) Filter.atTop (𝓝 (lam⁻¹)) :=
      (Filter.Tendsto.inv₀ hlim_lam (ne_of_gt hlam_pos))
    have hsmul : Filter.Tendsto (fun n => (lam_n n)⁻¹ • x_n n) Filter.atTop (𝓝 (lam⁻¹ • x)) := by
      have hpair :
          Filter.Tendsto (fun n => ((lam_n n)⁻¹, x_n n)) Filter.atTop (𝓝 (lam⁻¹, x)) := by
        simpa [nhds_prod_eq] using hlim_inv.prodMk hlim_x
      have hcont : Continuous fun p : ℝ × (Fin n → ℝ) => p.1 • p.2 := by
        simpa using (continuous_smul : Continuous fun p : ℝ × (Fin n → ℝ) => p.1 • p.2)
      exact (hcont.tendsto (lam⁻¹, x)).comp hpair
    have hlim_div :
        Filter.Tendsto (fun n => μ_n n / lam_n n) Filter.atTop (𝓝 (μ / lam)) := by
      have hmul := hlim_mu.mul hlim_inv
      simpa [div_eq_mul_inv] using hmul
    have hv_tendsto :
        Filter.Tendsto v Filter.atTop (𝓝 ((lam⁻¹ • x), μ / lam)) := by
      have hv' :
          Filter.Tendsto v Filter.atTop (𝓝 (lam⁻¹ • x) ×ˢ 𝓝 (μ / lam)) :=
        hsmul.prodMk hlim_div
      simpa [nhds_prod_eq] using hv'
    have hmem_epi :
        ∀ᶠ k : ℕ in Filter.atTop, v k ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) f := by
      filter_upwards [hpos_eventually] with k hkpos
      have hq' : h (lam_n k) (x_n k) ≤ (μ_n k : EReal) := by
        have hq'' : ((lam_n k, x_n k), μ_n k) ∈ P := hmemP k
        simpa [P] using hq''
      have hle :
          (lam_n k : EReal) * f ((lam_n k)⁻¹ • x_n k) ≤ (μ_n k : EReal) := by
        simpa [h, hkpos] using hq'
      have hmul :
          ((lam_n k)⁻¹ : EReal) * ((lam_n k : EReal) * f ((lam_n k)⁻¹ • x_n k)) ≤
            ((lam_n k)⁻¹ : EReal) * (μ_n k : EReal) := by
        have hnonneg : (0 : EReal) ≤ ((lam_n k)⁻¹ : EReal) := by
          exact (EReal.coe_le_coe_iff).2 (le_of_lt (inv_pos.mpr hkpos))
        exact mul_le_mul_of_nonneg_left hle hnonneg
      have hleft :
          ((lam_n k)⁻¹ : EReal) * ((lam_n k : EReal) * f ((lam_n k)⁻¹ • x_n k)) =
            f ((lam_n k)⁻¹ • x_n k) := by
        have hcancel :=
          section13_mul_inv_mul_cancel_pos_real (a := lam_n k) hkpos
            (z := f ((lam_n k)⁻¹ • x_n k))
        simpa [mul_assoc] using hcancel
      have hright :
          ((lam_n k)⁻¹ : EReal) * (μ_n k : EReal) = (μ_n k / lam_n k : EReal) := by
        calc
          ((lam_n k)⁻¹ : EReal) * (μ_n k : EReal) =
              (μ_n k : EReal) * ((lam_n k)⁻¹ : EReal) := by
                simp [mul_comm]
          _ = (μ_n k / lam_n k : EReal) := by
                simp [div_eq_mul_inv]
      have hle' :
          f ((lam_n k)⁻¹ • x_n k) ≤ (μ_n k / lam_n k : EReal) := by
        have hle'' :
            f ((lam_n k)⁻¹ • x_n k) ≤ ((lam_n k)⁻¹ : EReal) * (μ_n k : EReal) := by
          simpa [hleft] using hmul
        simpa [hright] using hle''
      simpa [v, mem_epigraph_univ_iff] using hle'
    have hclosed_epi :
        IsClosed (epigraph (S := (Set.univ : Set (Fin n → ℝ))) f) :=
      isClosed_epigraph_univ_of_lowerSemicontinuous (hf := hf_closed.2)
    have hlimit_mem :
        (lam⁻¹ • x, μ / lam) ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) f :=
      hclosed_epi.mem_of_tendsto hv_tendsto hmem_epi
    have hle : f (lam⁻¹ • x) ≤ (μ / lam : EReal) := by
      simpa [mem_epigraph_univ_iff] using hlimit_mem
    have hmul :
        (lam : EReal) * f (lam⁻¹ • x) ≤ (lam : EReal) * ((μ / lam : ℝ) : EReal) :=
      mul_le_mul_of_nonneg_left hle (by exact_mod_cast (le_of_lt hlam_pos))
    have hright : (lam : EReal) * ((μ / lam : ℝ) : EReal) = (μ : EReal) := by
      have hreal : (lam : ℝ) * (μ / lam) = μ := by
        field_simp [hlam_pos.ne']
      exact_mod_cast hreal
    have hle' :
        (lam : EReal) * f (lam⁻¹ • x) ≤ (μ : EReal) := by
      simpa [hright] using hmul
    have hrepr : h lam x = (lam : EReal) * f (lam⁻¹ • x) := by
      simp [h, hlam_pos]
    simpa [P, hrepr] using hle'
  · have hlam_zero : lam = 0 := by
      have hle : lam ≤ 0 := le_of_not_gt hlam_pos
      exact le_antisymm hle hlam_nonneg
    have hdot : ∀ y ∈ C, dotProduct x y ≤ μ := by
      intro y hy
      have hineq :
          ∀ n, dotProduct (x_n n) y ≤ μ_n n + lam_n n * (fStar y).toReal := by
        intro n
        have hq' : ((lam_n n, x_n n), μ_n n) ∈ P := hmemP n
        have hdot' :=
          dotProduct_le_mu_add_lam_mul_fStar_toReal_of_mem_P (f := f) hf_nonneg hf_closed hf0
            (q := ((lam_n n, x_n n), μ_n n)) hq' y hy
        simpa [lam_n, x_n, μ_n, fStar, C, h, P] using hdot'
      have hcont :
          Continuous fun x' : Fin n → ℝ => (dotProduct y x' : ℝ) := by
        simpa using (continuous_dotProduct_const (x := y))
      have hlim_left :
          Filter.Tendsto (fun n => dotProduct (x_n n) y) Filter.atTop (𝓝 (dotProduct x y)) := by
        have hlim' :
            Filter.Tendsto (fun n => dotProduct y (x_n n)) Filter.atTop (𝓝 (dotProduct y x)) :=
          (hcont.tendsto _).comp hlim_x
        simpa [dotProduct_comm] using hlim'
      have hlim_mul :
          Filter.Tendsto (fun n => lam_n n * (fStar y).toReal) Filter.atTop
            (𝓝 (lam * (fStar y).toReal)) :=
        hlim_lam.mul (tendsto_const_nhds (x := (fStar y).toReal))
      have hlim_right :
          Filter.Tendsto (fun n => μ_n n + lam_n n * (fStar y).toReal) Filter.atTop
            (𝓝 (μ + lam * (fStar y).toReal)) :=
        hlim_mu.add hlim_mul
      have hle :
          dotProduct x y ≤ μ + lam * (fStar y).toReal :=
        le_of_tendsto_of_tendsto hlim_left hlim_right
          (Filter.Eventually.of_forall hineq)
      simpa [hlam_zero, mul_zero, add_zero] using hle
    have hsupp_le :
        supportFunctionEReal C x ≤ (μ : EReal) := by
      have hdot' : ∀ y ∈ C, dotProduct y x ≤ μ := by
        intro y hy
        simpa [dotProduct_comm] using hdot y hy
      exact (section13_supportFunctionEReal_le_coe_iff (C := C) (y := x) (μ := μ)).2 hdot'
    have hproper :
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f :=
      properConvexFunctionOn_of_nonneg_closedConvex_zero (f := f) hf_nonneg hf_closed hf0
    have hsupp :
        supportFunctionEReal C = recessionFunction f := by
      simpa [C, fStar] using
        (section13_supportFunctionEReal_dom_fenchelConjugate_eq_recessionFunction (n := n)
          (f := f) hf_closed hproper)
    have hrec : recessionFunction f x ≤ (μ : EReal) := by
      simpa [hsupp] using hsupp_le
    have hrepr : h lam x = recessionFunction f x := by
      simp [h, hlam_zero]
    simpa [P, hrepr] using hrec


end Section15
end Chap03
