/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Weiran Shi, Yunxi Duan, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section16_part14
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section16_part7
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section12_part9
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section05_part8

section Chap03
section Section16

open scoped BigOperators
open scoped Pointwise

/-- The conjugate of `x ↦ ‖x - a‖` is the unit-ball indicator plus a linear term. -/
lemma section16_fenchelConjugate_norm_sub_eq_indicator_add_dot {n : ℕ} (a : Fin n → ℝ) :
    fenchelConjugate n (fun x => ((‖x - a‖ : ℝ) : EReal)) =
      fun xStar : Fin n → ℝ =>
        (if l1Norm xStar ≤ (1 : ℝ) then (0 : EReal) else (⊤ : EReal)) +
          ((dotProduct a xStar : ℝ) : EReal) := by
  classical
  funext xStar
  have h :=
    congrArg (fun g => g xStar)
      (section16_fenchelConjugate_translate (n := n)
        (h := fun x : Fin n → ℝ => ((‖x‖ : ℝ) : EReal)) a)
  simpa [section16_fenchelConjugate_norm_eq_indicator_unitBall] using h

/-- Translating the norm preserves proper convexity on `Set.univ`. -/
lemma section16_properConvexFunctionOn_norm_sub {n : ℕ} (a : Fin n → ℝ) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
      (fun x => ((‖x - a‖ : ℝ) : EReal)) := by
  simpa using
    (properConvexFunctionOn_translate (n := n) (a := a)
      (f := fun x : Fin n → ℝ => ((‖x‖ : ℝ) : EReal))
      (properConvexFunctionOn_norm (n := n)))

/-- The effective domain of `x ↦ ‖x - a‖` is all of `ℝ^n`. -/
lemma section16_closure_effectiveDomain_norm_sub_eq_univ {n : ℕ} (a : Fin n → ℝ) :
    closure (effectiveDomain (Set.univ : Set (Fin n → ℝ))
      (fun x => ((‖x - a‖ : ℝ) : EReal))) = (Set.univ : Set (Fin n → ℝ)) := by
  have hdom :
      effectiveDomain (Set.univ : Set (Fin n → ℝ))
        (fun x => ((‖x - a‖ : ℝ) : EReal)) = (Set.univ : Set (Fin n → ℝ)) := by
    ext x
    simp [effectiveDomain_eq]
  simp [hdom]

/-- Text 16.5.1: Let `f(x) = max { ‖x - aᵢ‖ | i = 1, …, m }`, where `a₁, …, aₘ ∈ ℝⁿ`.

For each `x⋆`, the conjugate `f⋆(x⋆)` is the minimum of

`λ₁ ⟪a₁, x₁⋆⟫ + ⋯ + λₘ ⟪aₘ, xₘ⋆⟫`

over all `xᵢ⋆` and `λᵢ` satisfying

- `λ₁ x₁⋆ + ⋯ + λₘ xₘ⋆ = x⋆`,
- `‖xᵢ⋆‖ ≤ 1`,
- `λᵢ ≥ 0` and `λ₁ + ⋯ + λₘ = 1`. -/
theorem section16_fenchelConjugate_sSup_norm_sub_points_eq_sInf {n m : ℕ} (a : Fin m → Fin n → ℝ)
    (hm : 0 < m) :
    let f : (Fin n → ℝ) → EReal :=
      fun x => sSup (Set.range fun i : Fin m => ((‖x - a i‖ : ℝ) : EReal))
    ∀ xStar : Fin n → ℝ,
      let S : Set EReal :=
        {r |
          ∃ (lam : Fin m → ℝ) (xStar_i : Fin m → Fin n → ℝ),
            (∀ i, 0 ≤ lam i) ∧
              (∑ i, lam i) = 1 ∧
                (∑ i, (lam i) • (xStar_i i)) = xStar ∧
                  (∀ i, l1Norm (xStar_i i) ≤ (1 : ℝ)) ∧
                    r = ((∑ i, lam i * (dotProduct (a i) (xStar_i i) : ℝ) : ℝ) : EReal)}
      fenchelConjugate n f xStar = sInf S ∧ (S.Nonempty → ∃ r, r ∈ S ∧ sInf S = r) := by
  classical
  simpa using (by
    intro xStar
    haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    let f_i : Fin m → (Fin n → ℝ) → EReal := fun i x => ((‖x - a i‖ : ℝ) : EReal)
    let S : Set EReal :=
      {r |
        ∃ (lam : Fin m → ℝ) (xStar_i : Fin m → Fin n → ℝ),
          (∀ i, 0 ≤ lam i) ∧
            (∑ i, lam i) = 1 ∧
              (∑ i, (lam i) • (xStar_i i)) = xStar ∧
                (∀ i, l1Norm (xStar_i i) ≤ (1 : ℝ)) ∧
                  r = ((∑ i, lam i * (dotProduct (a i) (xStar_i i) : ℝ) : ℝ) : EReal)}
    let S0 : Set EReal :=
      {r |
        ∃ (lam : Fin m → ℝ) (xStar_i : Fin m → Fin n → ℝ),
          (∀ i, 0 ≤ lam i) ∧
            (∑ i, lam i) = 1 ∧
              (∑ i, (lam i) • (xStar_i i)) = xStar ∧
                r = ∑ i, ((lam i : ℝ) : EReal) * fenchelConjugate n (f_i i) (xStar_i i)}
    have hf :
        ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f_i i) := by
      intro i
      simpa [f_i] using (section16_properConvexFunctionOn_norm_sub (a := a i))
    have hC :
        ∀ i, closure (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f_i i)) =
          (Set.univ : Set (Fin n → ℝ)) := by
      intro i
      simpa [f_i] using (section16_closure_effectiveDomain_norm_sub_eq_univ (a := a i))
    have hthm :=
      section16_fenchelConjugate_sSup_eq_convexHullFunctionFamily_of_finite_of_closure_effectiveDomain_eq
        (n := n) (ι := Fin m) (f := f_i) hf (C := Set.univ) hC
    have hxS0 :
        fenchelConjugate n (fun x => sSup (Set.range fun i => f_i i x)) xStar = sInf S0 := by
      simpa [S0] using (hthm.2 xStar).1
    have hatt0 : ∃ r, r ∈ S0 ∧ sInf S0 = r := by
      simpa [S0] using (hthm.2 xStar).2
    have hsubset1 : S ⊆ S0 := by
      intro r hr
      rcases hr with ⟨lam, xStar_i, hlam, hsum, hsumx, hball, rfl⟩
      refine ⟨lam, xStar_i, hlam, hsum, hsumx, ?_⟩
      have hsum_coe :
          ((∑ i, lam i * (dotProduct (a i) (xStar_i i) : ℝ) : ℝ) : EReal) =
            ∑ i, ((lam i : ℝ) : EReal) * ((dotProduct (a i) (xStar_i i) : ℝ) : EReal) := by
        simpa using
          (section16_coe_finset_sum (s := (Finset.univ : Finset (Fin m)))
            (b := fun i : Fin m => lam i * (dotProduct (a i) (xStar_i i) : ℝ)))
      calc
        ((∑ i, lam i * (dotProduct (a i) (xStar_i i) : ℝ) : ℝ) : EReal)
            = ∑ i, ((lam i : ℝ) : EReal) * ((dotProduct (a i) (xStar_i i) : ℝ) : EReal) := hsum_coe
        _ = ∑ i, ((lam i : ℝ) : EReal) * fenchelConjugate n (f_i i) (xStar_i i) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hballi : l1Norm (xStar_i i) ≤ (1 : ℝ) := hball i
            simp [section16_fenchelConjugate_norm_sub_eq_indicator_add_dot, f_i, hballi]
    have hsubset2 : S0 ⊆ insert ⊤ S := by
      intro r hr
      rcases hr with ⟨lam, xStar_i, hlam, hsum, hsumx, rfl⟩
      let term : Fin m → EReal := fun i =>
        ((lam i : ℝ) : EReal) * fenchelConjugate n (f_i i) (xStar_i i)
      have hterm :
          ∀ i,
            term i =
              ((lam i : ℝ) : EReal) *
                ((if l1Norm (xStar_i i) ≤ (1 : ℝ) then (0 : EReal) else (⊤ : EReal)) +
                  ((dotProduct (a i) (xStar_i i) : ℝ) : EReal)) := by
        intro i
        simp [term, section16_fenchelConjugate_norm_sub_eq_indicator_add_dot, f_i]
      by_cases hbad : ∃ i, lam i ≠ 0 ∧ ¬ l1Norm (xStar_i i) ≤ (1 : ℝ)
      · rcases hbad with ⟨i0, hlam0, hball0⟩
        have hpos : 0 < lam i0 := lt_of_le_of_ne (hlam i0) (Ne.symm hlam0)
        have hposE : (0 : EReal) < ((lam i0 : ℝ) : EReal) := (EReal.coe_pos).2 hpos
        have htop :
            ((if l1Norm (xStar_i i0) ≤ (1 : ℝ) then (0 : EReal) else (⊤ : EReal)) +
              ((dotProduct (a i0) (xStar_i i0) : ℝ) : EReal)) = ⊤ := by
          simp [hball0]
        have hterm_top : term i0 = ⊤ := by
          calc
            term i0 =
                ((lam i0 : ℝ) : EReal) *
                  ((if l1Norm (xStar_i i0) ≤ (1 : ℝ) then (0 : EReal) else (⊤ : EReal)) +
                    ((dotProduct (a i0) (xStar_i i0) : ℝ) : EReal)) := hterm i0
            _ = ⊤ := by
                  simpa [htop] using
                    (EReal.mul_top_of_pos (x := ((lam i0 : ℝ) : EReal)) hposE)
        have hbot :
            ∀ j ∈ (Finset.univ : Finset (Fin m)), term j ≠ ⊥ := by
          intro j hj
          have hne_bot :
              (if l1Norm (xStar_i j) ≤ (1 : ℝ) then (0 : EReal) else (⊤ : EReal)) +
                ((dotProduct (a j) (xStar_i j) : ℝ) : EReal) ≠ (⊥ : EReal) := by
            by_cases hball : l1Norm (xStar_i j) ≤ (1 : ℝ)
            · simp [hball]
            · simp [hball]
          have htermj_ne_bot :
              ((lam j : ℝ) : EReal) *
                ((if l1Norm (xStar_i j) ≤ (1 : ℝ) then (0 : EReal) else (⊤ : EReal)) +
                  ((dotProduct (a j) (xStar_i j) : ℝ) : EReal)) ≠ (⊥ : EReal) := by
            refine (EReal.mul_ne_bot ((lam j : ℝ) : EReal)
              ((if l1Norm (xStar_i j) ≤ (1 : ℝ) then (0 : EReal) else (⊤ : EReal)) +
                ((dotProduct (a j) (xStar_i j) : ℝ) : EReal))).2 ?_
            refine ⟨?_, ?_, ?_, ?_⟩
            · left
              exact EReal.coe_ne_bot _
            · right
              exact hne_bot
            · left
              exact EReal.coe_ne_top _
            · left
              exact (EReal.coe_nonneg).2 (hlam j)
          simpa [hterm j] using htermj_ne_bot
        have hsum_top : (∑ i, term i) = (⊤ : EReal) := by
          have hi0' : i0 ∈ (Finset.univ : Finset (Fin m)) := by simp
          exact
            sum_eq_top_of_term_top (s := (Finset.univ : Finset (Fin m)))
              (f := term) (i := i0) hi0' hterm_top hbot
        have hr_top :
            (∑ i, ((lam i : ℝ) : EReal) * fenchelConjugate n (f_i i) (xStar_i i)) = ⊤ := by
          simpa [term] using hsum_top
        exact (Set.mem_insert_iff).2 (Or.inl hr_top)
      · have hgood : ∀ i, lam i = 0 ∨ l1Norm (xStar_i i) ≤ (1 : ℝ) := by
          intro i
          by_cases hzero : lam i = 0
          · exact Or.inl hzero
          · have : l1Norm (xStar_i i) ≤ (1 : ℝ) := by
              by_contra hball
              exact hbad ⟨i, hzero, hball⟩
            exact Or.inr this
        let xStar_i' : Fin m → Fin n → ℝ := fun i =>
          if l1Norm (xStar_i i) ≤ (1 : ℝ) then xStar_i i else 0
        have hball' : ∀ i, l1Norm (xStar_i' i) ≤ (1 : ℝ) := by
          intro i
          by_cases hball : l1Norm (xStar_i i) ≤ (1 : ℝ)
          · simp [xStar_i', hball]
          · have hx : xStar_i' i = 0 := by
              simp [xStar_i', hball]
            simp [hx, l1Norm]
        have hsumx' : (∑ i, lam i • xStar_i' i) = xStar := by
          have hsumx'' : (∑ i, lam i • xStar_i' i) = ∑ i, lam i • xStar_i i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            by_cases hzero : lam i = 0
            · simp [xStar_i', hzero]
            · have hball : l1Norm (xStar_i i) ≤ (1 : ℝ) := by
                cases hgood i with
                | inl h => exact (hzero h).elim
                | inr h => exact h
              simp [xStar_i', hball]
          simpa [hsumx''] using hsumx
        have hsumr' :
            ∑ i, ((lam i : ℝ) : EReal) *
                ((dotProduct (a i) (xStar_i' i) : ℝ) : EReal) =
              ∑ i, ((lam i : ℝ) : EReal) * fenchelConjugate n (f_i i) (xStar_i i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          by_cases hzero : lam i = 0
          · simp [xStar_i', hzero]
          · have hball : l1Norm (xStar_i i) ≤ (1 : ℝ) := by
              cases hgood i with
              | inl h => exact (hzero h).elim
              | inr h => exact h
            simp [xStar_i', hball, section16_fenchelConjugate_norm_sub_eq_indicator_add_dot, f_i]
        have hsumr'' :
            ((∑ i, lam i * (dotProduct (a i) (xStar_i' i) : ℝ) : ℝ) : EReal) =
              ∑ i, ((lam i : ℝ) : EReal) *
                ((dotProduct (a i) (xStar_i' i) : ℝ) : EReal) := by
          simpa using
            (section16_coe_finset_sum (s := (Finset.univ : Finset (Fin m)))
              (b := fun i : Fin m => lam i * (dotProduct (a i) (xStar_i' i) : ℝ)))
        have hrS :
            ∑ i, ((lam i : ℝ) : EReal) * fenchelConjugate n (f_i i) (xStar_i i) =
              ((∑ i, lam i * (dotProduct (a i) (xStar_i' i) : ℝ) : ℝ) : EReal) := by
          calc
            ∑ i, ((lam i : ℝ) : EReal) * fenchelConjugate n (f_i i) (xStar_i i) =
                ∑ i, ((lam i : ℝ) : EReal) *
                  ((dotProduct (a i) (xStar_i' i) : ℝ) : EReal) := by
                    symm
                    exact hsumr'
            _ = ((∑ i, lam i * (dotProduct (a i) (xStar_i' i) : ℝ) : ℝ) : EReal) := by
                    symm
                    exact hsumr''
        have hrS_mem : (∑ i, ((lam i : ℝ) : EReal) * fenchelConjugate n (f_i i) (xStar_i i)) ∈ S := by
          refine ⟨lam, xStar_i', hlam, hsum, hsumx', hball', ?_⟩
          simp [hrS]
        exact (Set.mem_insert_iff).2 (Or.inr hrS_mem)
    have hsInf : sInf S0 = sInf S := by
      exact le_antisymm (sInf_le_sInf hsubset1) (sInf_le_sInf_of_subset_insert_top hsubset2)
    have hxS :
        fenchelConjugate n (fun x => sSup (Set.range fun i => f_i i x)) xStar = sInf S := by
      simpa [hsInf] using hxS0
    have hatt : S.Nonempty → ∃ r, r ∈ S ∧ sInf S = r := by
      intro hSne
      rcases hatt0 with ⟨r0, hr0, hsInf0⟩
      have hsInfS : sInf S = r0 := by
        simpa [hsInf] using hsInf0
      have hr0_mem : r0 ∈ insert ⊤ S := hsubset2 hr0
      have hsInf_ne_top : sInf S ≠ (⊤ : EReal) := by
        rcases hSne with ⟨rS, hrS⟩
        have hsInf_le : sInf S ≤ rS := sInf_le hrS
        rcases hrS with ⟨lam, xStar_i, _hlam, _hsum, _hsumx, _hball, rfl⟩
        intro htop
        have hsInf_le' := hsInf_le
        simp [htop] at hsInf_le'
      have hr0_ne_top : r0 ≠ (⊤ : EReal) := by
        simpa [hsInfS] using hsInf_ne_top
      have hr0S : r0 ∈ S := by
        rcases (Set.mem_insert_iff).1 hr0_mem with htop | hS
        · exact (hr0_ne_top htop).elim
        · exact hS
      exact ⟨r0, hr0S, hsInfS⟩
    have hxS' := hxS
    have hatt' := hatt
    simp [f_i, S] at hxS' hatt'
    exact ⟨hxS', hatt'⟩)

end Section16
end Chap03
