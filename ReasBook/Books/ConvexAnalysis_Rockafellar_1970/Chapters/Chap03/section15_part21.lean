/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yijie Wang, Yunxi Duan, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part20
section Chap03
section Section15

open scoped BigOperators
open scoped Pointwise


/-- Bipolarity for `polarSetProd`, using the closed convex bipolar theorem. -/
lemma polarSetProd_bipolar_eq_closure_of_convex_zeroMem {n : ℕ}
    (C : Set ((Fin n → ℝ) × ℝ)) (hCconv : Convex ℝ C)
    (hC0 : (0 : (Fin n → ℝ) × ℝ) ∈ C) :
    polarSetProd (n := n) (polarSetProd (n := n) C) = closure C := by
  classical
  have hclosed : IsClosed (closure C) := isClosed_closure
  have hconv : Convex ℝ (closure C) := hCconv.closure
  have h0 : (0 : (Fin n → ℝ) × ℝ) ∈ closure C := subset_closure hC0
  have hbipolar :
      {x : (Fin n → ℝ) × ℝ |
          ∀ φ ∈ polar (E := (Fin n → ℝ) × ℝ) (closure C), φ x ≤ 1} =
        closure C :=
    section14_bipolar_eq_of_closed_convex (E := (Fin n → ℝ) × ℝ) hclosed hconv h0
  have hbipolar' :
      polarSetProd (n := n) (polarSetProd (n := n) (closure C)) = closure C := by
    calc
      polarSetProd (n := n) (polarSetProd (n := n) (closure C)) =
          {x : (Fin n → ℝ) × ℝ |
              ∀ φ ∈ polar (E := (Fin n → ℝ) × ℝ) (closure C), φ x ≤ 1} := by
        simpa using
          (bipolar_dualSet_eq_polarSetProd_polarSetProd (n := n) (C := closure C)).symm
      _ = closure C := hbipolar
  have hpolar_cl : polarSetProd (n := n) (closure C) = polarSetProd (n := n) C :=
    polarSetProd_closure_eq (n := n) C
  calc
    polarSetProd (n := n) (polarSetProd (n := n) C) =
        polarSetProd (n := n) (polarSetProd (n := n) (closure C)) := by
          simp [hpolar_cl]
    _ = closure C := hbipolar'

/-- Nonnegativity rules out the value `⊥`. -/
lemma hbot_of_nonneg {n : ℕ} {f : (Fin n → ℝ) → EReal} (hf_nonneg : ∀ x, 0 ≤ f x) :
    ∀ x, f x ≠ (⊥ : EReal) := by
  intro x hfx
  have h0le : (0 : EReal) ≤ (⊥ : EReal) := by
    simpa [hfx] using (hf_nonneg x)
  have h0eq : (0 : EReal) = (⊥ : EReal) := (le_bot_iff).1 h0le
  simp at h0eq

/-- If a reflected point lies in the polar of the epigraph and `f 0 = 0`,
then the height is nonnegative. -/
lemma mu_nonneg_of_vertReflect_mem_polarSetProd_epigraph {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hf0 : f 0 = 0) {xStar : Fin n → ℝ} {μ : ℝ}
    (hmem :
      vertReflect (n := n) (xStar, μ) ∈
        polarSetProd (n := n) (epigraph (S := (Set.univ : Set (Fin n → ℝ))) f)) :
    0 ≤ μ := by
  by_contra hμ
  have hμlt : μ < 0 := lt_of_not_ge hμ
  have hnegpos : 0 < -μ := by linarith
  set t : ℝ := 2 / (-μ)
  have htpos : 0 < t := by
    have htwo : 0 < (2 : ℝ) := by norm_num
    exact div_pos htwo hnegpos
  have ht_nonneg : 0 ≤ t := le_of_lt htpos
  have hmem_epi :
      ((0 : Fin n → ℝ), t) ∈
        epigraph (S := (Set.univ : Set (Fin n → ℝ))) f := by
    have hle : f (0 : Fin n → ℝ) ≤ (t : EReal) := by
      have : (0 : EReal) ≤ (t : EReal) := by exact_mod_cast ht_nonneg
      simpa [hf0] using this
    simpa [mem_epigraph_univ_iff] using hle
  have hineq := hmem (0, t) hmem_epi
  have hineq' : t * (-μ) ≤ 1 := by
    have hdot : ((0 : Fin n → ℝ) ⬝ᵥ xStar : ℝ) = 0 := by simp
    simpa [vertReflect, hdot] using hineq
  have hμne : -μ ≠ 0 := by linarith
  have hmul : t * (-μ) = 2 := by
    dsimp [t]
    have hμne' : μ ≠ 0 := by linarith
    field_simp [hμne']
  have hcontr : (2 : ℝ) ≤ 1 := by
    simp [hmul] at hineq'
  linarith


end Section15
end Chap03
