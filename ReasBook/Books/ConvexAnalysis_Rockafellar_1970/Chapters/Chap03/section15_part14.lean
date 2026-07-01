/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yijie Wang, Yunxi Duan, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part13

section Chap03
section Section15

open scoped BigOperators
open scoped Pointwise
open scoped Topology
open Filter

/-- The unit sublevel of a closed gauge is polar to the unit sublevel of its polar gauge. -/
lemma unitSublevel_polarGauge_eq_polarSet_and_bipolar {n : ℕ} {k : (Fin n → ℝ) → EReal}
    (hk : IsClosedGauge k) :
    let C : Set (Fin n → ℝ) := {x | k x ≤ (1 : EReal)}
    let CStar : Set (Fin n → ℝ) := {xStar | polarGauge k xStar ≤ (1 : EReal)}
    CStar = {xStar | ∀ x ∈ C, (x ⬝ᵥ xStar : ℝ) ≤ 1} ∧
      C = {x | ∀ xStar ∈ CStar, (x ⬝ᵥ xStar : ℝ) ≤ 1} := by
  classical
  dsimp
  set C : Set (Fin n → ℝ) := {x | k x ≤ (1 : EReal)} with hCdef
  set CStar : Set (Fin n → ℝ) := {xStar | polarGauge k xStar ≤ (1 : EReal)} with hCStardef
  have hCStar :
      CStar = {xStar | ∀ x ∈ C, (x ⬝ᵥ xStar : ℝ) ≤ 1} := by
    have h :=
      unitSublevel_polarGauge_eq_polarSet (k := k) hk.1
    dsimp at h
    simpa [hCdef, hCStardef] using h
  have hkStar : IsGauge (polarGauge k) := polarGauge_isGauge (k := k)
  have hCStar' :
      {x | polarGauge (polarGauge k) x ≤ (1 : EReal)} =
        {x | ∀ xStar ∈ CStar, (x ⬝ᵥ xStar : ℝ) ≤ 1} := by
    have h :=
      unitSublevel_polarGauge_eq_polarSet (k := polarGauge k) hkStar
    dsimp at h
    have h' :
        {x | polarGauge (polarGauge k) x ≤ (1 : EReal)} =
          {x | ∀ xStar ∈ CStar, (xStar ⬝ᵥ x : ℝ) ≤ 1} := by
      simpa [hCStardef] using h
    ext x; constructor
    · intro hx
      have hx' :
          x ∈ {x | ∀ xStar ∈ CStar, (xStar ⬝ᵥ x : ℝ) ≤ 1} := by
        simpa [h'] using hx
      intro xStar hxStar
      have hx'' := hx' xStar hxStar
      simpa [dotProduct_comm] using hx''
    · intro hx
      have hx' :
          x ∈ {x | ∀ xStar ∈ CStar, (xStar ⬝ᵥ x : ℝ) ≤ 1} := by
        intro xStar hxStar
        have hx'' := hx xStar hxStar
        simpa [dotProduct_comm] using hx''
      simpa [h'.symm] using hx'
  have hpol_invol :
      polarGauge (polarGauge k) = k :=
    polarGauge_involutive_of_isGauge_isClosed_epigraph hk.1 hk.2
  have hC :
      C = {x | ∀ xStar ∈ CStar, (x ⬝ᵥ xStar : ℝ) ≤ 1} := by
    simpa [hCdef, hpol_invol] using hCStar'
  exact ⟨hCStar, hC⟩

/-- Recover `(p f)^{1/p}` and `(q f^*)^{1/q}` from the power representation. -/
lemma k_eq_closedGauge_from_cor1531 {n : ℕ} {p q : ℝ} (hp : 1 < p)
    (hpq : (1 / p) + (1 / q) = 1) {f : (Fin n → ℝ) → EReal}
    {k0 : (Fin n → ℝ) → EReal} (hk0 : IsClosedGauge k0)
    (hfk0 : f = fun x => ((1 / p : ℝ) : EReal) * phiPow p (k0 x))
    (hfc : ∀ xStar : Fin n → ℝ,
      fenchelConjugate n f xStar =
        ((1 / q : ℝ) : EReal) * phiPow q (polarGauge k0 xStar)) :
    (fun x => phiPow (1 / p) (((p : ℝ) : EReal) * f x)) = k0 ∧
      (fun xStar =>
        phiPow (1 / q) (((q : ℝ) : EReal) * fenchelConjugate n f xStar)) = polarGauge k0 := by
  classical
  have hp_pos : 0 < p := by linarith
  have h_one_div_lt : (1 / p : ℝ) < 1 := by
    have h :=
      one_div_lt_one_div_of_lt (a := (1 : ℝ)) (b := p) (ha := by norm_num) (h := hp)
    simpa using h
  have hq_inv_pos : 0 < (1 / q : ℝ) := by
    have hq_inv : (1 / q : ℝ) = 1 - 1 / p := by linarith [hpq]
    have hpos : 0 < (1 - 1 / p : ℝ) := by linarith [h_one_div_lt]
    simpa [hq_inv] using hpos
  have hq_pos : 0 < q := (one_div_pos.mp hq_inv_pos)
  constructor
  · funext x
    have hk0_nonneg : (0 : EReal) ≤ k0 x := hk0.1.2.1 x
    have hpne : p ≠ 0 := by linarith
    calc
      phiPow (1 / p) (((p : ℝ) : EReal) * f x) =
          phiPow (1 / p) (((p : ℝ) : EReal) * (((1 / p : ℝ) : EReal) * phiPow p (k0 x))) := by
        rw [hfk0]
      _ = phiPow (1 / p) (phiPow p (k0 x)) := by
        have hmul : ((p : ℝ) : EReal) * ((p⁻¹ : ℝ) : EReal) = (1 : EReal) := by
          have hmul : (p * p⁻¹ : ℝ) = 1 := by
            field_simp [hpne]
          have hmul' : ((p * p⁻¹ : ℝ) : EReal) = (1 : EReal) := by
            exact_mod_cast hmul
          simpa [EReal.coe_mul] using hmul'
        calc
          phiPow (1 / p) (((p : ℝ) : EReal) * (((1 / p : ℝ) : EReal) * phiPow p (k0 x))) =
              phiPow (1 / p) (((p : ℝ) : EReal) * (((p⁻¹ : ℝ) : EReal) * phiPow p (k0 x))) := by
                rw [one_div]
          _ = phiPow (1 / p) (((p : ℝ) : EReal) * ((p⁻¹ : ℝ) : EReal) * phiPow p (k0 x)) := by
                rw [mul_assoc]
          _ = phiPow (1 / p) ((1 : EReal) * phiPow p (k0 x)) := by
                rw [hmul]
          _ = phiPow (1 / p) (phiPow p (k0 x)) := by
                rw [one_mul]
      _ = k0 x := phiPow_one_div_comp_phiPow_of_nonneg (p := p) hp_pos hk0_nonneg
  · funext xStar
    have hpol_nonneg : (0 : EReal) ≤ polarGauge k0 xStar := polarGauge_nonneg (k := k0) xStar
    have hqne : q ≠ 0 := by linarith
    calc
      phiPow (1 / q) (((q : ℝ) : EReal) * fenchelConjugate n f xStar) =
          phiPow (1 / q) (((q : ℝ) : EReal) *
              (((1 / q : ℝ) : EReal) * phiPow q (polarGauge k0 xStar))) := by
        rw [hfc]
      _ = phiPow (1 / q) (phiPow q (polarGauge k0 xStar)) := by
        have hmul : ((q : ℝ) : EReal) * ((q⁻¹ : ℝ) : EReal) = (1 : EReal) := by
          have hmul : (q * q⁻¹ : ℝ) = 1 := by
            field_simp [hqne]
          have hmul' : ((q * q⁻¹ : ℝ) : EReal) = (1 : EReal) := by
            exact_mod_cast hmul
          simpa [EReal.coe_mul] using hmul'
        calc
          phiPow (1 / q) (((q : ℝ) : EReal) *
              (((1 / q : ℝ) : EReal) * phiPow q (polarGauge k0 xStar))) =
              phiPow (1 / q) (((q : ℝ) : EReal) *
                (((q⁻¹ : ℝ) : EReal) * phiPow q (polarGauge k0 xStar))) := by
                rw [one_div]
          _ = phiPow (1 / q) (((q : ℝ) : EReal) * ((q⁻¹ : ℝ) : EReal) * phiPow q (polarGauge k0 xStar)) := by
                rw [mul_assoc]
          _ = phiPow (1 / q) ((1 : EReal) * phiPow q (polarGauge k0 xStar)) := by
                rw [hmul]
          _ = phiPow (1 / q) (phiPow q (polarGauge k0 xStar)) := by
                rw [one_mul]
      _ = polarGauge k0 xStar :=
        phiPow_one_div_comp_phiPow_of_nonneg (p := q) hq_pos hpol_nonneg

end Section15
end Chap03
