/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yijie Wang, Yunxi Duan, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part12

section Chap03
section Section15

open scoped BigOperators
open scoped Pointwise
open scoped Topology
open Filter

/-- `phiPow` is inverted by the reciprocal exponent on nonnegative inputs. -/
lemma phiPow_one_div_comp_phiPow_of_nonneg {p : ℝ} (hp : 0 < p) {z : EReal} (hz : 0 ≤ z) :
    phiPow (1 / p) (phiPow p z) = z := by
  classical
  by_cases hz_top : z = ⊤
  · simp [phiPow, hz_top]
  ·
    have hz_ne_bot : z ≠ ⊥ := by
      intro hz_bot
      have h0le : (0 : EReal) ≤ (⊥ : EReal) := by
        have hz' := hz
        rw [hz_bot] at hz'
        exact hz'
      have hbot_lt : (⊥ : EReal) < (0 : EReal) := by
        exact EReal.bot_lt_coe (0 : ℝ)
      exact (not_le_of_gt hbot_lt) h0le
    have hz_coe : (z.toReal : EReal) = z := EReal.coe_toReal (x := z) hz_top hz_ne_bot
    have hz_nonneg : 0 ≤ z.toReal := by
      have : (0 : EReal) ≤ (z.toReal : EReal) := by simpa [hz_coe] using hz
      exact (EReal.coe_le_coe_iff).1 this
    have hphi : phiPow p z = ((Real.rpow z.toReal p : ℝ) : EReal) := by
      simp [phiPow, hz_top, hz_ne_bot, max_eq_left hz_nonneg]
    have hphi' :
        phiPow (1 / p) (phiPow p z) =
          ((Real.rpow (Real.rpow z.toReal p) (1 / p) : ℝ) : EReal) := by
      have hpow_nonneg : 0 ≤ z.toReal ^ p := by
        simpa using (Real.rpow_nonneg hz_nonneg p)
      have hphi'' :
          phiPow (1 / p) ((Real.rpow z.toReal p : ℝ) : EReal) =
            ((Real.rpow (Real.rpow z.toReal p) (1 / p) : ℝ) : EReal) := by
        simp [phiPow]
        rw [max_eq_left hpow_nonneg]
      simpa [hphi] using hphi''
    have hpne : p ≠ 0 := by linarith
    have hpow : Real.rpow (Real.rpow z.toReal p) (1 / p) = z.toReal := by
      simpa [one_div] using (Real.rpow_rpow_inv hz_nonneg hpne)
    have hpow_coe :
        ((Real.rpow (Real.rpow z.toReal p) (1 / p) : ℝ) : EReal) = (z.toReal : EReal) := by
      exact_mod_cast hpow
    calc
      phiPow (1 / p) (phiPow p z) =
          ((Real.rpow (Real.rpow z.toReal p) (1 / p) : ℝ) : EReal) := hphi'
      _ = (z.toReal : EReal) := hpow_coe
      _ = z := hz_coe

/-- `phiPow` with exponent `p` inverts `phiPow (1/p)` on nonnegative inputs. -/
lemma phiPow_comp_phiPow_one_div_of_nonneg {p : ℝ} (hp : 0 < p) {z : EReal} (hz : 0 ≤ z) :
    phiPow p (phiPow (1 / p) z) = z := by
  classical
  by_cases hz_top : z = ⊤
  · simp [phiPow, hz_top]
  ·
    have hz_ne_bot : z ≠ ⊥ := by
      intro hz_bot
      have h0le : (0 : EReal) ≤ (⊥ : EReal) := by
        have hz' := hz
        rw [hz_bot] at hz'
        exact hz'
      have hbot_lt : (⊥ : EReal) < (0 : EReal) := by
        exact EReal.bot_lt_coe (0 : ℝ)
      exact (not_le_of_gt hbot_lt) h0le
    have hz_coe : (z.toReal : EReal) = z := EReal.coe_toReal (x := z) hz_top hz_ne_bot
    have hz_nonneg : 0 ≤ z.toReal := by
      have : (0 : EReal) ≤ (z.toReal : EReal) := by simpa [hz_coe] using hz
      exact (EReal.coe_le_coe_iff).1 this
    have hphi : phiPow (1 / p) z = ((Real.rpow z.toReal (1 / p) : ℝ) : EReal) := by
      simp [phiPow, hz_top, hz_ne_bot, max_eq_left hz_nonneg]
    have hphi' :
        phiPow p (phiPow (1 / p) z) =
          ((Real.rpow (Real.rpow z.toReal (1 / p)) p : ℝ) : EReal) := by
      have hpow_nonneg : 0 ≤ z.toReal ^ p⁻¹ := by
        simpa [one_div] using (Real.rpow_nonneg hz_nonneg (1 / p))
      have hphi'' :
          phiPow p ((Real.rpow z.toReal (1 / p) : ℝ) : EReal) =
            ((Real.rpow (Real.rpow z.toReal (1 / p)) p : ℝ) : EReal) := by
        simp [phiPow]
        rw [max_eq_left hpow_nonneg]
      have hphi' : phiPow p⁻¹ z = ((z.toReal ^ p⁻¹ : ℝ) : EReal) := by
        simpa [one_div] using hphi
      simpa [hphi'] using hphi''
    have hpne : p ≠ 0 := by linarith
    have hpow : Real.rpow (Real.rpow z.toReal (1 / p)) p = z.toReal := by
      simpa [one_div] using (Real.rpow_inv_rpow (x := z.toReal) hz_nonneg hpne)
    have hpow_coe :
        ((Real.rpow (Real.rpow z.toReal (1 / p)) p : ℝ) : EReal) = (z.toReal : EReal) := by
      exact_mod_cast hpow
    calc
      phiPow p (phiPow (1 / p) z) =
          ((Real.rpow (Real.rpow z.toReal (1 / p)) p : ℝ) : EReal) := hphi'
      _ = (z.toReal : EReal) := hpow_coe
      _ = z := hz_coe

/-- The base sublevel of `f` equals the unit sublevel of `k := (p f)^{1/p}` under nonnegativity. -/
lemma sublevel_f_one_div_eq_unitSublevel_k {n : ℕ} {p : ℝ} {f : (Fin n → ℝ) → EReal}
    (hp : 0 < p) (hnonneg : ∀ x, (0 : EReal) ≤ f x) :
    {x | f x ≤ ((1 / p : ℝ) : EReal)} =
      {x | phiPow (1 / p) (((p : ℝ) : EReal) * f x) ≤ (1 : EReal)} := by
  classical
  have hp_ne : p ≠ 0 := by linarith
  have hp_nonneg : (0 : EReal) ≤ ((p : ℝ) : EReal) := by
    exact_mod_cast (le_of_lt hp)
  have hpinv_pos : 0 < (1 / p : ℝ) := one_div_pos.mpr hp
  have hpinv_nonneg : 0 ≤ (1 / p : ℝ) := le_of_lt hpinv_pos
  have hmono_p : Monotone (phiPow p) := phiPow_mono (r := p) (le_of_lt hp)
  have hmono_inv : Monotone (phiPow (1 / p)) := phiPow_mono (r := 1 / p) hpinv_nonneg
  have h1_ne_top : (1 : EReal) ≠ ⊤ := by
    exact (EReal.coe_ne_top (1 : ℝ))
  have h1_ne_bot : (1 : EReal) ≠ ⊥ := by
    exact (EReal.coe_ne_bot (1 : ℝ))
  have hphi_one : phiPow p (1 : EReal) = (1 : EReal) := by
    simp [phiPow, h1_ne_top, h1_ne_bot]
  have hphi_inv_one : phiPow (1 / p) (1 : EReal) = (1 : EReal) := by
    simp [phiPow, h1_ne_top, h1_ne_bot]
  have hphi_inv_one' : phiPow p⁻¹ (1 : EReal) = (1 : EReal) := by
    simp [phiPow, h1_ne_top, h1_ne_bot]
  have hmul_pp : ((p : ℝ) : EReal) * ((p⁻¹ : ℝ) : EReal) = (1 : EReal) := by
    have hmul : (p * p⁻¹ : ℝ) = 1 := by
      field_simp [hp_ne]
    have hmul' : ((p * p⁻¹ : ℝ) : EReal) = (1 : EReal) := by
      exact_mod_cast hmul
    simpa [EReal.coe_mul] using hmul'
  have hmul_pp' : ((p⁻¹ : ℝ) : EReal) * ((p : ℝ) : EReal) = (1 : EReal) := by
    simpa [mul_comm] using hmul_pp
  ext x; constructor
  · intro hx
    have hpf : (((p : ℝ) : EReal) * f x) ≤ (1 : EReal) := by
      have hmul := mul_le_mul_of_nonneg_left hx hp_nonneg
      simpa [one_div, hmul_pp, mul_assoc] using hmul
    have h := hmono_inv hpf
    have h' : phiPow p⁻¹ (((p : ℝ) : EReal) * f x) ≤ phiPow p⁻¹ (1 : EReal) := by
      simpa [one_div] using h
    have h'' : phiPow p⁻¹ (((p : ℝ) : EReal) * f x) ≤ (1 : EReal) := by
      simpa [hphi_inv_one'] using h'
    simpa [one_div] using h''
  · intro hx
    have hpf : phiPow p (phiPow (1 / p) (((p : ℝ) : EReal) * f x)) ≤ (1 : EReal) := by
      have h := hmono_p hx
      simpa [hphi_one] using h
    have hpf' : (((p : ℝ) : EReal) * f x) ≤ (1 : EReal) := by
      have hpf_nonneg : (0 : EReal) ≤ (((p : ℝ) : EReal) * f x) :=
        EReal.mul_nonneg hp_nonneg (hnonneg x)
      have hcomp := phiPow_comp_phiPow_one_div_of_nonneg (p := p) hp hpf_nonneg
      have hcomp' :
          phiPow p (phiPow p⁻¹ (((p : ℝ) : EReal) * f x)) = ((p : ℝ) : EReal) * f x := by
        simpa [one_div] using hcomp
      have hpf'' : phiPow p (phiPow p⁻¹ (((p : ℝ) : EReal) * f x)) ≤ (1 : EReal) := by
        simpa [one_div] using hpf
      simpa [hcomp'] using hpf''
    have hmul := mul_le_mul_of_nonneg_left hpf' (by
      exact_mod_cast (le_of_lt hpinv_pos) : (0 : EReal) ≤ ((1 / p : ℝ) : EReal))
    have hmul' := hmul
    simp [one_div] at hmul'
    have hmul'' :
        ((p⁻¹ : ℝ) : EReal) * ((p : ℝ) : EReal) * f x ≤ ((p⁻¹ : ℝ) : EReal) := by
      simpa [mul_assoc] using hmul'
    have hmul''' : (1 : EReal) * f x ≤ ((p⁻¹ : ℝ) : EReal) := by
      simpa [hmul_pp'] using hmul''
    simpa using hmul'''

/-- The unit sublevel of a gauge corresponds to its polar set. -/
lemma unitSublevel_polarGauge_eq_polarSet {n : ℕ} {k : (Fin n → ℝ) → EReal} (hk : IsGauge k) :
    let C : Set (Fin n → ℝ) := {x | k x ≤ (1 : EReal)}
    {xStar | polarGauge k xStar ≤ (1 : EReal)} =
      {xStar | ∀ x ∈ C, (x ⬝ᵥ xStar : ℝ) ≤ 1} := by
  classical
  intro C
  have hsupport :
      ∀ xStar, supportFunctionEReal C xStar = polarGauge k xStar := by
    intro xStar
    simpa [C] using (supportFunction_unitSublevel_eq_polarGauge_of_isGauge (hk := hk) xStar)
  have hCStar :
      {xStar | polarGauge k xStar ≤ (1 : EReal)} =
        {xStar | supportFunctionEReal C xStar ≤ (1 : EReal)} := by
    ext xStar; constructor <;> intro hx <;> simpa [hsupport xStar] using hx
  exact hCStar.trans (supportFunctionEReal_sublevel_one_eq_polarSet (C := C))

end Section15
end Chap03
