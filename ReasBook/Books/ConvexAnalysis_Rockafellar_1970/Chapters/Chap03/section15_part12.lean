/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yijie Wang, Yunxi Duan, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part11

section Chap03
section Section15

open scoped BigOperators
open scoped Pointwise
open scoped Topology
open Filter

/-- A closed proper convex positively homogeneous function vanishes at the origin. -/
lemma f0_eq_zero_of_closedProperConvex_posHomogeneous {n : ℕ} {p : ℝ}
    {f : (Fin n → ℝ) → EReal} (hp : 1 < p)
    (hf_closed : ClosedConvexFunction f)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hf_hom : PositivelyHomogeneousOfDegree (n := n) p f) :
    f 0 = 0 := by
  have h0_ne_top : f 0 ≠ ⊤ :=
    f0_ne_top_of_closedProperConvex_posHomogeneous hp hf_closed hf_proper hf_hom
  have h0_ne_bot : f 0 ≠ ⊥ := by
    exact hf_proper.2.2 0 (by simp)
  set r0 : ℝ := (f 0).toReal
  have hr0 : (r0 : EReal) = f 0 := by
    simpa [r0] using (EReal.coe_toReal (x := f 0) h0_ne_top h0_ne_bot)
  have hhom0 : f 0 = ((Real.rpow 2 p : ℝ) : EReal) * f 0 := by
    simpa using hf_hom (0 : Fin n → ℝ) 2 (by norm_num)
  have hhom0' : r0 = Real.rpow 2 p * r0 := by
    have : (r0 : EReal) = ((Real.rpow 2 p * r0 : ℝ) : EReal) := by
      simpa [hr0, EReal.coe_mul] using hhom0
    exact (EReal.coe_eq_coe_iff).1 this
  have hpow_gt : 1 < Real.rpow 2 p := by
    have h2 : (1 : ℝ) < 2 := by norm_num
    have hp0 : 0 < p := by linarith
    exact Real.one_lt_rpow h2 hp0
  have hr0_eq : r0 = 0 := by
    have hmul : (Real.rpow 2 p - 1) * r0 = 0 := by
      nlinarith [hhom0']
    have hpow_ne : Real.rpow 2 p - 1 ≠ 0 := by
      linarith [hpow_gt]
    have hzero := mul_eq_zero.mp hmul
    rcases hzero with hzero | hzero
    · exact (hpow_ne hzero).elim
    · exact hzero
  have : (r0 : EReal) = (0 : EReal) := by
    simp [hr0_eq]
  simpa [hr0] using this

/-- Gauge-like functions with `f 0 = 0` are nonnegative. -/
lemma nonneg_of_isGaugeLike_f0_eq_zero {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hf : IsGaugeLike f) (h0 : f 0 = 0) : ∀ x : Fin n → ℝ, (0 : EReal) ≤ f x := by
  intro x
  rcases hf with ⟨_hconv, hmin, _hhom⟩
  have hx : f x ∈ Set.range f := ⟨x, rfl⟩
  have hle : sInf (Set.range f) ≤ f x := sInf_le hx
  simpa [hmin.symm, h0] using hle

/-- A positively homogeneous closed proper convex function has a closed-gauge power representation. -/
lemma exists_closedGauge_rpow_representation_of_posHomogeneous {n : ℕ} {p : ℝ}
    {f : (Fin n → ℝ) → EReal} (hp : 1 < p)
    (hf_closed : ClosedConvexFunction f)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hf_hom : PositivelyHomogeneousOfDegree (n := n) p f) :
    ∃ k : (Fin n → ℝ) → EReal, IsClosedGauge k ∧
      f = fun x => ((1 / p : ℝ) : EReal) * phiPow p (k x) := by
  classical
  have hf_gl : IsGaugeLike f :=
    isGaugeLike_of_closedProperConvex_posHomogeneous hp hf_closed hf_proper hf_hom
  have hf_glc : IsGaugeLikeClosedProperConvex f := ⟨hf_gl, hf_closed, hf_proper⟩
  have hf0 : f 0 = 0 :=
    f0_eq_zero_of_closedProperConvex_posHomogeneous hp hf_closed hf_proper hf_hom
  have hβpos : 0 < (1 / p : ℝ) := by
    have : 0 < p := by linarith
    exact one_div_pos.mpr this
  have hβ0 : f 0 < ((1 / p : ℝ) : EReal) := by
    have h0 : (0 : EReal) < ((1 / p : ℝ) : EReal) := by exact_mod_cast hβpos
    calc
      f 0 = (0 : EReal) := hf0
      _ < ((1 / p : ℝ) : EReal) := h0
  set k : (Fin n → ℝ) → EReal :=
    supportFunctionEReal
      {xStar | ∀ x ∈ {x | f x ≤ ((1 / p : ℝ) : EReal)}, (x ⬝ᵥ xStar : ℝ) ≤ 1}
  have hk' :
      IsClosedGauge k ∧ {x | k x ≤ (1 : EReal)} = {x | f x ≤ ((1 / p : ℝ) : EReal)} := by
    simpa [k] using
      (closedGauge_from_baseSublevel_supportFunctionEReal_polar_and_unitSublevel (f := f) (β := 1 / p)
        hf_glc hβ0)
  have hk : IsClosedGauge k := hk'.1
  have hunit : {x | k x ≤ (1 : EReal)} = {x | f x ≤ ((1 / p : ℝ) : EReal)} := hk'.2
  have hk_gauge : IsGauge k := hk.1
  have hsub :
      ∀ {r : ℝ}, 0 < r →
        {x | k x ≤ (r : EReal)} =
          {x | f x ≤ (((1 / p : ℝ) * Real.rpow r p) : ℝ)} :=
    sublevel_closedGauge_eq_sublevel_f_pow (hp := by linarith) (hf_hom := hf_hom) (hk := hk_gauge)
      hunit
  have hnonneg : ∀ x : Fin n → ℝ, (0 : EReal) ≤ f x :=
    nonneg_of_isGaugeLike_f0_eq_zero (hf := hf_gl) hf0
  refine ⟨k, hk, ?_⟩
  funext x
  by_cases hkx_top : k x = ⊤
  ·
    have hfx_top : f x = ⊤ := by
      by_contra hfx_top
      have hfx_bot : f x ≠ ⊥ := hf_proper.2.2 x (by simp)
      set M : ℝ := (f x).toReal
      have hM_coe : (M : EReal) = f x := EReal.coe_toReal (x := f x) hfx_top hfx_bot
      have hM_nonneg : 0 ≤ M := by
        have : (0 : EReal) ≤ (M : EReal) := by simpa [hM_coe] using hnonneg x
        exact (EReal.coe_le_coe_iff).1 this
      have hM1_pos : 0 < M + 1 := by linarith
      set β : ℝ := 1 / p
      have hβpos' : 0 < β := by
        have : 0 < p := by linarith
        exact one_div_pos.mpr this
      set t : ℝ := Real.rpow (β / (M + 1)) (1 / p)
      have htpos : 0 < t := by
        have hbase : 0 < β / (M + 1) := by exact div_pos hβpos' hM1_pos
        exact Real.rpow_pos_of_pos hbase (1 / p)
      have htpow : Real.rpow t p = β / (M + 1) := by
        have hbase_nonneg : 0 ≤ β / (M + 1) := by
          exact le_of_lt (div_pos hβpos' hM1_pos)
        have hpne : p ≠ 0 := by linarith
        simpa [t, one_div] using (Real.rpow_inv_rpow (x := β / (M + 1)) hbase_nonneg hpne)
      have hmul_le : Real.rpow t p * M ≤ β := by
        have hmul : Real.rpow t p * M = β * (M / (M + 1)) := by
          calc
            Real.rpow t p * M = (β / (M + 1)) * M := by rw [htpow]
            _ = β * (M / (M + 1)) := by
              simp [div_eq_mul_inv, mul_comm, mul_left_comm]
        have hfrac_le : M / (M + 1) ≤ 1 := by
          have hle : M ≤ M + 1 := by linarith
          exact (div_le_one hM1_pos).2 hle
        have hβnonneg : 0 ≤ β := le_of_lt hβpos'
        calc
          Real.rpow t p * M = β * (M / (M + 1)) := hmul
          _ ≤ β * 1 := by exact mul_le_mul_of_nonneg_left hfrac_le hβnonneg
          _ = β := by ring
      have hle_real : ((Real.rpow t p * M : ℝ) : EReal) ≤ (β : EReal) := by
        exact_mod_cast hmul_le
      have hle' : ((Real.rpow t p : ℝ) : EReal) * f x ≤ (β : EReal) := by
        calc
          ((Real.rpow t p : ℝ) : EReal) * f x =
              ((Real.rpow t p : ℝ) : EReal) * (M : EReal) := by simp [hM_coe]
          _ = ((Real.rpow t p * M : ℝ) : EReal) := by simp [EReal.coe_mul]
          _ ≤ (β : EReal) := hle_real
      have hhom : f (t • x) = ((Real.rpow t p : ℝ) : EReal) * f x := hf_hom x t htpos
      have hle : f (t • x) ≤ (β : EReal) := by simpa [hhom] using hle'
      have hx_mem : t • x ∈ {x | f x ≤ (β : EReal)} := by simpa using hle
      have hx_mem' : t • x ∈ {x | k x ≤ (1 : EReal)} := by simpa [hunit] using hx_mem
      have hk_le : k (t • x) ≤ (1 : EReal) := by simpa using hx_mem'
      have hk_scale : k (t • x) = ((t : ℝ) : EReal) * k x :=
        hk_gauge.2.2.1 x t (le_of_lt htpos)
      have hk_top' : k (t • x) = ⊤ := by
        simp [hk_scale, hkx_top, ereal_coe_mul_top_of_pos htpos]
      have : (⊤ : EReal) ≤ (1 : EReal) := by simpa [hk_top'] using hk_le
      exact (not_top_le_coe 1) this
    have hmul_top : ((p⁻¹ : ℝ) : EReal) * (⊤ : EReal) = (⊤ : EReal) := by
      simpa [one_div] using (ereal_coe_mul_top_of_pos (one_div_pos.mpr (by linarith)))
    simp [phiPow, hkx_top, hfx_top, hmul_top, one_div]
  ·
    have hkx_ne_bot : k x ≠ ⊥ := IsGauge.ne_bot hk_gauge x
    set r : ℝ := (k x).toReal
    have hr_coe : (r : EReal) = k x := EReal.coe_toReal (x := k x) hkx_top hkx_ne_bot
    have hr_nonneg : 0 ≤ r := by
      have : (0 : EReal) ≤ (r : EReal) := by simpa [hr_coe.symm] using hk_gauge.2.1 x
      exact (EReal.coe_le_coe_iff).1 this
    by_cases hr0 : r = 0
    ·
      have hkx_zero : k x = (0 : EReal) := by simpa [hr0] using hr_coe.symm
      have hx_mem : x ∈ {x | k x ≤ (1 : EReal)} := by
        simp [hkx_zero]
      have hfx_le : f x ≤ ((1 / p : ℝ) : EReal) := by
        have hx_mem' : x ∈ {x | f x ≤ ((1 / p : ℝ) : EReal)} := by
          simpa [hunit] using hx_mem
        simpa using hx_mem'
      have hfx_top : f x ≠ ⊤ := by
        intro htop
        rw [htop] at hfx_le
        exact (not_top_le_coe (1 / p : ℝ)) hfx_le
      have hfx_bot : f x ≠ ⊥ := hf_proper.2.2 x (by simp)
      by_cases hfx_zero : f x = 0
      ·
        have hpne : p ≠ 0 := by linarith
        have hphi : phiPow p (k x) = (0 : EReal) := by
          simp [phiPow, hkx_zero, Real.zero_rpow hpne]
        simp [hfx_zero, hphi]
      ·
        have hfx_pos : (0 : EReal) < f x :=
          lt_of_le_of_ne (hnonneg x) (by symm; exact hfx_zero)
        set M : ℝ := (f x).toReal
        have hM_coe : (M : EReal) = f x := EReal.coe_toReal (x := f x) hfx_top hfx_bot
        have hM_pos : 0 < M := by
          have : (0 : EReal) < (M : EReal) := by simpa [hM_coe] using hfx_pos
          exact (EReal.coe_lt_coe_iff).1 this
        set β : ℝ := 1 / p
        have hβpos' : 0 < β := by
          have : 0 < p := by linarith
          exact one_div_pos.mpr this
        set t : ℝ := Real.rpow (β / M + 1) (1 / p)
        have htpos : 0 < t := by
          have hdiv : 0 < β / M := div_pos hβpos' hM_pos
          have hbase : 0 < β / M + 1 := by linarith [hdiv]
          exact Real.rpow_pos_of_pos hbase (1 / p)
        have htpow : Real.rpow t p = β / M + 1 := by
          have hbase_nonneg : 0 ≤ β / M + 1 := by
            have hdiv : 0 < β / M := div_pos hβpos' hM_pos
            linarith [hdiv]
          have hpne : p ≠ 0 := by linarith
          simpa [t, one_div] using (Real.rpow_inv_rpow (x := β / M + 1) hbase_nonneg hpne)
        have hmul_gt : Real.rpow t p * M > β := by
          have hmul : Real.rpow t p * M = β + M := by
            calc
              Real.rpow t p * M = (β / M + 1) * M := by rw [htpow]
              _ = β + M := by field_simp [hM_pos.ne']
          have hβlt : β < β + M := by linarith [hM_pos]
          calc
            β < β + M := hβlt
            _ = Real.rpow t p * M := by
              symm
              exact hmul
        have hle_real : ((β : ℝ) : EReal) < ((Real.rpow t p * M : ℝ) : EReal) := by
          exact_mod_cast hmul_gt
        have hle' : (β : EReal) < ((Real.rpow t p : ℝ) : EReal) * f x := by
          calc
            (β : EReal) < ((Real.rpow t p * M : ℝ) : EReal) := hle_real
            _ = ((Real.rpow t p : ℝ) : EReal) * (M : EReal) := by
              simp [EReal.coe_mul]
            _ = ((Real.rpow t p : ℝ) : EReal) * f x := by simp [hM_coe]
        have hhom : f (t • x) = ((Real.rpow t p : ℝ) : EReal) * f x := hf_hom x t htpos
        have hgt : (β : EReal) < f (t • x) := by simpa [hhom] using hle'
        have hk_scale : k (t • x) = ((t : ℝ) : EReal) * k x :=
          hk_gauge.2.2.1 x t (le_of_lt htpos)
        have hk_zero : k (t • x) = (0 : EReal) := by
          simp [hk_scale, hkx_zero]
        have hx_mem : t • x ∈ {x | k x ≤ (1 : EReal)} := by
          simp [hk_zero]
        have hx_mem' : t • x ∈ {x | f x ≤ (β : EReal)} := by
          simpa [hunit, β] using hx_mem
        have hle : f (t • x) ≤ (β : EReal) := by simpa using hx_mem'
        exact (not_lt_of_ge hle hgt).elim
    ·
      have hrpos : 0 < r := lt_of_le_of_ne hr_nonneg (Ne.symm hr0)
      have hx_mem : x ∈ {x | k x ≤ (r : EReal)} := by
        have : k x ≤ (r : EReal) := by simp [hr_coe]
        simpa using this
      have hfx_le : f x ≤ (((1 / p : ℝ) * Real.rpow r p) : EReal) := by
        have hx_mem' : x ∈ {x | f x ≤ (((1 / p : ℝ) * Real.rpow r p) : EReal)} := by
          simpa [hsub hrpos] using hx_mem
        simpa using hx_mem'
      set y : Fin n → ℝ := (r⁻¹) • x
      have hk_scale : k y = ((r⁻¹ : ℝ) : EReal) * k x :=
        hk_gauge.2.2.1 x r⁻¹ (le_of_lt (inv_pos.mpr hrpos))
      have hk_y : k y = (1 : EReal) := by
        have hrne : r ≠ 0 := ne_of_gt hrpos
        calc
          k y = ((r⁻¹ : ℝ) : EReal) * (r : EReal) := by
            simp [y, hr_coe.symm, hk_scale]
          _ = ((r⁻¹ * r : ℝ) : EReal) := by simp [EReal.coe_mul]
          _ = (1 : EReal) := by
            have : (r⁻¹ * r : ℝ) = 1 := by field_simp [hrne]
            simp [this]
      have hy_mem : y ∈ {x | k x ≤ (1 : EReal)} := by
        simp [hk_y]
      have hfy_le : f y ≤ ((1 / p : ℝ) : EReal) := by
        have hy_mem' : y ∈ {x | f x ≤ ((1 / p : ℝ) : EReal)} := by
          simpa [hunit] using hy_mem
        simpa using hy_mem'
      have hfy_ge : ((1 / p : ℝ) : EReal) ≤ f y := by
        by_contra hlt
        have hlt' : f y < ((1 / p : ℝ) : EReal) := lt_of_not_ge hlt
        by_cases hfy_zero : f y = 0
        ·
          set s0 : ℝ := (1 / 2 : ℝ)
          have hs0_pos : 0 < s0 := by norm_num
          have hle_real : (0 : ℝ) ≤ (1 / p : ℝ) * Real.rpow s0 p := by
            have hβpos'' : 0 < (1 / p : ℝ) := by
              have : 0 < p := by linarith
              exact one_div_pos.mpr this
            have hβnonneg : 0 ≤ (1 / p : ℝ) := le_of_lt hβpos''
            have hs0_nonneg : 0 ≤ s0 := by linarith
            have hpow_nonneg : 0 ≤ Real.rpow s0 p := by
              simpa using (Real.rpow_nonneg hs0_nonneg p)
            exact mul_nonneg hβnonneg hpow_nonneg
          have hy_mem' : y ∈ {x | f x ≤ (((1 / p : ℝ) * Real.rpow s0 p) : EReal)} := by
            have : f y ≤ (((1 / p : ℝ) * Real.rpow s0 p) : EReal) := by
              have hle' : (0 : EReal) ≤ (((1 / p : ℝ) * Real.rpow s0 p) : EReal) := by
                exact_mod_cast hle_real
              simpa [hfy_zero] using hle'
            simpa using this
          have hk_le : k y ≤ (s0 : EReal) := by
            have hy_mem'' : y ∈ {x | k x ≤ (s0 : EReal)} := by
              simpa [hsub hs0_pos] using hy_mem'
            simpa using hy_mem''
          have : (1 : EReal) ≤ (s0 : EReal) := by
            simpa [hk_y] using hk_le
          have : (1 : ℝ) ≤ s0 := by exact_mod_cast this
          have : (1 : ℝ) ≤ (1 / 2 : ℝ) := by simpa [s0] using this
          nlinarith
        ·
          have hfy_bot : f y ≠ ⊥ := hf_proper.2.2 y (by simp [y])
          have hfy_top : f y ≠ ⊤ := by
            intro htop
            rw [htop] at hfy_le
            exact (not_top_le_coe (1 / p : ℝ)) hfy_le
          set Fy : ℝ := (f y).toReal
          have hFy_coe : (Fy : EReal) = f y := EReal.coe_toReal (x := f y) hfy_top hfy_bot
          have hFy_pos : 0 < Fy := by
            have hfy_pos : (0 : EReal) < f y :=
              lt_of_le_of_ne (hnonneg y) (by symm; exact hfy_zero)
            have : (0 : EReal) < (Fy : EReal) := by simpa [hFy_coe] using hfy_pos
            exact (EReal.coe_lt_coe_iff).1 this
          have hFy_nonneg : 0 ≤ Fy := le_of_lt hFy_pos
          have hFy_lt : Fy < (1 / p : ℝ) := by
            have : (Fy : EReal) < ((1 / p : ℝ) : EReal) := by simpa [hFy_coe] using hlt'
            exact (EReal.coe_lt_coe_iff).1 this
          set s : ℝ := Real.rpow (Fy / (1 / p : ℝ)) (1 / p)
          have hs_pos : 0 < s := by
            have hbase : 0 < Fy / (1 / p : ℝ) := by
              have hβpos'' : 0 < (1 / p : ℝ) := by
                have : 0 < p := by linarith
                exact one_div_pos.mpr this
              exact div_pos hFy_pos hβpos''
            exact Real.rpow_pos_of_pos hbase (1 / p)
          have hs_lt_one : s < 1 := by
            have hbase_nonneg : 0 ≤ Fy / (1 / p : ℝ) := by
              have hβpos'' : 0 < (1 / p : ℝ) := by
                have : 0 < p := by linarith
                exact one_div_pos.mpr this
              exact div_nonneg hFy_nonneg (le_of_lt hβpos'')
            have hbase_lt_one : Fy / (1 / p : ℝ) < 1 := by
              have hβpos'' : 0 < (1 / p : ℝ) := by
                have : 0 < p := by linarith
                exact one_div_pos.mpr this
              exact (div_lt_one hβpos'').2 hFy_lt
            have hpow_pos : 0 < (1 / p : ℝ) := by
              have : 0 < p := by linarith
              exact one_div_pos.mpr this
            simpa [s] using (Real.rpow_lt_one hbase_nonneg hbase_lt_one hpow_pos)
          have hspow : Real.rpow s p = Fy / (1 / p : ℝ) := by
            have hbase_nonneg : 0 ≤ Fy / (1 / p : ℝ) := by
              have hβpos'' : 0 < (1 / p : ℝ) := by
                have : 0 < p := by linarith
                exact one_div_pos.mpr this
              exact div_nonneg hFy_nonneg (le_of_lt hβpos'')
            have hpne : p ≠ 0 := by linarith
            simpa [s, one_div] using (Real.rpow_inv_rpow (x := Fy / (1 / p : ℝ)) hbase_nonneg hpne)
          have hy_mem' : y ∈ {x | f x ≤ (((1 / p : ℝ) * Real.rpow s p) : EReal)} := by
            have hle_real : ((Fy : ℝ) : EReal) ≤
                (((1 / p : ℝ) * Real.rpow s p) : EReal) := by
              have hle_real' : Fy ≤ (1 / p : ℝ) * Real.rpow s p := by
                have hpne : p ≠ 0 := by linarith
                have hcalc : (1 / p : ℝ) * Real.rpow s p = Fy := by
                  calc
                    (1 / p : ℝ) * Real.rpow s p =
                        (1 / p : ℝ) * (Fy / (1 / p : ℝ)) := by rw [hspow]
                    _ = Fy := by field_simp [hpne]
                exact le_of_eq hcalc.symm
              exact_mod_cast hle_real'
            simpa [hFy_coe] using hle_real
          have hk_le : k y ≤ (s : EReal) := by
            have hy_mem'' : y ∈ {x | k x ≤ (s : EReal)} := by
              have hs_pos' : 0 < s := hs_pos
              simpa [hsub hs_pos'] using hy_mem'
            simpa using hy_mem''
          have : (1 : EReal) ≤ (s : EReal) := by
            simpa [hk_y] using hk_le
          have : (1 : ℝ) ≤ s := by exact_mod_cast this
          exact (not_lt_of_ge this hs_lt_one).elim
      have hfy_eq : f y = ((1 / p : ℝ) : EReal) := le_antisymm hfy_le hfy_ge
      have hhom : f x = ((Real.rpow r p : ℝ) : EReal) * f y := by
        have hx_eq : r • y = x := by
          have hrne : r ≠ 0 := ne_of_gt hrpos
          simp [y, smul_smul, hrne]
        simpa [hx_eq] using (hf_hom y r hrpos)
      have hphi : phiPow p (k x) = ((Real.rpow r p : ℝ) : EReal) := by
        simp [phiPow, hr_coe.symm, max_eq_left hr_nonneg]
      calc
        f x = ((Real.rpow r p : ℝ) : EReal) * f y := hhom
        _ = ((1 / p : ℝ) : EReal) * ((Real.rpow r p : ℝ) : EReal) := by
          simp [hfy_eq, mul_comm]
        _ = ((1 / p : ℝ) : EReal) * phiPow p (k x) := by simp [hphi]
/-- If a profile `φ` scales on nonnegative inputs, then `(1/p) * φ ∘ k` is positively homogeneous
of degree `p`. -/
lemma posHomogeneous_of_exists_closedGauge_scaled {n : ℕ} {p : ℝ}
    {f : (Fin n → ℝ) → EReal} {φ : EReal → EReal}
    (hφ : ∀ {z : EReal} {t : ℝ}, 0 ≤ z → 0 < t →
      φ (((t : ℝ) : EReal) * z) = ((Real.rpow t p : ℝ) : EReal) * φ z) :
    (∃ k : (Fin n → ℝ) → EReal, IsClosedGauge k ∧
        f = fun x => ((1 / p : ℝ) : EReal) * φ (k x)) →
      PositivelyHomogeneousOfDegree (n := n) p f := by
  intro h
  rcases h with ⟨k, hk, rfl⟩
  intro x t ht
  have hk_scale : k (t • x) = ((t : ℝ) : EReal) * k x :=
    hk.1.2.2.1 x t (le_of_lt ht)
  have hk_nonneg : (0 : EReal) ≤ k x := hk.1.2.1 x
  calc
    ((1 / p : ℝ) : EReal) * φ (k (t • x)) =
        ((1 / p : ℝ) : EReal) * φ (((t : ℝ) : EReal) * k x) := by
      simp [hk_scale]
    _ = ((1 / p : ℝ) : EReal) * (((Real.rpow t p : ℝ) : EReal) * φ (k x)) := by
      simp [hφ hk_nonneg ht]
    _ = ((Real.rpow t p : ℝ) : EReal) * (((1 / p : ℝ) : EReal) * φ (k x)) := by
      simp [mul_assoc, mul_left_comm, mul_comm]

/-- The conjugate of a closed-gauge power profile is a power profile with conjugate exponent. -/
lemma fenchelConjugate_rpow_closedGauge_formula_and_posHomogeneous {n : ℕ} {p q : ℝ}
    (hp : 1 < p) (hpq : (1 / p) + (1 / q) = 1) {f : (Fin n → ℝ) → EReal}
    {k : (Fin n → ℝ) → EReal} (hk : IsClosedGauge k)
    (hfk : f = fun x => ((1 / p : ℝ) : EReal) * phiPow p (k x)) :
    PositivelyHomogeneousOfDegree (n := n) q (fenchelConjugate n f) ∧
      ∀ xStar : Fin n → ℝ,
        fenchelConjugate n f xStar = ((1 / q : ℝ) : EReal) * phiPow q (polarGauge k xStar) := by
  classical
  set gPow : EReal → EReal := fun z => ((1 / p : ℝ) : EReal) * phiPow p z
  have hbasic := gPow_basic (p := p) hp
  have hg_mono : Monotone gPow := hbasic.1
  have hg_top : gPow ⊤ = ⊤ := hbasic.2.1
  have hζ :
      ∃ ζ : ℝ, 0 < ζ ∧ gPow (ζ : EReal) ≠ ⊤ ∧ gPow (ζ : EReal) ≠ ⊥ := hbasic.2.2
  have hfg' : f = fun x => gPow (k x) := by
    simpa [gPow] using hfk
  have hformula :
      ∀ xStar : Fin n → ℝ,
        fenchelConjugate n f xStar = monotoneConjugateERealNonneg gPow (polarGauge k xStar) :=
    (fenchelConjugate_eq_monotoneConjugate_polarGauge_of_comp (n := n) (f := f) (k := k)
          (g := gPow) hk hfg' hg_mono hg_top hζ).2
  have hformula' :
      ∀ xStar : Fin n → ℝ,
        fenchelConjugate n f xStar = ((1 / q : ℝ) : EReal) * phiPow q (polarGauge k xStar) := by
    intro xStar
    have hpol_nonneg : (0 : EReal) ≤ polarGauge k xStar := (polarGauge_isGauge (k := k)).2.1 xStar
    calc
      fenchelConjugate n f xStar =
          monotoneConjugateERealNonneg gPow (polarGauge k xStar) := hformula xStar
      _ = ((1 / q : ℝ) : EReal) * phiPow q (polarGauge k xStar) := by
          simpa [gPow] using
            (monotoneConjugateERealNonneg_gPow_eq_one_div_q_phiPow (p := p) (q := q) hp hpq
              hpol_nonneg)
  have hpos : PositivelyHomogeneousOfDegree (n := n) q (fenchelConjugate n f) := by
    intro x t ht
    have hkStar : IsGauge (polarGauge k) := polarGauge_isGauge (k := k)
    have hkStar_nonneg : (0 : EReal) ≤ polarGauge k x := hkStar.2.1 x
    have hkStar_scale :
        polarGauge k (t • x) = ((t : ℝ) : EReal) * polarGauge k x :=
      hkStar.2.2.1 x t (le_of_lt ht)
    calc
      fenchelConjugate n f (t • x) =
          ((1 / q : ℝ) : EReal) * phiPow q (polarGauge k (t • x)) := hformula' (t • x)
      _ = ((1 / q : ℝ) : EReal) * phiPow q (((t : ℝ) : EReal) * polarGauge k x) := by
          simp [hkStar_scale]
      _ = ((1 / q : ℝ) : EReal) *
            (((Real.rpow t q : ℝ) : EReal) * phiPow q (polarGauge k x)) := by
          simp [phiPow_mul_of_nonneg (r := q) (z := polarGauge k x) (t := t) hkStar_nonneg ht]
      _ = ((Real.rpow t q : ℝ) : EReal) *
            (((1 / q : ℝ) : EReal) * phiPow q (polarGauge k x)) := by
          simp [mul_assoc, mul_left_comm, mul_comm]
      _ = ((Real.rpow t q : ℝ) : EReal) * fenchelConjugate n f x := by
          simp [hformula']
  exact ⟨hpos, hformula'⟩

/-- Triangle inequality for affine combinations. -/
lemma section15_abs_combo_le (a b t : ℝ) (ht0 : 0 ≤ t) (ht1 : 0 ≤ 1 - t) :
    |(1 - t) * a + t * b| ≤ (1 - t) * |a| + t * |b| := by
  calc
    |(1 - t) * a + t * b| ≤ |(1 - t) * a| + |t * b| := by
      simpa using (abs_add_le ((1 - t) * a) (t * b))
    _ = |1 - t| * |a| + |t| * |b| := by
      simp [abs_mul]
    _ = (1 - t) * |a| + t * |b| := by
      simp [abs_of_nonneg ht1, abs_of_nonneg ht0]

/-- Convexity inequality for `|·|^p` with `p ≥ 1`. -/
lemma section15_abs_rpow_combo_le {p : ℝ} (hp : 1 ≤ p) (a b t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : 0 ≤ 1 - t) :
    Real.rpow (|((1 - t) * a + t * b)|) p ≤
      (1 - t) * Real.rpow (|a|) p + t * Real.rpow (|b|) p := by
  have hcombo : |(1 - t) * a + t * b| ≤ (1 - t) * |a| + t * |b| :=
    section15_abs_combo_le a b t ht0 ht1
  have hnonneg : 0 ≤ |(1 - t) * a + t * b| := abs_nonneg _
  have hp0 : 0 ≤ p := by linarith
  have hmono :
      Real.rpow (|((1 - t) * a + t * b)|) p ≤
        Real.rpow ((1 - t) * |a| + t * |b|) p :=
    Real.rpow_le_rpow hnonneg hcombo hp0
  have hconv : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x : ℝ => x ^ p) := convexOn_rpow hp
  have hconv' :
      ((1 - t) * |a| + t * |b|) ^ p ≤ (1 - t) * |a| ^ p + t * |b| ^ p := by
    have hx : |a| ∈ Set.Ici (0 : ℝ) := abs_nonneg a
    have hy : |b| ∈ Set.Ici (0 : ℝ) := abs_nonneg b
    have h :=
      (hconv.2) (x := |a|) hx (y := |b|) hy (a := (1 : ℝ) - t) (b := t) ht1 ht0 (by ring)
    simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc] using h
  exact le_trans hmono (by simpa using hconv')

/-- Convexity of the `(1/p) * ∑ |xᵢ|^p` function. -/
lemma section15_convexFunction_sum_abs_rpow_div {n : ℕ} {p : ℝ} (hp : 1 < p) :
    ConvexFunction (fun x : Fin n → ℝ =>
      (((1 / p : ℝ) * ∑ i : Fin n, Real.rpow (|x i|) p) : EReal)) := by
  classical
  have hnotbot :
      ∀ x ∈ (Set.univ : Set (Fin n → ℝ)),
        (((1 / p : ℝ) * ∑ i : Fin n, Real.rpow (|x i|) p) : EReal) ≠ ⊥ := by
    intro x hx
    simpa using
      (EReal.coe_ne_bot ((1 / p : ℝ) * ∑ i : Fin n, Real.rpow (|x i|) p))
  have hconv_on :
      ConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (fun x : Fin n → ℝ =>
          (((1 / p : ℝ) * ∑ i : Fin n, Real.rpow (|x i|) p) : EReal)) := by
    refine
      (convexFunctionOn_iff_segment_inequality
          (C := (Set.univ : Set (Fin n → ℝ)))
          (f := fun x : Fin n → ℝ =>
            (((1 / p : ℝ) * ∑ i : Fin n, Real.rpow (|x i|) p) : EReal))
          (hC := by simpa using (convex_univ : Convex ℝ (Set.univ : Set (Fin n → ℝ))))
          (hnotbot := hnotbot)).2 ?_
    intro x hx y hy t ht0 ht1
    have ht0' : 0 ≤ t := le_of_lt ht0
    have ht1' : 0 ≤ 1 - t := by linarith
    have hp1 : 1 ≤ p := by linarith
    let g : (Fin n → ℝ) → ℝ :=
      fun x => (1 / p : ℝ) * ∑ i : Fin n, Real.rpow (|x i|) p
    have hsum :
        ∑ i : Fin n, Real.rpow (|((1 - t) * x i + t * y i)|) p ≤
          (1 - t) * ∑ i : Fin n, Real.rpow (|x i|) p +
            t * ∑ i : Fin n, Real.rpow (|y i|) p := by
      have hterm :
          ∀ i : Fin n,
            Real.rpow (|((1 - t) * x i + t * y i)|) p ≤
              (1 - t) * Real.rpow (|x i|) p + t * Real.rpow (|y i|) p := by
        intro i
        exact section15_abs_rpow_combo_le (p := p) hp1 (a := x i) (b := y i) (t := t) ht0' ht1'
      calc
        ∑ i : Fin n, Real.rpow (|((1 - t) * x i + t * y i)|) p
            ≤ ∑ i : Fin n,
                ((1 - t) * Real.rpow (|x i|) p + t * Real.rpow (|y i|) p) := by
              exact Finset.sum_le_sum (fun i hi => hterm i)
        _ = (1 - t) * ∑ i : Fin n, Real.rpow (|x i|) p +
              t * ∑ i : Fin n, Real.rpow (|y i|) p := by
              have hxsum :
                  ∑ i : Fin n, (1 - t) * Real.rpow (|x i|) p =
                    (1 - t) * ∑ i : Fin n, Real.rpow (|x i|) p := by
                symm
                exact (Finset.mul_sum (a := 1 - t) (s := Finset.univ)
                  (f := fun i => Real.rpow (|x i|) p))
              have hysum :
                  ∑ i : Fin n, t * Real.rpow (|y i|) p =
                    t * ∑ i : Fin n, Real.rpow (|y i|) p := by
                symm
                exact (Finset.mul_sum (a := t) (s := Finset.univ)
                  (f := fun i => Real.rpow (|y i|) p))
              calc
                ∑ i : Fin n,
                    ((1 - t) * Real.rpow (|x i|) p + t * Real.rpow (|y i|) p) =
                    ∑ i : Fin n, (1 - t) * Real.rpow (|x i|) p +
                      ∑ i : Fin n, t * Real.rpow (|y i|) p := by
                  simp [Finset.sum_add_distrib]
                _ = (1 - t) * ∑ i : Fin n, Real.rpow (|x i|) p +
                      t * ∑ i : Fin n, Real.rpow (|y i|) p := by
                  rw [hxsum, hysum]
    have hp_pos : 0 < p := by linarith
    have hcoeff_nonneg : 0 ≤ (1 / p : ℝ) := by exact le_of_lt (one_div_pos.mpr hp_pos)
    have hsum_scaled :
        (1 / p : ℝ) * ∑ i : Fin n, Real.rpow (|((1 - t) * x i + t * y i)|) p ≤
          (1 / p : ℝ) *
            ((1 - t) * ∑ i : Fin n, Real.rpow (|x i|) p +
              t * ∑ i : Fin n, Real.rpow (|y i|) p) :=
      mul_le_mul_of_nonneg_left hsum hcoeff_nonneg
    have hsum_scaled' :
        (1 / p : ℝ) *
            ((1 - t) * ∑ i : Fin n, Real.rpow (|x i|) p +
              t * ∑ i : Fin n, Real.rpow (|y i|) p) =
          (1 - t) * ((1 / p : ℝ) * ∑ i : Fin n, Real.rpow (|x i|) p) +
            t * ((1 / p : ℝ) * ∑ i : Fin n, Real.rpow (|y i|) p) := by
      ring
    have hreal :
        g ((1 - t) • x + t • y) ≤ (1 - t) * g x + t * g y := by
      have hreal' :
          (1 / p : ℝ) * ∑ i : Fin n, Real.rpow (|((1 - t) * x i + t * y i)|) p ≤
            (1 - t) * ((1 / p : ℝ) * ∑ i : Fin n, Real.rpow (|x i|) p) +
              t * ((1 / p : ℝ) * ∑ i : Fin n, Real.rpow (|y i|) p) := by
        calc
          (1 / p : ℝ) * ∑ i : Fin n, Real.rpow (|((1 - t) * x i + t * y i)|) p ≤
              (1 / p : ℝ) *
                ((1 - t) * ∑ i : Fin n, Real.rpow (|x i|) p +
                  t * ∑ i : Fin n, Real.rpow (|y i|) p) := hsum_scaled
          _ = (1 - t) * ((1 / p : ℝ) * ∑ i : Fin n, Real.rpow (|x i|) p) +
                t * ((1 / p : ℝ) * ∑ i : Fin n, Real.rpow (|y i|) p) := hsum_scaled'
      simpa [g, Pi.smul_apply, Pi.add_apply, smul_eq_mul] using hreal'
    have hrealE :
        (g ((1 - t) • x + t • y) : EReal) ≤
          (((1 - t) * g x + t * g y : ℝ) : EReal) := by
      exact_mod_cast hreal
    simpa [g, Pi.smul_apply, Pi.add_apply, smul_eq_mul, EReal.coe_add, EReal.coe_mul] using hrealE
  simpa [ConvexFunction] using hconv_on

/-- Lower semicontinuity of the `(1/p) * ∑ |xᵢ|^p` function. -/
lemma section15_lowerSemicontinuous_sum_abs_rpow_div {n : ℕ} {p : ℝ} (hp : 1 < p) :
    LowerSemicontinuous (fun x : Fin n → ℝ =>
      (((1 / p : ℝ) * ∑ i : Fin n, Real.rpow (|x i|) p) : EReal)) := by
  have hp0 : 0 ≤ p := by linarith
  have hcont_sum :
      Continuous (fun x : Fin n → ℝ => ∑ i : Fin n, Real.rpow (|x i|) p) := by
    classical
    refine continuous_finset_sum (s := Finset.univ) ?_
    intro i hi
    have hcont_abs : Continuous (fun x : Fin n → ℝ => |x i|) :=
      continuous_abs.comp (continuous_apply i)
    have hcont_rpow : Continuous (fun x : Fin n → ℝ => (|x i|) ^ p) := by
      refine hcont_abs.rpow_const ?_
      intro x
      exact Or.inr hp0
    simpa using hcont_rpow
  have hcont_real :
      Continuous (fun x : Fin n → ℝ =>
        (1 / p : ℝ) * ∑ i : Fin n, Real.rpow (|x i|) p) := by
    exact continuous_const.mul hcont_sum
  have hcont :
      Continuous (fun x : Fin n → ℝ =>
        (((1 / p : ℝ) * ∑ i : Fin n, Real.rpow (|x i|) p) : EReal)) :=
    continuous_coe_real_ereal.comp hcont_real
  exact hcont.lowerSemicontinuous

/-- Positive homogeneity of the `(1/p) * ∑ |xᵢ|^p` function. -/
lemma section15_posHomogeneous_sum_abs_rpow_div {n : ℕ} {p : ℝ} :
    PositivelyHomogeneousOfDegree (n := n) p (fun x : Fin n → ℝ =>
      (((1 / p : ℝ) * ∑ i : Fin n, Real.rpow (|x i|) p) : EReal)) := by
  intro x t ht
  have ht0 : 0 ≤ t := le_of_lt ht
  have hterm :
      ∀ i : Fin n,
        Real.rpow (|t * x i|) p = Real.rpow t p * Real.rpow (|x i|) p := by
    intro i
    have hx0 : 0 ≤ |x i| := abs_nonneg _
    calc
      Real.rpow (|t * x i|) p = Real.rpow (|t| * |x i|) p := by
        simp [abs_mul]
      _ = Real.rpow (t * |x i|) p := by
        simp [abs_of_pos ht]
      _ = Real.rpow t p * Real.rpow (|x i|) p := by
        simpa using (Real.mul_rpow (x := t) (y := |x i|) (z := p) ht0 hx0)
  have hsum :
      ∑ i : Fin n, Real.rpow (|t * x i|) p =
        Real.rpow t p * ∑ i : Fin n, Real.rpow (|x i|) p := by
    classical
    calc
      ∑ i : Fin n, Real.rpow (|t * x i|) p =
          ∑ i : Fin n, Real.rpow t p * Real.rpow (|x i|) p := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simpa using hterm i
      _ = Real.rpow t p * ∑ i : Fin n, Real.rpow (|x i|) p := by
        symm
        exact (Finset.mul_sum (a := Real.rpow t p) (s := Finset.univ)
          (f := fun i => Real.rpow (|x i|) p))
  have hmul :
      (1 / p : ℝ) * (Real.rpow t p * ∑ i : Fin n, Real.rpow (|x i|) p) =
        Real.rpow t p * ((1 / p : ℝ) * ∑ i : Fin n, Real.rpow (|x i|) p) := by
    ring
  calc
    (((1 / p : ℝ) * ∑ i : Fin n, Real.rpow (|(t • x) i|) p) : EReal) =
        (((1 / p : ℝ) * ∑ i : Fin n, Real.rpow (|t * x i|) p) : EReal) := by
      simp [Pi.smul_apply, smul_eq_mul]
    _ = ((Real.rpow t p : ℝ) : EReal) *
          (((1 / p : ℝ) * ∑ i : Fin n, Real.rpow (|x i|) p) : EReal) := by
      have hreal :
          (1 / p : ℝ) * ∑ i : Fin n, Real.rpow (|t * x i|) p =
            Real.rpow t p * ((1 / p : ℝ) * ∑ i : Fin n, Real.rpow (|x i|) p) := by
        calc
          (1 / p : ℝ) * ∑ i : Fin n, Real.rpow (|t * x i|) p =
              (1 / p : ℝ) * (Real.rpow t p * ∑ i : Fin n, Real.rpow (|x i|) p) := by
            rw [hsum]
          _ = Real.rpow t p * ((1 / p : ℝ) * ∑ i : Fin n, Real.rpow (|x i|) p) := hmul
      exact_mod_cast hreal
    _ = ((Real.rpow t p : ℝ) : EReal) *
          (fun x : Fin n → ℝ =>
            (((1 / p : ℝ) * ∑ i : Fin n, Real.rpow (|x i|) p) : EReal)) x := by
      rfl

/-- Text 15.0.22: Let `1 < p < ∞` and define `f : ℝⁿ → ℝ` by
`f x = (1/p) * (|ξ₁|^p + ... + |ξₙ|^p)` for `x = (ξ₁, ..., ξₙ)`. Then `f` is a closed proper convex
function and is positively homogeneous of degree `p`.

In this development, `ℝⁿ` is `Fin n → ℝ`, `f` is treated as `EReal`-valued by coercion, closedness
is `ClosedConvexFunction`, properness is `ProperConvexFunctionOn univ`, and `|ξᵢ|^p` is
`Real.rpow |ξᵢ| p`. -/
theorem sum_abs_rpow_div_closedProperConvex_posHomogeneous {n : ℕ} {p : ℝ} (hp : 1 < p) :
    let f : (Fin n → ℝ) → EReal :=
      fun x => (((1 / p : ℝ) * ∑ i : Fin n, Real.rpow (|x i|) p) : EReal)
    ClosedConvexFunction f ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f ∧
        PositivelyHomogeneousOfDegree (n := n) p f := by
  classical
  dsimp
  set f : (Fin n → ℝ) → EReal :=
    fun x => (((1 / p : ℝ) * ∑ i : Fin n, Real.rpow (|x i|) p) : EReal) with hf
  have hconv : ConvexFunction f := by
    simpa [hf] using (section15_convexFunction_sum_abs_rpow_div (n := n) (p := p) hp)
  have hls : LowerSemicontinuous f := by
    simpa [hf] using (section15_lowerSemicontinuous_sum_abs_rpow_div (n := n) (p := p) hp)
  have hhom : PositivelyHomogeneousOfDegree (n := n) p f := by
    simpa [hf] using (section15_posHomogeneous_sum_abs_rpow_div (n := n) (p := p))
  have hclosed : ClosedConvexFunction f := ⟨hconv, hls⟩
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f := by
    have hconv_on : ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f := by
      simpa [ConvexFunction] using hconv
    have hnotbot : ∀ x ∈ (Set.univ : Set (Fin n → ℝ)), f x ≠ ⊥ := by
      intro x hx
      simpa [hf] using
        (EReal.coe_ne_bot ((1 / p : ℝ) * ∑ i : Fin n, Real.rpow (|x i|) p))
    have hpne : p ≠ 0 := by linarith
    have hzero : f 0 = 0 := by
      simp [hf, hpne, Real.zero_rpow]
    have hmem : (0, 0) ∈ epigraph (Set.univ : Set (Fin n → ℝ)) f := by
      refine (mem_epigraph_univ_iff (f := f) (x := 0) (μ := 0)).2 ?_
      simp [hzero]
    have hne : Set.Nonempty (epigraph (Set.univ : Set (Fin n → ℝ)) f) := ⟨(0, 0), hmem⟩
    exact ⟨hconv_on, hne, hnotbot⟩
  exact ⟨hclosed, hproper, hhom⟩

/-- Conjugate-exponent data from `1 / p + 1 / q = 1`. -/
lemma section15_holderConjugate_of_hpq {p q : ℝ} (hp : 1 < p) (hpq : (1 / p) + (1 / q) = 1) :
    p.HolderConjugate q := by
  refine (Real.holderConjugate_iff).2 ?_
  refine ⟨hp, ?_⟩
  simpa [one_div] using hpq

/-- Young's inequality in a rearranged single-term form. -/
lemma section15_young_term_bound {p q a t : ℝ} (hpq : p.HolderConjugate q) :
    a * t - (1 / p) * Real.rpow (|t|) p ≤ (1 / q) * Real.rpow (|a|) q := by
  have h := Real.young_inequality t a hpq
  have h' :
      a * t ≤ (1 / p) * Real.rpow (|t|) p + (1 / q) * Real.rpow (|a|) q := by
    simpa [div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using h
  linarith

/-- Coordinatewise Young bounds summed over `Fin n`. -/
lemma section15_dot_sub_sum_abs_rpow_le {n : ℕ} {p q : ℝ} (hpq : p.HolderConjugate q)
    (xStar x : Fin n → ℝ) :
    (∑ i : Fin n, x i * xStar i) - (1 / p) * ∑ i : Fin n, Real.rpow (|x i|) p ≤
      (1 / q) * ∑ i : Fin n, Real.rpow (|xStar i|) q := by
  classical
  have hterm :
      ∀ i : Fin n,
        x i * xStar i - (1 / p) * Real.rpow (|x i|) p ≤ (1 / q) * Real.rpow (|xStar i|) q := by
    intro i
    simpa [mul_comm] using
      (section15_young_term_bound (p := p) (q := q) (a := xStar i) (t := x i) hpq)
  have hsum :
      ∑ i : Fin n, (x i * xStar i - (1 / p) * Real.rpow (|x i|) p) ≤
        ∑ i : Fin n, (1 / q) * Real.rpow (|xStar i|) q := by
    refine Finset.sum_le_sum ?_
    intro i hi
    exact hterm i
  have hsum_eq :
      ∑ i : Fin n, (x i * xStar i - (1 / p) * Real.rpow (|x i|) p) =
        (∑ i : Fin n, x i * xStar i) - (1 / p) * ∑ i : Fin n, Real.rpow (|x i|) p := by
    calc
      ∑ i : Fin n, (x i * xStar i - (1 / p) * Real.rpow (|x i|) p) =
          (∑ i : Fin n, x i * xStar i) - ∑ i : Fin n, (1 / p) * Real.rpow (|x i|) p := by
        simp [Finset.sum_sub_distrib]
      _ = (∑ i : Fin n, x i * xStar i) - (1 / p) * ∑ i : Fin n, Real.rpow (|x i|) p := by
        simp [Finset.mul_sum, mul_comm]
  calc
    (∑ i : Fin n, x i * xStar i) - (1 / p) * ∑ i : Fin n, Real.rpow (|x i|) p =
        ∑ i : Fin n, (x i * xStar i - (1 / p) * Real.rpow (|x i|) p) := by
      symm
      exact hsum_eq
    _ ≤ ∑ i : Fin n, (1 / q) * Real.rpow (|xStar i|) q := hsum
    _ = (1 / q) * ∑ i : Fin n, Real.rpow (|xStar i|) q := by
      simp [Finset.mul_sum, mul_comm]

/-- Multiplying by `|Real.sign r|` does not change `|r|^a` when `a > 0`. -/
lemma section15_abs_sign_mul_rpow_eq {r a : ℝ} (ha : 0 < a) :
    |Real.sign r| * Real.rpow (|r|) a = Real.rpow (|r|) a := by
  by_cases h : r = 0
  · subst h
    have ha' : a ≠ 0 := by linarith
    simp [Real.sign_zero, Real.zero_rpow, ha']
  ·
    have hr : r < 0 ∨ 0 < r := lt_or_gt_of_ne h
    have hsign : |Real.sign r| = 1 := by
      cases hr with
      | inl hneg => simp [Real.sign_of_neg hneg]
      | inr hpos => simp [Real.sign_of_pos hpos]
    simp [hsign]

/-- Evaluation of the Fenchel expression at the explicit maximizer. -/
lemma section15_eval_at_explicit_maximizer {n : ℕ} {p q : ℝ} (hpq : p.HolderConjugate q)
    (xStar : Fin n → ℝ) :
    let x0 : Fin n → ℝ := fun i => Real.sign (xStar i) * Real.rpow (|xStar i|) (q - 1)
    ((x0 ⬝ᵥ xStar : ℝ) : EReal) -
        (((1 / p : ℝ) * ∑ i : Fin n, Real.rpow (|x0 i|) p) : EReal) =
      (((1 / q : ℝ) * ∑ i : Fin n, Real.rpow (|xStar i|) q) : EReal) := by
  classical
  dsimp
  set x0 : Fin n → ℝ := fun i => Real.sign (xStar i) * Real.rpow (|xStar i|) (q - 1) with hx0
  have hq1pos : 0 < q - 1 := by
    linarith [hpq.symm.lt]
  have hmul : (q - 1) * p = q := by
    have h := hpq.mul_eq_add
    linarith
  have hdot_term :
      ∀ i : Fin n, x0 i * xStar i = Real.rpow (|xStar i|) q := by
    intro i
    have hq1 : 0 ≤ q - 1 := le_of_lt hq1pos
    have hnonneg : 0 ≤ |xStar i| := abs_nonneg _
    calc
      x0 i * xStar i =
          Real.sign (xStar i) * xStar i * Real.rpow (|xStar i|) (q - 1) := by
        simp [hx0, mul_comm, mul_left_comm]
      _ = (Real.sign (xStar i) * xStar i) * Real.rpow (|xStar i|) (q - 1) := by
        simp [mul_assoc]
      _ = |xStar i| * Real.rpow (|xStar i|) (q - 1) := by
        simp [real_sign_mul_self_eq_abs]
      _ = Real.rpow (|xStar i|) q := by
        calc
          |xStar i| * Real.rpow (|xStar i|) (q - 1) =
              Real.rpow (|xStar i|) 1 * Real.rpow (|xStar i|) (q - 1) := by simp
          _ = Real.rpow (|xStar i|) (1 + (q - 1)) := by
            symm
            have h1 : 0 ≤ (1 : ℝ) := by norm_num
            simpa using (Real.rpow_add_of_nonneg hnonneg h1 hq1)
          _ = Real.rpow (|xStar i|) q := by
            have hq : 1 + (q - 1) = q := by ring
            simp [hq]
  have hdot : x0 ⬝ᵥ xStar = ∑ i : Fin n, Real.rpow (|xStar i|) q := by
    simp [dotProduct, hdot_term]
  have hpow_term :
      ∀ i : Fin n, Real.rpow (|x0 i|) p = Real.rpow (|xStar i|) q := by
    intro i
    have hnonneg : 0 ≤ Real.rpow (|xStar i|) (q - 1) := Real.rpow_nonneg (abs_nonneg _) _
    have habs :
        |Real.sign (xStar i)| * Real.rpow (|xStar i|) (q - 1) =
          Real.rpow (|xStar i|) (q - 1) :=
      section15_abs_sign_mul_rpow_eq (r := xStar i) (a := q - 1) hq1pos
    have hx0abs :
        |x0 i| = |Real.sign (xStar i)| * Real.rpow (|xStar i|) (q - 1) := by
      calc
        |x0 i| = |Real.sign (xStar i) * Real.rpow (|xStar i|) (q - 1)| := by
          simp [hx0]
        _ = |Real.sign (xStar i)| * |Real.rpow (|xStar i|) (q - 1)| := by
          simp [abs_mul]
        _ = |Real.sign (xStar i)| * Real.rpow (|xStar i|) (q - 1) := by
          rw [abs_of_nonneg hnonneg]
    calc
      Real.rpow (|x0 i|) p = Real.rpow (Real.rpow (|xStar i|) (q - 1)) p := by
        rw [hx0abs, habs]
      _ = Real.rpow (|xStar i|) ((q - 1) * p) := by
        symm
        simpa using (Real.rpow_mul (abs_nonneg (xStar i)) (q - 1) p)
      _ = Real.rpow (|xStar i|) q := by
        simp [hmul]
  have hsum : ∑ i : Fin n, Real.rpow (|x0 i|) p = ∑ i : Fin n, Real.rpow (|xStar i|) q := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact hpow_term i
  have hreal :
      (x0 ⬝ᵥ xStar) - (1 / p) * ∑ i : Fin n, Real.rpow (|x0 i|) p =
        (1 / q) * ∑ i : Fin n, Real.rpow (|xStar i|) q := by
    set s : ℝ := ∑ i : Fin n, Real.rpow (|xStar i|) q
    calc
      (x0 ⬝ᵥ xStar) - (1 / p) * ∑ i : Fin n, Real.rpow (|x0 i|) p =
          s - (1 / p) * s := by
        rw [hdot, hsum]
      _ = (1 / q) * s := by
        have hqeq : (1 - 1 / p : ℝ) = 1 / q := by
          have h' : (1 / p : ℝ) + (1 / q : ℝ) = 1 := by
            simpa [one_div] using hpq.inv_add_inv_eq_one
          linarith
        calc
          s - (1 / p) * s = (1 - 1 / p) * s := by ring
          _ = (1 / q) * s := by rw [hqeq]
  exact_mod_cast hreal

/-- Text 15.0.23: Let `1 < p < ∞` and define `f : ℝⁿ → ℝ` by
`f x = (1/p) * (|ξ₁|^p + ... + |ξₙ|^p)` for `x = (ξ₁, ..., ξₙ)`. Its conjugate is
`f^*(x^*) = (1/q) * (|ξ₁^*|^q + ... + |ξₙ^*|^q)`, where `1/p + 1/q = 1`.

In this development, `ℝⁿ` is `Fin n → ℝ`, `|ξᵢ|^p` is `Real.rpow |ξᵢ| p`, and the conjugate is
modeled as `fenchelConjugate n f`. -/
theorem fenchelConjugate_sum_abs_rpow_div_eq_sum_abs_rpow_div {n : ℕ} {p q : ℝ} (hp : 1 < p)
    (hpq : (1 / p) + (1 / q) = 1) :
    let f : (Fin n → ℝ) → EReal :=
      fun x => (((1 / p : ℝ) * ∑ i : Fin n, Real.rpow (|x i|) p) : EReal)
    fenchelConjugate n f =
      fun xStar => (((1 / q : ℝ) * ∑ i : Fin n, Real.rpow (|xStar i|) q) : EReal) := by
  classical
  dsimp
  set f : (Fin n → ℝ) → EReal :=
    fun x => (((1 / p : ℝ) * ∑ i : Fin n, Real.rpow (|x i|) p) : EReal) with hf
  have hpq' : p.HolderConjugate q := section15_holderConjugate_of_hpq (p := p) (q := q) hp hpq
  funext xStar
  apply le_antisymm
  ·
    unfold fenchelConjugate
    refine sSup_le ?_
    rintro y ⟨x, rfl⟩
    have hreal :
        (x ⬝ᵥ xStar) - (1 / p) * ∑ i : Fin n, Real.rpow (|x i|) p ≤
          (1 / q) * ∑ i : Fin n, Real.rpow (|xStar i|) q := by
      simpa [dotProduct] using
        (section15_dot_sub_sum_abs_rpow_le (p := p) (q := q) hpq' (xStar := xStar) (x := x))
    have hE :
        ((x ⬝ᵥ xStar : ℝ) : EReal) -
            (((1 / p : ℝ) * ∑ i : Fin n, Real.rpow (|x i|) p) : EReal) ≤
          (((1 / q : ℝ) * ∑ i : Fin n, Real.rpow (|xStar i|) q) : EReal) := by
      exact_mod_cast hreal
    simpa [hf] using hE
  ·
    set x0 : Fin n → ℝ := fun i => Real.sign (xStar i) * Real.rpow (|xStar i|) (q - 1) with hx0
    have hval :
        ((x0 ⬝ᵥ xStar : ℝ) : EReal) -
            (((1 / p : ℝ) * ∑ i : Fin n, Real.rpow (|x0 i|) p) : EReal) =
          (((1 / q : ℝ) * ∑ i : Fin n, Real.rpow (|xStar i|) q) : EReal) := by
      simpa [hx0] using (section15_eval_at_explicit_maximizer (p := p) (q := q) hpq' xStar)
    have hsup :
        ((x0 ⬝ᵥ xStar : ℝ) : EReal) - f x0 ≤
          sSup (Set.range (fun x : Fin n → ℝ => ((x ⬝ᵥ xStar : ℝ) : EReal) - f x)) := by
      exact le_sSup ⟨x0, rfl⟩
    calc
      (((1 / q : ℝ) * ∑ i : Fin n, Real.rpow (|xStar i|) q) : EReal) =
          ((x0 ⬝ᵥ xStar : ℝ) : EReal) -
            (((1 / p : ℝ) * ∑ i : Fin n, Real.rpow (|x0 i|) p) : EReal) := by
        symm
        exact hval
      _ = ((x0 ⬝ᵥ xStar : ℝ) : EReal) - f x0 := by
        simp [hf, hx0]
      _ ≤ sSup (Set.range (fun x : Fin n → ℝ => ((x ⬝ᵥ xStar : ℝ) : EReal) - f x)) := hsup

/-- Corollary 15.3.1: Let `1 < p < ∞` and let `q` be its conjugate exponent, `1/p + 1/q = 1`.
For a closed proper convex function `f`, positive homogeneity of degree `p` is equivalent to the
existence of a closed gauge `k` such that `f(x) = (1/p) * k(x)^p`.

In this case, the Fenchel conjugate `f^*` (modeled as `fenchelConjugate n f`) is positively
homogeneous of degree `q` and satisfies `f^*(x^*) = (1/q) * (k^∘(x^*))^q`, where `k^∘` is the polar
gauge (modeled as `polarGauge k`). -/
theorem closedProperConvex_posHomogeneous_degree_iff_exists_closedGauge_rpow {n : ℕ}
    {p q : ℝ} (hp : 1 < p) (hpq : (1 / p) + (1 / q) = 1) {f : (Fin n → ℝ) → EReal}
    (hf_closed : ClosedConvexFunction f)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    let φp : EReal → EReal := fun z =>
      if z = ⊥ then (0 : EReal) else if z = ⊤ then (⊤ : EReal) else (Real.rpow (max z.toReal 0) p : EReal)
    let φq : EReal → EReal := fun z =>
      if z = ⊥ then (0 : EReal) else if z = ⊤ then (⊤ : EReal) else (Real.rpow (max z.toReal 0) q : EReal)
    (PositivelyHomogeneousOfDegree (n := n) p f ↔
        ∃ k : (Fin n → ℝ) → EReal, IsClosedGauge k ∧
          f = fun x => ((1 / p : ℝ) : EReal) * φp (k x)) ∧
      (∀ k : (Fin n → ℝ) → EReal,
        IsClosedGauge k →
          f = (fun x => ((1 / p : ℝ) : EReal) * φp (k x)) →
            PositivelyHomogeneousOfDegree (n := n) q (fenchelConjugate n f) ∧
              ∀ xStar : Fin n → ℝ,
                fenchelConjugate n f xStar = ((1 / q : ℝ) : EReal) * φq (polarGauge k xStar)) := by
  classical
  let φp : EReal → EReal := fun z =>
    if z = ⊥ then (0 : EReal) else if z = ⊤ then (⊤ : EReal) else (Real.rpow (max z.toReal 0) p : EReal)
  let φq : EReal → EReal := fun z =>
    if z = ⊥ then (0 : EReal) else if z = ⊤ then (⊤ : EReal) else (Real.rpow (max z.toReal 0) q : EReal)
  have hmain :
      (PositivelyHomogeneousOfDegree (n := n) p f ↔
          ∃ k : (Fin n → ℝ) → EReal, IsClosedGauge k ∧
            f = fun x => ((1 / p : ℝ) : EReal) * φp (k x)) ∧
        (∀ k : (Fin n → ℝ) → EReal,
          IsClosedGauge k →
            f = (fun x => ((1 / p : ℝ) : EReal) * φp (k x)) →
              PositivelyHomogeneousOfDegree (n := n) q (fenchelConjugate n f) ∧
                ∀ xStar : Fin n → ℝ,
                  fenchelConjugate n f xStar = ((1 / q : ℝ) : EReal) * φq (polarGauge k xStar)) := by
    constructor
    · constructor
      · intro hf_hom
        rcases
            exists_closedGauge_rpow_representation_of_posHomogeneous (n := n) (p := p) hp hf_closed
              hf_proper hf_hom with
          ⟨k, hk, hfk⟩
        refine ⟨k, hk, ?_⟩
        simpa [φp, phiPow] using hfk
      · intro hk
        have hφp :
            ∀ {z : EReal} {t : ℝ}, 0 ≤ z → 0 < t →
              φp (((t : ℝ) : EReal) * z) =
                ((Real.rpow t p : ℝ) : EReal) * φp z := by
          intro z t hz ht
          simpa [φp, phiPow] using (phiPow_mul_of_nonneg (r := p) (z := z) (t := t) hz ht)
        exact
          posHomogeneous_of_exists_closedGauge_scaled (f := f) (p := p) (φ := φp) hφp hk
    · intro k hk hfk
      have hfk' :
          f = fun x => ((1 / p : ℝ) : EReal) * phiPow p (k x) := by
        simpa [φp, phiPow] using hfk
      simpa [φq, phiPow] using
        (fenchelConjugate_rpow_closedGauge_formula_and_posHomogeneous (n := n) (p := p) (q := q) hp
          hpq (f := f) (k := k) hk hfk')
  simpa [φp, φq] using hmain
end Section15
end Chap03
