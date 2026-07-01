/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yijie Wang, Yunxi Duan, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section04_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section04_part6
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section07_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section09_part13
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section12_part6
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section12_part7
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section13_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section13_part6
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section14_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section14_part5

section Chap03
section Section15

open scoped BigOperators
open scoped Pointwise
open scoped RealInnerProductSpace

/-- Text 15.0.1: A function `k : ℝⁿ → (-∞, +∞]` is a gauge if it is convex, nonnegative,
positively homogeneous of degree `1` (i.e. `k (λ x) = λ k x` for all `λ ≥ 0`), and satisfies
`k 0 = 0`.

Equivalently, its epigraph `epi k = {(x, μ) | k x ≤ μ}` is a convex cone in `ℝⁿ⁺¹` containing
`(0, 0)` and containing no vector `(x, μ)` with `μ < 0`.

In this formalization, we use `Fin n → ℝ` for `ℝⁿ`, `EReal` for `(-∞, +∞]`, and the epigraph
construction `epigraph (S := Set.univ) k` from `Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section04_part1`. -/
def IsGauge {n : ℕ} (k : (Fin n → ℝ) → EReal) : Prop :=
  ConvexFunctionOn (S := (Set.univ : Set (Fin n → ℝ))) k ∧
    (∀ x, 0 ≤ k x) ∧
    (∀ x (r : ℝ), 0 ≤ r → k (r • x) = (r : EReal) * k x) ∧
    k 0 = 0

/-- A gauge never attains `⊥` because it is nonnegative. -/
lemma IsGauge.ne_bot {n : ℕ} {k : (Fin n → ℝ) → EReal} (hk : IsGauge k) (x : Fin n → ℝ) :
    k x ≠ (⊥ : EReal) := by
  rcases hk with ⟨_, hnonneg, _, _⟩
  intro hbot
  have h0le : (0 : EReal) ≤ k x := hnonneg x
  have h0le' : (0 : EReal) ≤ (⊥ : EReal) := by
    have h0le' := h0le
    rw [hbot] at h0le'
    exact h0le'
  have h0eq : (0 : EReal) = (⊥ : EReal) := (le_bot_iff).1 h0le'
  have h0ne : (0 : EReal) ≠ (⊥ : EReal) := by simp
  exact h0ne h0eq

/-- A gauge is subadditive. -/
lemma IsGauge.add_le {n : ℕ} {k : (Fin n → ℝ) → EReal} (hk : IsGauge k)
    (x y : Fin n → ℝ) : k (x + y) ≤ k x + k y := by
  rcases hk with ⟨hkconv, hnonneg, hhom, hk0⟩
  have hnotbot : ∀ x ∈ (Set.univ : Set (Fin n → ℝ)), k x ≠ (⊥ : EReal) := by
    intro x hx
    exact IsGauge.ne_bot ⟨hkconv, hnonneg, hhom, hk0⟩ x
  have hconv_univ : Convex ℝ (Set.univ : Set (Fin n → ℝ)) := by
    simpa using (convex_univ : Convex ℝ (Set.univ : Set (Fin n → ℝ)))
  have hseg :=
    (convexFunctionOn_iff_segment_inequality
        (C := (Set.univ : Set (Fin n → ℝ))) hconv_univ hnotbot).1 hkconv
  have hmid :=
    hseg x (by simp) y (by simp) (1 / 2 : ℝ) (by norm_num) (by norm_num)
  have hhalf : (1 - (2 : ℝ)⁻¹) = (2 : ℝ)⁻¹ := by norm_num
  have hmid' :
      k ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) ≤
        ((1 / 2 : ℝ) : EReal) * k x + ((1 / 2 : ℝ) : EReal) * k y := by
    simpa [one_div, hhalf] using hmid
  have htwo_half : (2 : ℝ) * (1 / 2 : ℝ) = (1 : ℝ) := by norm_num
  have hsum : (2 : ℝ) • ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) = x + y := by
    calc
      (2 : ℝ) • ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) =
          (2 : ℝ) • ((1 / 2 : ℝ) • x) + (2 : ℝ) • ((1 / 2 : ℝ) • y) := by
            simp [smul_add]
      _ = ((2 : ℝ) * (1 / 2 : ℝ)) • x + ((2 : ℝ) * (1 / 2 : ℝ)) • y := by
            simp [smul_smul]
      _ = x + y := by
            simp
  have hhom2 :
      k ((2 : ℝ) • ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y)) =
        ((2 : ℝ) : EReal) * k ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) := by
    simpa using hhom ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) 2 (by norm_num)
  have htwo_nonneg : (0 : EReal) ≤ ((2 : ℝ) : EReal) := by
    exact_mod_cast (show (0 : ℝ) ≤ 2 by norm_num)
  have hscale :
      ((2 : ℝ) : EReal) * k ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) ≤
        ((2 : ℝ) : EReal) *
          (((1 / 2 : ℝ) : EReal) * k x + ((1 / 2 : ℝ) : EReal) * k y) := by
    exact mul_le_mul_of_nonneg_left hmid' htwo_nonneg
  calc
    k (x + y) =
        ((2 : ℝ) : EReal) * k ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) := by
          simpa [hsum] using hhom2
    _ ≤
        ((2 : ℝ) : EReal) *
          (((1 / 2 : ℝ) : EReal) * k x + ((1 / 2 : ℝ) : EReal) * k y) := hscale
    _ = k x + k y := by
          have hhalf_nonneg : (0 : EReal) ≤ ((1 / 2 : ℝ) : EReal) := by
            exact_mod_cast (show (0 : ℝ) ≤ (1 / 2 : ℝ) by norm_num)
          have hx_nonneg : 0 ≤ ((1 / 2 : ℝ) : EReal) * k x :=
            EReal.mul_nonneg hhalf_nonneg (hnonneg x)
          have hy_nonneg : 0 ≤ ((1 / 2 : ℝ) : EReal) * k y :=
            EReal.mul_nonneg hhalf_nonneg (hnonneg y)
          calc
            ((2 : ℝ) : EReal) *
                (((1 / 2 : ℝ) : EReal) * k x + ((1 / 2 : ℝ) : EReal) * k y) =
                ((2 : ℝ) : EReal) * (((1 / 2 : ℝ) : EReal) * k x) +
                  ((2 : ℝ) : EReal) * (((1 / 2 : ℝ) : EReal) * k y) := by
              simpa using
                (EReal.left_distrib_of_nonneg (ha := hx_nonneg) (hb := hy_nonneg)
                  (c := ((2 : ℝ) : EReal)))
            _ =
                (((2 : ℝ) : EReal) * ((1 / 2 : ℝ) : EReal)) * k x +
                  (((2 : ℝ) : EReal) * ((1 / 2 : ℝ) : EReal)) * k y := by
                simp [mul_assoc]
            _ = k x + k y := by
                have hmul : ((2 : ℝ) : EReal) * ((2 : ℝ) : EReal)⁻¹ = (1 : EReal) := by
                  have h : (2 : ℝ) * (2 : ℝ)⁻¹ = (1 : ℝ) := by
                    have htwo_ne : (2 : ℝ) ≠ 0 := by norm_num
                    field_simp [htwo_ne]
                  have hE : ((2 : ℝ) * (2 : ℝ)⁻¹ : EReal) = (1 : EReal) := by
                    exact_mod_cast h
                  simpa [EReal.coe_mul, EReal.coe_inv] using hE
                calc
                  ((2 : ℝ) : EReal) * ((1 / 2 : ℝ) : EReal) * k x +
                      ((2 : ℝ) : EReal) * ((1 / 2 : ℝ) : EReal) * k y =
                      ((2 : ℝ) : EReal) * (((2 : ℝ) : EReal)⁻¹ * k x) +
                        ((2 : ℝ) : EReal) * (((2 : ℝ) : EReal)⁻¹ * k y) := by
                        simp [one_div, EReal.coe_inv, mul_assoc]
                  _ =
                      (((2 : ℝ) : EReal) * ((2 : ℝ) : EReal)⁻¹) * k x +
                        (((2 : ℝ) : EReal) * ((2 : ℝ) : EReal)⁻¹) * k y := by
                        simp [mul_assoc]
                  _ = (1 : EReal) * k x + (1 : EReal) * k y := by
                        simp [hmul]
                  _ = k x + k y := by simp

/-- The unit sublevel set of a gauge is nonempty (it contains `0`). -/
lemma IsGauge.sublevel_one_nonempty {n : ℕ} {k : (Fin n → ℝ) → EReal} (hk : IsGauge k) :
    ({x : Fin n → ℝ | k x ≤ (1 : EReal)}).Nonempty := by
  rcases hk with ⟨_, _, _, hk0⟩
  refine ⟨0, ?_⟩
  have h0le : (0 : EReal) ≤ (1 : EReal) := by
    exact_mod_cast (show (0 : ℝ) ≤ (1 : ℝ) by norm_num)
  simp [hk0, h0le]

/-- The unit sublevel set of a gauge is convex. -/
lemma IsGauge.convex_sublevel_one {n : ℕ} {k : (Fin n → ℝ) → EReal} (hk : IsGauge k) :
    Convex ℝ {x : Fin n → ℝ | k x ≤ (1 : EReal)} := by
  rcases hk with ⟨hkconv, _, _, _⟩
  have hkconv' : ConvexFunction k := by
    simpa [ConvexFunction] using hkconv
  exact (convexFunction_level_sets_convex (f := k) hkconv' (1 : EReal)).2

/-- The gauge of the unit sublevel set of a finite-valued gauge agrees with `toReal`. -/
lemma IsGauge.gaugeFunction_sublevel_one_eq_toReal {n : ℕ} {k : (Fin n → ℝ) → EReal}
    (hk : IsGauge k) (hk_finite : ∀ x, k x ≠ ⊤) :
    ∀ x, gaugeFunction {x : Fin n → ℝ | k x ≤ (1 : EReal)} x = (k x).toReal := by
  classical
  intro x
  let C : Set (Fin n → ℝ) := {x | k x ≤ (1 : EReal)}
  have hk' : IsGauge k := hk
  rcases hk with ⟨_, hnonneg, hhom, _⟩
  let S : Set ℝ := {r : ℝ | 0 ≤ r ∧ ∃ y ∈ C, x = r • y}
  set r0 : ℝ := (k x).toReal
  have hk_ne_bot : k x ≠ (⊥ : EReal) := IsGauge.ne_bot hk' x
  have hk_ne_top : k x ≠ ⊤ := hk_finite x
  have hk_eq : k x = (r0 : EReal) := by
    simpa [r0] using (EReal.coe_toReal (x := k x) hk_ne_top hk_ne_bot).symm
  have h0le_real : 0 ≤ r0 := by
    have h0le : (0 : EReal) ≤ k x := hnonneg x
    have htoReal : (0 : EReal).toReal ≤ (k x).toReal :=
      EReal.toReal_le_toReal h0le (by simp) hk_ne_top
    simpa [r0] using htoReal
  have hS_bdd : BddBelow S := by
    refine ⟨0, ?_⟩
    intro r hr
    exact hr.1
  have hr0mem : r0 ≠ 0 → r0 ∈ S := by
    intro hr0
    have hr0pos : 0 < r0 := lt_of_le_of_ne h0le_real (by symm; exact hr0)
    refine ⟨h0le_real, (1 / r0) • x, ?_, ?_⟩
    · have hnonneg_inv : 0 ≤ (1 / r0) := by
        simpa [one_div] using (inv_nonneg.mpr (le_of_lt hr0pos))
      have hhomx : k ((1 / r0) • x) = ((1 / r0 : ℝ) : EReal) * k x := by
        simpa using (hhom x (1 / r0) hnonneg_inv)
      have hkx' : k ((1 / r0) • x) = (1 : EReal) := by
        calc
          k ((1 / r0) • x) = ((1 / r0 : ℝ) : EReal) * k x := hhomx
          _ = ((1 / r0 : ℝ) : EReal) * (r0 : EReal) := by simp [hk_eq]
          _ = ((r0⁻¹ * r0 : ℝ) : EReal) := by
            simp [one_div, EReal.coe_mul]
          _ = (1 : EReal) := by
            have : (r0⁻¹ * r0 : ℝ) = 1 := by field_simp [hr0]
            exact_mod_cast this
      have hle : k ((1 / r0) • x) ≤ (1 : EReal) := by
        calc
          k ((1 / r0) • x) = (1 : EReal) := hkx'
          _ ≤ (1 : EReal) := le_rfl
      simpa [C] using hle
    · have hx_eq' : r0 • ((1 / r0) • x) = x := by
        simp [smul_smul, hr0, div_eq_mul_inv]
      simpa using hx_eq'.symm
  have hS_nonempty : S.Nonempty := by
    by_cases hr0 : r0 = 0
    · have hkx0 : k x = (0 : EReal) := by
        simpa [r0, hr0] using hk_eq
      have h0le : (0 : EReal) ≤ (1 : EReal) := by
        exact_mod_cast (show (0 : ℝ) ≤ (1 : ℝ) by norm_num)
      have hxC : x ∈ C := by
        simp [C, hkx0, h0le]
      refine ⟨1, ?_⟩
      refine ⟨by norm_num, x, hxC, ?_⟩
      simp
    · exact ⟨r0, hr0mem hr0⟩
  have hlb' : r0 ≤ sInf S := by
    refine le_csInf hS_nonempty ?_
    intro r hr
    rcases hr with ⟨hr0, y, hyC, hxy⟩
    have hky_le : k y ≤ (1 : EReal) := by
      simpa [C] using hyC
    have hkx_eq : k x = (r : EReal) * k y := by
      simpa [hxy] using (hhom y r hr0)
    have hky_eq : k y = ((k y).toReal : EReal) := by
      have hky_ne_bot : k y ≠ (⊥ : EReal) := IsGauge.ne_bot hk' y
      have hky_ne_top : k y ≠ ⊤ := hk_finite y
      simpa using (EReal.coe_toReal (x := k y) hky_ne_top hky_ne_bot).symm
    have hky_le_real : (k y).toReal ≤ 1 := by
      have hky_ne_bot : k y ≠ (⊥ : EReal) := IsGauge.ne_bot hk' y
      have htoReal :=
        EReal.toReal_le_toReal hky_le hky_ne_bot (by
          simpa using (EReal.coe_ne_top (1 : ℝ)))
      simpa using htoReal
    have hkx_eq' : k x = ((r * (k y).toReal : ℝ) : EReal) := by
      have hkx_eq'' : k x = (r : EReal) * ((k y).toReal : EReal) := by
        calc
          k x = (r : EReal) * k y := hkx_eq
          _ = (r : EReal) * ((k y).toReal : EReal) := by
            exact congrArg (fun t => (r : EReal) * t) hky_eq
      simpa [EReal.coe_mul] using hkx_eq''
    have hmul_le : r * (k y).toReal ≤ r := by
      have hmul_le' : r * (k y).toReal ≤ r * 1 := mul_le_mul_of_nonneg_left hky_le_real hr0
      simpa using hmul_le'
    have hkx_le : k x ≤ (r : EReal) := by
      have : ((r * (k y).toReal : ℝ) : EReal) ≤ (r : EReal) :=
        (EReal.coe_le_coe_iff).2 hmul_le
      simpa [hkx_eq'] using this
    have htoReal :=
      EReal.toReal_le_toReal hkx_le hk_ne_bot (by simp)
    dsimp [r0]
    exact htoReal
  have hub' : sInf S ≤ r0 := by
    by_cases hr0 : r0 = 0
    · apply le_of_forall_pos_le_add
      intro ε hε
      have hε0 : 0 ≤ ε := le_of_lt hε
      have hεne : ε ≠ 0 := ne_of_gt hε
      have hkx0 : k x = (0 : EReal) := by
        simpa [r0, hr0] using hk_eq
      have hyC : (1 / ε) • x ∈ C := by
        have hnonneg_inv : 0 ≤ (1 / ε) := by
          simpa [one_div] using (inv_nonneg.mpr hε0)
        have hhomx : k ((1 / ε) • x) = ((1 / ε : ℝ) : EReal) * k x := by
          simpa using (hhom x (1 / ε) hnonneg_inv)
        have hkx' : k ((1 / ε) • x) = (0 : EReal) := by
          calc
            k ((1 / ε) • x) = ((1 / ε : ℝ) : EReal) * k x := hhomx
            _ = ((1 / ε : ℝ) : EReal) * (0 : EReal) := by simp [hkx0]
            _ = (0 : EReal) := by simp
        have hle : k ((1 / ε) • x) ≤ (1 : EReal) := by
          have h0le : (0 : EReal) ≤ (1 : EReal) := by
            exact_mod_cast (show (0 : ℝ) ≤ (1 : ℝ) by norm_num)
          calc
            k ((1 / ε) • x) = (0 : EReal) := hkx'
            _ ≤ (1 : EReal) := h0le
        simpa [C] using hle
      have hx_eq : x = ε • ((1 / ε) • x) := by
        have hx_eq' : ε • ((1 / ε) • x) = x := by
          simp [smul_smul, hεne, div_eq_mul_inv]
        simpa using hx_eq'.symm
      have hmem : ε ∈ S := by
        refine ⟨hε0, (1 / ε) • x, hyC, ?_⟩
        simpa using hx_eq
      have hsInf_le : sInf S ≤ ε := csInf_le hS_bdd hmem
      simpa [hr0] using hsInf_le
    · have hr0mem' : r0 ∈ S := hr0mem hr0
      exact csInf_le hS_bdd hr0mem'
  have hfinal : gaugeFunction C x = r0 := by
    have hlb : r0 ≤ gaugeFunction C x := by
      simpa [C, gaugeFunction, S] using hlb'
    have hub : gaugeFunction C x ≤ r0 := by
      simpa [C, gaugeFunction, S] using hub'
    exact le_antisymm hub hlb
  simpa [C, r0] using hfinal

/-- The gauge of the unit sublevel set of a finite-valued gauge agrees with `k`. -/
lemma IsGauge.gaugeFunction_sublevel_one_eq {n : ℕ} {k : (Fin n → ℝ) → EReal}
    (hk : IsGauge k) (hk_finite : ∀ x, k x ≠ ⊤) :
    (fun x => (gaugeFunction {x : Fin n → ℝ | k x ≤ (1 : EReal)} x : EReal)) = k := by
  funext x
  have hreal :
      gaugeFunction {x : Fin n → ℝ | k x ≤ (1 : EReal)} x = (k x).toReal :=
    (IsGauge.gaugeFunction_sublevel_one_eq_toReal (k := k) hk hk_finite) x
  have hk_ne_top : k x ≠ ⊤ := hk_finite x
  have hk_ne_bot : k x ≠ (⊥ : EReal) := IsGauge.ne_bot hk x
  have hk_eq : ((k x).toReal : EReal) = k x :=
    EReal.coe_toReal (x := k x) hk_ne_top hk_ne_bot
  have hreal' :
      (gaugeFunction {x : Fin n → ℝ | k x ≤ (1 : EReal)} x : EReal) =
        ((k x).toReal : EReal) := by
    exact_mod_cast hreal
  simpa [hk_eq] using hreal'

/-- Text 15.0.2: Every gauge `k` can be represented as `k = γ(· | C)` for some nonempty convex set
`C`. In this development, `γ(· | C)` is represented by `fun x => (gaugeFunction C x : EReal)`. -/
lemma IsGauge.exists_set_eq_gaugeFunction {n : ℕ} {k : (Fin n → ℝ) → EReal} (hk : IsGauge k)
    (hk_finite : ∀ x, k x ≠ ⊤) :
    ∃ C : Set (Fin n → ℝ), C.Nonempty ∧ Convex ℝ C ∧ k = fun x => (gaugeFunction C x : EReal) := by
  classical
  let C : Set (Fin n → ℝ) := {x | k x ≤ (1 : EReal)}
  refine ⟨C, ?_, ?_, ?_⟩
  · have hne : ({x : Fin n → ℝ | k x ≤ (1 : EReal)}).Nonempty :=
      IsGauge.sublevel_one_nonempty (k := k) hk
    simpa [C] using hne
  · have hconv : Convex ℝ {x : Fin n → ℝ | k x ≤ (1 : EReal)} :=
      IsGauge.convex_sublevel_one (k := k) hk
    simpa [C] using hconv
  · funext x
    have hreal :
        gaugeFunction {x : Fin n → ℝ | k x ≤ (1 : EReal)} x = (k x).toReal :=
      (IsGauge.gaugeFunction_sublevel_one_eq_toReal (k := k) hk hk_finite) x
    have hk_ne_top : k x ≠ ⊤ := hk_finite x
    have hk_ne_bot : k x ≠ (⊥ : EReal) := IsGauge.ne_bot hk x
    have hk_eq : ((k x).toReal : EReal) = k x :=
      EReal.coe_toReal (x := k x) hk_ne_top hk_ne_bot
    have hreal' : (gaugeFunction C x : EReal) = ((k x).toReal : EReal) := by
      exact_mod_cast hreal
    simpa [C, hk_eq] using hreal'.symm

/-- Text 15.0.3: For a nonempty convex set
`C = {x ∈ ℝⁿ | k x ≤ 1}`, one has `γ(· | C) = k`.

In this development, `γ(· | C)` is represented by `fun x => (gaugeFunction C x : EReal)`. -/
lemma gaugeFunction_eq_of_convex_nonempty_eq_sublevel {n : ℕ} {k : (Fin n → ℝ) → EReal}
    {C : Set (Fin n → ℝ)} (hC : C = {x | k x ≤ (1 : EReal)}) (hk : IsGauge k)
    (hk_finite : ∀ x, k x ≠ ⊤) :
    (fun x => (gaugeFunction C x : EReal)) = k := by
  simpa [hC] using (IsGauge.gaugeFunction_sublevel_one_eq (k := k) hk hk_finite)

/-- A closed convex absorbing set is the unit sublevel set of its gauge function. -/
lemma set_eq_gaugeFunction_sublevel_one {n : ℕ} {D : Set (Fin n → ℝ)}
    (hDclosed : IsClosed D) (hDconv : Convex ℝ D) (hD0 : (0 : Fin n → ℝ) ∈ D)
    (hDabs :
      ∀ x : Fin n → ℝ, ∃ lam : ℝ, 0 ≤ lam ∧ x ∈ (fun y => lam • y) '' D) :
    D = {x | (gaugeFunction D x : EReal) ≤ (1 : EReal)} := by
  have hlevel :
      {x : Fin n → ℝ | gaugeFunction D x ≤ (1 : ℝ)} = D := by
    have h := (gaugeFunction_closed_and_level_sets (C := D) hDclosed hDconv hD0 hDabs).2.1
    simpa using (h 1 (by norm_num))
  ext x; constructor
  · intro hx
    have hx' : gaugeFunction D x ≤ (1 : ℝ) := by
      have : x ∈ {x : Fin n → ℝ | gaugeFunction D x ≤ (1 : ℝ)} := by
        simpa [hlevel] using hx
      simpa using this
    exact (EReal.coe_le_coe_iff).2 hx'
  · intro hx
    have hx' : gaugeFunction D x ≤ (1 : ℝ) := (EReal.coe_le_coe_iff).1 hx
    have : x ∈ {x : Fin n → ℝ | gaugeFunction D x ≤ (1 : ℝ)} := by
      simpa using hx'
    simpa [hlevel] using this

/-- If a set's gauge function agrees with `k`, then the set is the `k ≤ 1` sublevel. -/
lemma eq_sublevel_one_of_gaugeFunction_eq {n : ℕ} {k : (Fin n → ℝ) → EReal} {D : Set (Fin n → ℝ)}
    (hDclosed : IsClosed D) (hDconv : Convex ℝ D) (hD0 : (0 : Fin n → ℝ) ∈ D)
    (hDabs :
      ∀ x : Fin n → ℝ, ∃ lam : ℝ, 0 ≤ lam ∧ x ∈ (fun y => lam • y) '' D)
    (hg : (fun x => (gaugeFunction D x : EReal)) = k) :
    D = {x | k x ≤ (1 : EReal)} := by
  have hset :
      D = {x | (gaugeFunction D x : EReal) ≤ (1 : EReal)} :=
    set_eq_gaugeFunction_sublevel_one (n := n) hDclosed hDconv hD0 hDabs
  ext x; constructor
  · intro hx
    have hmem :
        x ∈ {x | (gaugeFunction D x : EReal) ≤ (1 : EReal)} := by
      have hmem' : x ∈ D := hx
      -- Avoid rewriting `D` inside `gaugeFunction D` by using `rw` at the top level.
      rw [hset] at hmem'
      exact hmem'
    have hx' : (gaugeFunction D x : EReal) ≤ (1 : EReal) := by
      simpa using hmem
    have hgx : (gaugeFunction D x : EReal) = k x := by
      simpa using congrArg (fun f => f x) hg
    simpa [hgx] using hx'
  · intro hx
    have hgx : (gaugeFunction D x : EReal) = k x := by
      simpa using congrArg (fun f => f x) hg
    have hx' : (gaugeFunction D x : EReal) ≤ (1 : EReal) := by
      simpa [hgx] using hx
    have hmem :
        x ∈ {x | (gaugeFunction D x : EReal) ≤ (1 : EReal)} := by
      simpa using hx'
    have hmem' : x ∈ D := by
      -- Avoid rewriting `D` inside `gaugeFunction D` by using `rw` at the top level.
      have hmem'' : x ∈ {x | (gaugeFunction D x : EReal) ≤ (1 : EReal)} := hmem
      -- Rewrite the target set back to `D`.
      rw [← hset] at hmem''
      exact hmem''
    simpa using hmem'

/-- Text 15.0.4: If `k` is closed (and finite, positive away from `0`), then the set
`C = {x ∈ ℝⁿ | k x ≤ 1}` is the unique closed convex set containing `0` such that
`γ(· | C) = k`.

In this development, we express "closedness of `k`" as closedness of the book epigraph
`epigraph univ k`, and `γ(· | C)` is represented by `fun x => (gaugeFunction C x : EReal)`. -/
lemma sublevel_one_unique_closed_convex_of_isClosed_epigraph {n : ℕ} {k : (Fin n → ℝ) → EReal}
    (hk : IsGauge k)
    (hk_finite : ∀ x, k x ≠ ⊤)
    (hk_pos : ∀ x, x ≠ 0 → (0 : EReal) < k x)
    (hk_closed : IsClosed (epigraph (S := (Set.univ : Set (Fin n → ℝ))) k)) :
    let C : Set (Fin n → ℝ) := {x | k x ≤ (1 : EReal)}
    IsClosed C ∧
      Convex ℝ C ∧
        (0 : Fin n → ℝ) ∈ C ∧
          (fun x => (gaugeFunction C x : EReal)) = k ∧
            ∀ D : Set (Fin n → ℝ),
              IsClosed D →
                Convex ℝ D →
                  (0 : Fin n → ℝ) ∈ D →
                    (fun x => (gaugeFunction D x : EReal)) = k → D = C := by
  classical
  intro C
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hcont : Continuous (fun x : Fin n → ℝ => (x, (1 : ℝ))) := by
      simpa using (Continuous.prodMk_left (X := (Fin n → ℝ)) (Y := ℝ) (1 : ℝ))
    have hpre :
        (fun x : Fin n → ℝ => (x, (1 : ℝ))) ⁻¹'
            epigraph (S := (Set.univ : Set (Fin n → ℝ))) k =
          {x | k x ≤ (1 : EReal)} := by
      ext x; constructor
      · intro hx; exact hx.2
      · intro hx; exact ⟨Set.mem_univ x, hx⟩
    have hclosed :
        IsClosed ((fun x : Fin n → ℝ => (x, (1 : ℝ))) ⁻¹'
          epigraph (S := (Set.univ : Set (Fin n → ℝ))) k) :=
      hk_closed.preimage hcont
    simpa [C, hpre] using hclosed
  · have hconv : Convex ℝ {x : Fin n → ℝ | k x ≤ (1 : EReal)} :=
      IsGauge.convex_sublevel_one (k := k) hk
    simpa [C] using hconv
  · rcases hk with ⟨_, hnonneg, _, hk0⟩
    have h0le : (0 : EReal) ≤ (1 : EReal) := by
      exact_mod_cast (show (0 : ℝ) ≤ (1 : ℝ) by norm_num)
    simp [C, hk0, h0le]
  · simpa [C] using (IsGauge.gaugeFunction_sublevel_one_eq (k := k) hk hk_finite)
  · intro D hDclosed hDconv hD0 hDg
    have hDabs :
        ∀ x : Fin n → ℝ, ∃ lam : ℝ, 0 ≤ lam ∧ x ∈ (fun y => lam • y) '' D := by
      intro x
      by_cases hx : x = 0
      · refine ⟨0, le_rfl, ?_⟩
        refine ⟨0, hD0, ?_⟩
        simp [hx]
      · let S : Set ℝ := {r : ℝ | 0 ≤ r ∧ ∃ y ∈ D, x = r • y}
        have hDg_x : (gaugeFunction D x : EReal) = k x := by
          simpa using congrArg (fun f => f x) hDg
        have hxpos : (0 : EReal) < (gaugeFunction D x : EReal) := by
          simpa [hDg_x] using (hk_pos x hx)
        have hxpos_real : 0 < gaugeFunction D x := (EReal.coe_pos).1 hxpos
        have hSnonempty : S.Nonempty := by
          by_contra hS
          have hSempty : S = ∅ := by
            apply Set.eq_empty_iff_forall_notMem.mpr
            intro r hr
            exact hS ⟨r, hr⟩
          have hx0 : gaugeFunction D x = 0 := by
            simp [gaugeFunction, S, hSempty, Real.sInf_empty]
          simp [hx0] at hxpos_real
        rcases hSnonempty with ⟨r, hr⟩
        rcases hr with ⟨hr0, y, hyD, hxy⟩
        refine ⟨r, hr0, ?_⟩
        exact ⟨y, hyD, by simp [hxy]⟩
    have hDset :
        D = {x | k x ≤ (1 : EReal)} :=
      eq_sublevel_one_of_gaugeFunction_eq (n := n) (k := k) (D := D)
        hDclosed hDconv hD0 hDabs hDg
    simpa [C] using hDset

/-- Text 15.0.5: Let `k` be a gauge on `ℝⁿ`. Its polar `kᵒ : ℝⁿ → [0, +∞]` is defined by
`kᵒ x⋆ = inf { μ⋆ ≥ 0 | ⟪x, x⋆⟫ ≤ μ⋆ * k x for all x }`.

In this development, `ℝⁿ` is `Fin n → ℝ` and we represent the `inf` as `sInf` in `EReal`. -/
noncomputable def polarGauge {n : ℕ} (k : (Fin n → ℝ) → EReal) (xStar : Fin n → ℝ) : EReal :=
  sInf {μStar : EReal | 0 ≤ μStar ∧ ∀ x : Fin n → ℝ, ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ μStar * k x}

/-- The polar gauge is nonnegative. -/
lemma polarGauge_nonneg {n : ℕ} {k : (Fin n → ℝ) → EReal} (xStar : Fin n → ℝ) :
    (0 : EReal) ≤ polarGauge k xStar := by
  unfold polarGauge
  refine le_sInf ?_
  intro μ hμ
  exact hμ.1

/-- The polar gauge of any function vanishes at `0`. -/
lemma polarGauge_zero {n : ℕ} (k : (Fin n → ℝ) → EReal) : polarGauge k (0 : Fin n → ℝ) = 0 := by
  unfold polarGauge
  have h0mem :
      (0 : EReal) ∈
        {μStar : EReal |
          0 ≤ μStar ∧ ∀ x : Fin n → ℝ, ((x ⬝ᵥ (0 : Fin n → ℝ) : ℝ) : EReal) ≤ μStar * k x} := by
    refine ⟨le_rfl, ?_⟩
    intro x
    simp
  have h0le :
      (0 : EReal) ≤
        sInf
          {μStar : EReal |
            0 ≤ μStar ∧
              ∀ x : Fin n → ℝ, ((x ⬝ᵥ (0 : Fin n → ℝ) : ℝ) : EReal) ≤ μStar * k x} := by
    refine le_sInf ?_
    intro μ hμ
    exact hμ.1
  have hle0 :
      sInf
          {μStar : EReal |
            0 ≤ μStar ∧
              ∀ x : Fin n → ℝ, ((x ⬝ᵥ (0 : Fin n → ℝ) : ℝ) : EReal) ≤ μStar * k x} ≤
        (0 : EReal) := by
    exact sInf_le h0mem
  exact le_antisymm hle0 h0le

/-- The polar gauge never attains `⊥`. -/
lemma polarGauge_ne_bot {n : ℕ} {k : (Fin n → ℝ) → EReal} (xStar : Fin n → ℝ) :
    polarGauge k xStar ≠ (⊥ : EReal) := by
  intro hbot
  have h0le : (0 : EReal) ≤ polarGauge k xStar := polarGauge_nonneg (k := k) xStar
  have h0le' : (0 : EReal) ≤ (⊥ : EReal) := by
    calc
      (0 : EReal) ≤ polarGauge k xStar := h0le
      _ = (⊥ : EReal) := hbot
  have h0eq : (0 : EReal) = (⊥ : EReal) := (le_bot_iff).1 h0le'
  have h0ne : (0 : EReal) ≠ (⊥ : EReal) := by simp
  exact h0ne h0eq

/-- Scaling a feasible multiplier remains feasible for the scaled dual vector. -/
lemma polarGauge_feasible_smul {n : ℕ} {k : (Fin n → ℝ) → EReal} {xStar : Fin n → ℝ}
    {μ : EReal} (hμ : 0 ≤ μ ∧ ∀ x : Fin n → ℝ, ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ μ * k x)
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ ((t : ℝ) : EReal) * μ ∧
      ∀ x : Fin n → ℝ,
        ((x ⬝ᵥ (t • xStar) : ℝ) : EReal) ≤ (((t : ℝ) : EReal) * μ) * k x := by
  refine ⟨?_, ?_⟩
  · exact mul_nonneg (by exact_mod_cast ht) hμ.1
  · intro x
    have hdot :
        ((x ⬝ᵥ (t • xStar) : ℝ) : EReal) =
          ((t : ℝ) : EReal) * ((x ⬝ᵥ xStar : ℝ) : EReal) := by
      simp [dotProduct_smul, smul_eq_mul, EReal.coe_mul]
    have hmul :
        ((t : ℝ) : EReal) * ((x ⬝ᵥ xStar : ℝ) : EReal) ≤
          ((t : ℝ) : EReal) * (μ * k x) :=
      mul_le_mul_of_nonneg_left (hμ.2 x) (by exact_mod_cast ht)
    have hmul' :
        ((t : ℝ) : EReal) * (μ * k x) = (((t : ℝ) : EReal) * μ) * k x := by
      simp [mul_assoc]
    simpa [hdot, hmul'] using hmul

/-- Adding feasible multipliers is feasible for the sum of dual vectors. -/
lemma polarGauge_feasible_add {n : ℕ} {k : (Fin n → ℝ) → EReal} {xStar₁ xStar₂ : Fin n → ℝ}
    {μ₁ μ₂ : EReal}
    (hμ₁ : 0 ≤ μ₁ ∧ ∀ x : Fin n → ℝ, ((x ⬝ᵥ xStar₁ : ℝ) : EReal) ≤ μ₁ * k x)
    (hμ₂ : 0 ≤ μ₂ ∧ ∀ x : Fin n → ℝ, ((x ⬝ᵥ xStar₂ : ℝ) : EReal) ≤ μ₂ * k x) :
    0 ≤ μ₁ + μ₂ ∧
      ∀ x : Fin n → ℝ,
        ((x ⬝ᵥ (xStar₁ + xStar₂) : ℝ) : EReal) ≤ (μ₁ + μ₂) * k x := by
  refine ⟨add_nonneg hμ₁.1 hμ₂.1, ?_⟩
  intro x
  have hdot :
      ((x ⬝ᵥ (xStar₁ + xStar₂) : ℝ) : EReal) =
        ((x ⬝ᵥ xStar₁ : ℝ) : EReal) + ((x ⬝ᵥ xStar₂ : ℝ) : EReal) := by
    simp [dotProduct_add]
  have hle : ((x ⬝ᵥ xStar₁ : ℝ) : EReal) + ((x ⬝ᵥ xStar₂ : ℝ) : EReal) ≤
      μ₁ * k x + μ₂ * k x :=
    add_le_add (hμ₁.2 x) (hμ₂.2 x)
  have hmul : μ₁ * k x + μ₂ * k x = (μ₁ + μ₂) * k x := by
    simpa using
      (EReal.right_distrib_of_nonneg (a := μ₁) (b := μ₂) (c := k x) hμ₁.1 hμ₂.1).symm
  simpa [hdot, hmul] using hle

/-- A feasible sum bounds the polar gauge of the summed dual vector. -/
lemma polarGauge_le_of_feasible_add {n : ℕ} {k : (Fin n → ℝ) → EReal}
    {xStar₁ xStar₂ : Fin n → ℝ} {μ₁ μ₂ : EReal}
    (hμ₁ : 0 ≤ μ₁ ∧ ∀ x : Fin n → ℝ, ((x ⬝ᵥ xStar₁ : ℝ) : EReal) ≤ μ₁ * k x)
    (hμ₂ : 0 ≤ μ₂ ∧ ∀ x : Fin n → ℝ, ((x ⬝ᵥ xStar₂ : ℝ) : EReal) ≤ μ₂ * k x) :
    polarGauge k (xStar₁ + xStar₂) ≤ μ₁ + μ₂ := by
  unfold polarGauge
  exact sInf_le (polarGauge_feasible_add (xStar₁ := xStar₁) (xStar₂ := xStar₂) hμ₁ hμ₂)

/-- A feasible scaling bounds the polar gauge of the scaled dual vector. -/
lemma polarGauge_le_of_feasible_smul {n : ℕ} {k : (Fin n → ℝ) → EReal} {xStar : Fin n → ℝ}
    {μ : EReal} (hμ : 0 ≤ μ ∧ ∀ x : Fin n → ℝ, ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ μ * k x)
    {t : ℝ} (ht : 0 ≤ t) :
    polarGauge k (t • xStar) ≤ ((t : ℝ) : EReal) * μ := by
  unfold polarGauge
  exact sInf_le (polarGauge_feasible_smul (xStar := xStar) (μ := μ) hμ ht)

/-- The polar gauge is positively homogeneous. -/
lemma polarGauge_posHom {n : ℕ} {k : (Fin n → ℝ) → EReal} :
    PositivelyHomogeneous (polarGauge k) := by
  intro xStar t ht
  have ht0 : 0 ≤ t := le_of_lt ht
  have htinv0 : 0 ≤ (t⁻¹ : ℝ) := inv_nonneg.mpr ht0
  have hle1 :
      ((t⁻¹ : ℝ) : EReal) * polarGauge k (t • xStar) ≤ polarGauge k xStar := by
    change
        ((t⁻¹ : ℝ) : EReal) * polarGauge k (t • xStar) ≤
          sInf
            {μ : EReal |
              0 ≤ μ ∧ ∀ x : Fin n → ℝ, ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ μ * k x}
    refine le_sInf ?_
    intro μ hμ
    have hμ' := polarGauge_feasible_smul (xStar := xStar) (μ := μ) hμ ht0
    have hpolar : polarGauge k (t • xStar) ≤ ((t : ℝ) : EReal) * μ := by
      unfold polarGauge
      exact sInf_le hμ'
    have hmul :
        ((t⁻¹ : ℝ) : EReal) * polarGauge k (t • xStar) ≤
          ((t⁻¹ : ℝ) : EReal) * (((t : ℝ) : EReal) * μ) :=
      mul_le_mul_of_nonneg_left hpolar (by exact_mod_cast htinv0)
    simpa [mul_assoc, section13_mul_inv_mul_cancel_pos_real (a := t) ht] using hmul
  have hle_left : polarGauge k (t • xStar) ≤ ((t : ℝ) : EReal) * polarGauge k xStar := by
    have hmul :
        ((t : ℝ) : EReal) * (((t⁻¹ : ℝ) : EReal) * polarGauge k (t • xStar)) ≤
          ((t : ℝ) : EReal) * polarGauge k xStar :=
      mul_le_mul_of_nonneg_left hle1 (by exact_mod_cast ht0)
    simpa [mul_assoc, section13_mul_mul_inv_cancel_pos_real (a := t) ht] using hmul
  have hle_right : ((t : ℝ) : EReal) * polarGauge k xStar ≤ polarGauge k (t • xStar) := by
    change
        ((t : ℝ) : EReal) * polarGauge k xStar ≤
          sInf
            {μ : EReal |
              0 ≤ μ ∧ ∀ x : Fin n → ℝ, ((x ⬝ᵥ (t • xStar) : ℝ) : EReal) ≤ μ * k x}
    refine le_sInf ?_
    intro μ hμ
    have hμ' := polarGauge_feasible_smul (xStar := t • xStar) (μ := μ) hμ htinv0
    have hμ'' :
        0 ≤ ((t⁻¹ : ℝ) : EReal) * μ ∧
          ∀ x : Fin n → ℝ,
            ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ (((t⁻¹ : ℝ) : EReal) * μ) * k x := by
      simpa [smul_smul, inv_mul_cancel, ht.ne', one_smul] using hμ'
    have hpolar : polarGauge k xStar ≤ ((t⁻¹ : ℝ) : EReal) * μ := by
      unfold polarGauge
      exact sInf_le hμ''
    have hmul :
        ((t : ℝ) : EReal) * polarGauge k xStar ≤
          ((t : ℝ) : EReal) * (((t⁻¹ : ℝ) : EReal) * μ) :=
      mul_le_mul_of_nonneg_left hpolar (by exact_mod_cast ht0)
    simpa [mul_assoc, section13_mul_mul_inv_cancel_pos_real (a := t) ht] using hmul
  exact le_antisymm hle_left hle_right

/-- The polar gauge is subadditive. -/
lemma polarGauge_add_le {n : ℕ} {k : (Fin n → ℝ) → EReal}
    (xStar₁ xStar₂ : Fin n → ℝ) :
    polarGauge k (xStar₁ + xStar₂) ≤ polarGauge k xStar₁ + polarGauge k xStar₂ := by
  classical
  by_cases htop1 : polarGauge k xStar₁ = ⊤
  ·
    have hbot2 : polarGauge k xStar₂ ≠ ⊥ := polarGauge_ne_bot (k := k) xStar₂
    simp [htop1, EReal.top_add_of_ne_bot hbot2]
  by_cases htop2 : polarGauge k xStar₂ = ⊤
  ·
    have hbot1 : polarGauge k xStar₁ ≠ ⊥ := polarGauge_ne_bot (k := k) xStar₁
    simp [htop2, EReal.add_top_of_ne_bot hbot1]
  have hbot1 : polarGauge k xStar₁ ≠ ⊥ := polarGauge_ne_bot (k := k) xStar₁
  have hbot2 : polarGauge k xStar₂ ≠ ⊥ := polarGauge_ne_bot (k := k) xStar₂
  set a : ℝ := (polarGauge k xStar₁).toReal
  set b : ℝ := (polarGauge k xStar₂).toReal
  have ha : polarGauge k xStar₁ = (a : EReal) := by
    simpa [a] using (EReal.coe_toReal (x := polarGauge k xStar₁) htop1 hbot1).symm
  have hb : polarGauge k xStar₂ = (b : EReal) := by
    simpa [b] using (EReal.coe_toReal (x := polarGauge k xStar₂) htop2 hbot2).symm
  have hle_eps :
      ∀ ε : ℝ, 0 < ε →
        polarGauge k (xStar₁ + xStar₂) ≤ ((a + b + ε : ℝ) : EReal) := by
    intro ε hε
    have hε2 : 0 < ε / 2 := by linarith
    have h1_lt : polarGauge k xStar₁ < ((a + ε / 2 : ℝ) : EReal) := by
      have : (a : EReal) < ((a + ε / 2 : ℝ) : EReal) := by
        exact (EReal.coe_lt_coe_iff).2 (by linarith)
      simpa [ha] using this
    obtain ⟨μ1, hμ1mem, hμ1lt⟩ := (sInf_lt_iff).1 h1_lt
    have h2_lt : polarGauge k xStar₂ < ((b + ε / 2 : ℝ) : EReal) := by
      have : (b : EReal) < ((b + ε / 2 : ℝ) : EReal) := by
        exact (EReal.coe_lt_coe_iff).2 (by linarith)
      simpa [hb] using this
    obtain ⟨μ2, hμ2mem, hμ2lt⟩ := (sInf_lt_iff).1 h2_lt
    have hle :
        polarGauge k (xStar₁ + xStar₂) ≤ μ1 + μ2 :=
      polarGauge_le_of_feasible_add (xStar₁ := xStar₁) (xStar₂ := xStar₂) hμ1mem hμ2mem
    have hle_sum :
        μ1 + μ2 ≤ ((a + b + ε : ℝ) : EReal) := by
      have hle' :
          μ1 + μ2 ≤ ((a + ε / 2 : ℝ) : EReal) + ((b + ε / 2 : ℝ) : EReal) :=
        add_le_add (le_of_lt hμ1lt) (le_of_lt hμ2lt)
      have hsumE :
          ((a + ε / 2 : ℝ) : EReal) + ((b + ε / 2 : ℝ) : EReal) =
            ((a + b + ε : ℝ) : EReal) := by
        have hsum : (a + ε / 2) + (b + ε / 2) = a + b + ε := by ring
        exact_mod_cast hsum
      calc
        μ1 + μ2 ≤ ((a + ε / 2 : ℝ) : EReal) + ((b + ε / 2 : ℝ) : EReal) := hle'
        _ = ((a + b + ε : ℝ) : EReal) := hsumE
    exact le_trans hle hle_sum
  have htop12 : polarGauge k (xStar₁ + xStar₂) ≠ ⊤ := by
    have hle := hle_eps 1 (by norm_num)
    intro htop
    have hle' : (⊤ : EReal) ≤ ((a + b + 1 : ℝ) : EReal) := by
      simpa [htop] using hle
    exact (not_le_of_gt (EReal.coe_lt_top (a + b + 1))) hle'
  have hbot12 : polarGauge k (xStar₁ + xStar₂) ≠ ⊥ :=
    polarGauge_ne_bot (k := k) (xStar₁ + xStar₂)
  set c : ℝ := (polarGauge k (xStar₁ + xStar₂)).toReal
  have hc : polarGauge k (xStar₁ + xStar₂) = (c : EReal) := by
    simpa [c] using
      (EReal.coe_toReal (x := polarGauge k (xStar₁ + xStar₂))
          htop12 hbot12).symm
  have hcle : c ≤ a + b := by
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    have hle' := hle_eps ε hε
    have hle'' : (c : EReal) ≤ ((a + b + ε : ℝ) : EReal) := by
      simpa [hc] using hle'
    exact (EReal.coe_le_coe_iff).1 hle''
  have : (c : EReal) ≤ ((a + b : ℝ) : EReal) :=
    (EReal.coe_le_coe_iff).2 hcle
  simpa [hc, ha, hb] using this

/-- The polar gauge is a gauge. -/
lemma polarGauge_isGauge {n : ℕ} (k : (Fin n → ℝ) → EReal) : IsGauge (polarGauge k) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    have hconv : ConvexFunction (polarGauge k) :=
      convex_of_subadditive_posHom (hpos := polarGauge_posHom)
        (hsub := polarGauge_add_le (k := k))
        (hnotbot := by intro x; exact polarGauge_ne_bot (k := k) x)
    simpa [ConvexFunction] using hconv
  · intro x
    exact polarGauge_nonneg (k := k) x
  · intro x r hr
    by_cases hr0 : r = 0
    · simp [hr0, polarGauge_zero]
    · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
      simpa using (polarGauge_posHom (k := k) x r hrpos)
  · exact polarGauge_zero k

/-- A feasible `μ` for the polar gauge bounds each ratio `⟪x, x⋆⟫ / k x` when `x ≠ 0`. -/
lemma polarGauge_ratio_le_of_feasible {n : ℕ} {k : (Fin n → ℝ) → EReal} (hk : IsGauge k)
    (hk_finite : ∀ x, k x ≠ ⊤) (hk_pos : ∀ x, x ≠ 0 → (0 : EReal) < k x)
    {xStar : Fin n → ℝ} {μ : EReal} (hμ0 : 0 ≤ μ)
    (hμ : ∀ x, ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ μ * k x) {x : Fin n → ℝ} (hx : x ≠ 0) :
    (((x ⬝ᵥ xStar : ℝ) / (k x).toReal : ℝ) : EReal) ≤ μ := by
  classical
  by_cases hμ_top : μ = ⊤
  · simp [hμ_top]
  have hk_ne_bot : k x ≠ (⊥ : EReal) := IsGauge.ne_bot hk x
  have hk_ne_top : k x ≠ ⊤ := hk_finite x
  have hk_eq : k x = ((k x).toReal : EReal) := by
    simpa using (EReal.coe_toReal (x := k x) hk_ne_top hk_ne_bot).symm
  have hμ_ne_bot : μ ≠ (⊥ : EReal) := by
    have hbot0 : (⊥ : EReal) < (0 : EReal) := by simp
    have hbotμ : (⊥ : EReal) < μ := lt_of_lt_of_le hbot0 hμ0
    exact ne_of_gt hbotμ
  have hμ_eq : μ = ((μ.toReal : ℝ) : EReal) := by
    simpa using (EReal.coe_toReal (x := μ) hμ_top hμ_ne_bot).symm
  have hμx : ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ μ * k x := hμ x
  have hμx' :
      ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ ((μ.toReal : ℝ) : EReal) * ((k x).toReal : EReal) := by
    have hμx' := hμx
    rw [hμ_eq, hk_eq] at hμx'
    exact hμx'
  have hμx'' :
      ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ ((μ.toReal * (k x).toReal : ℝ) : EReal) := by
    simpa [EReal.coe_mul, mul_comm, mul_left_comm, mul_assoc] using hμx'
  have hμx_real :
      (x ⬝ᵥ xStar : ℝ) ≤ μ.toReal * (k x).toReal :=
    (EReal.coe_le_coe_iff).1 hμx''
  have hnonneg : ∀ x, 0 ≤ k x := hk.2.1
  have h0le : (0 : EReal) ≤ k x := hnonneg x
  have hk_toReal_nonneg : 0 ≤ (k x).toReal := by
    have htoReal := EReal.toReal_le_toReal h0le (by simp) hk_ne_top
    simpa using htoReal
  have hk_toReal_ne_zero : (k x).toReal ≠ 0 := by
    intro h0
    have hk_eq' : ((k x).toReal : EReal) = k x :=
      EReal.coe_toReal (x := k x) hk_ne_top hk_ne_bot
    have hk_zero : k x = (0 : EReal) := by
      calc
        k x = ((k x).toReal : EReal) := hk_eq'.symm
        _ = (0 : EReal) := by simp [h0]
    exact (ne_of_gt (hk_pos x hx)) hk_zero
  have hk_toReal_pos : 0 < (k x).toReal :=
    lt_of_le_of_ne hk_toReal_nonneg (Ne.symm hk_toReal_ne_zero)
  have hratio_le : (x ⬝ᵥ xStar : ℝ) / (k x).toReal ≤ μ.toReal :=
    (div_le_iff₀ hk_toReal_pos).2 (by simpa [mul_comm] using hμx_real)
  have hratio_le_ereal :
      (((x ⬝ᵥ xStar : ℝ) / (k x).toReal : ℝ) : EReal) ≤ ((μ.toReal : ℝ) : EReal) := by
    exact (EReal.coe_le_coe_iff).2 hratio_le
  calc
    (((x ⬝ᵥ xStar : ℝ) / (k x).toReal : ℝ) : EReal) ≤ ((μ.toReal : ℝ) : EReal) :=
      hratio_le_ereal
    _ = μ := hμ_eq.symm

/-- A bound on the ratio yields the product bound when the coefficient is finite. -/
lemma polarGauge_mul_le_of_ratio_le {n : ℕ} {k : (Fin n → ℝ) → EReal} (hk : IsGauge k)
    (hk_finite : ∀ x, k x ≠ ⊤) (hk_pos : ∀ x, x ≠ 0 → (0 : EReal) < k x)
    {xStar : Fin n → ℝ} {μ : EReal} (hμ_top : μ ≠ ⊤) (hμ_ne_bot : μ ≠ ⊥)
    {x : Fin n → ℝ} (hx : x ≠ 0)
    (hμ : (((x ⬝ᵥ xStar : ℝ) / (k x).toReal : ℝ) : EReal) ≤ μ) :
    ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ μ * k x := by
  classical
  have hk_ne_bot : k x ≠ (⊥ : EReal) := IsGauge.ne_bot hk x
  have hk_ne_top : k x ≠ ⊤ := hk_finite x
  have hk_eq : k x = ((k x).toReal : EReal) := by
    simpa using (EReal.coe_toReal (x := k x) hk_ne_top hk_ne_bot).symm
  have hμ_eq : μ = ((μ.toReal : ℝ) : EReal) := by
    simpa using (EReal.coe_toReal (x := μ) hμ_top hμ_ne_bot).symm
  have hnonneg : ∀ x, 0 ≤ k x := hk.2.1
  have h0le : (0 : EReal) ≤ k x := hnonneg x
  have hk_toReal_nonneg : 0 ≤ (k x).toReal := by
    have htoReal := EReal.toReal_le_toReal h0le (by simp) hk_ne_top
    simpa using htoReal
  have hk_toReal_ne_zero : (k x).toReal ≠ 0 := by
    intro h0
    have hk_eq' : ((k x).toReal : EReal) = k x :=
      EReal.coe_toReal (x := k x) hk_ne_top hk_ne_bot
    have hk_zero : k x = (0 : EReal) := by
      calc
        k x = ((k x).toReal : EReal) := hk_eq'.symm
        _ = (0 : EReal) := by simp [h0]
    exact (ne_of_gt (hk_pos x hx)) hk_zero
  have hk_toReal_pos : 0 < (k x).toReal :=
    lt_of_le_of_ne hk_toReal_nonneg (Ne.symm hk_toReal_ne_zero)
  have hμ' :
      (((x ⬝ᵥ xStar : ℝ) / (k x).toReal : ℝ) : EReal) ≤ ((μ.toReal : ℝ) : EReal) := by
    have hμ' := hμ
    rw [hμ_eq] at hμ'
    exact hμ'
  have hμ_real : (x ⬝ᵥ xStar : ℝ) / (k x).toReal ≤ μ.toReal :=
    (EReal.coe_le_coe_iff).1 hμ'
  have hmul_real : (x ⬝ᵥ xStar : ℝ) ≤ μ.toReal * (k x).toReal :=
    (div_le_iff₀ hk_toReal_pos).1 hμ_real
  have hmul_ereal :
      ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ ((μ.toReal * (k x).toReal : ℝ) : EReal) := by
    exact (EReal.coe_le_coe_iff).2 hmul_real
  have hmul_ereal' :
      ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ ((μ.toReal : ℝ) : EReal) * ((k x).toReal : EReal) := by
    simpa [EReal.coe_mul, mul_comm, mul_left_comm, mul_assoc] using hmul_ereal
  have hmul_eq : ((μ.toReal : ℝ) : EReal) * ((k x).toReal : EReal) = μ * k x := by
    rw [hμ_eq.symm, hk_eq.symm]
  exact hmul_ereal'.trans_eq hmul_eq

/-- Text 15.0.6: If a gauge `k` is finite everywhere and positive except at the origin, then `kᵒ`
admits the equivalent formula
`kᵒ x⋆ = sup_{x ≠ 0} ⟪x, x⋆⟫ / k x`.

In this development, `kᵒ` is `polarGauge k`, and we express `sup` as a `sSup` over the image of
`x ↦ ⟪x, x⋆⟫ / (k x)` (using `EReal.toReal` to form a real quotient). -/
lemma polarGauge_eq_sSup_div {n : ℕ} {k : (Fin n → ℝ) → EReal} (hk : IsGauge k)
    (hk_finite : ∀ x, k x ≠ ⊤) (hk_pos : ∀ x, x ≠ 0 → (0 : EReal) < k x)
    (h_nonempty : ∃ x : Fin n → ℝ, x ≠ 0) (xStar : Fin n → ℝ) :
    polarGauge k xStar =
      sSup
        ((fun x : Fin n → ℝ =>
              (((x ⬝ᵥ xStar : ℝ) / (k x).toReal : ℝ) : EReal)) '' {x | x ≠ 0}) := by
  classical
  let R : Set EReal :=
    ((fun x : Fin n → ℝ => (((x ⬝ᵥ xStar : ℝ) / (k x).toReal : ℝ) : EReal)) '' {x | x ≠ 0})
  let M : Set EReal :=
    {μ : EReal | 0 ≤ μ ∧ ∀ x : Fin n → ℝ, ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ μ * k x}
  have hSup_le : sSup R ≤ sInf M := by
    refine sSup_le ?_
    intro r hr
    rcases hr with ⟨x, hx, rfl⟩
    refine le_sInf ?_
    intro μ hμ
    rcases hμ with ⟨hμ0, hμ⟩
    exact
      polarGauge_ratio_le_of_feasible (hk := hk) (hk_finite := hk_finite) (hk_pos := hk_pos)
        (xStar := xStar) hμ0 hμ hx
  have hInf_le : sInf M ≤ sSup R := by
    let μ0 : EReal := sSup R
    have hμ0_nonneg : 0 ≤ μ0 := by
      rcases h_nonempty with ⟨x0, hx0⟩
      by_cases hxStar0 : xStar = 0
      · have hrmem : (((x0 ⬝ᵥ xStar : ℝ) / (k x0).toReal : ℝ) : EReal) ∈ R := by
          exact ⟨x0, hx0, rfl⟩
        have hratio_nonneg :
            (0 : EReal) ≤ (((x0 ⬝ᵥ xStar : ℝ) / (k x0).toReal : ℝ) : EReal) := by
          simp [hxStar0]
        have hratio_le : (((x0 ⬝ᵥ xStar : ℝ) / (k x0).toReal : ℝ) : EReal) ≤ μ0 :=
          le_sSup hrmem
        exact le_trans hratio_nonneg hratio_le
      · have hxStar_ne : xStar ≠ 0 := hxStar0
        have hrmem :
            (((xStar ⬝ᵥ xStar : ℝ) / (k xStar).toReal : ℝ) : EReal) ∈ R := by
          exact ⟨xStar, hxStar_ne, rfl⟩
        have hdot_nonneg : (0 : ℝ) ≤ (xStar ⬝ᵥ xStar : ℝ) := by
          simpa using (dotProduct_self_star_nonneg (v := xStar))
        have hnonneg : ∀ x, 0 ≤ k x := hk.2.1
        have h0le : (0 : EReal) ≤ k xStar := hnonneg xStar
        have hk_toReal_nonneg : 0 ≤ (k xStar).toReal := by
          have htoReal := EReal.toReal_le_toReal h0le (by simp) (hk_finite xStar)
          simpa using htoReal
        have hratio_nonneg_real :
            (0 : ℝ) ≤ (xStar ⬝ᵥ xStar : ℝ) / (k xStar).toReal :=
          div_nonneg hdot_nonneg hk_toReal_nonneg
        have hratio_nonneg :
            (0 : EReal) ≤
              (((xStar ⬝ᵥ xStar : ℝ) / (k xStar).toReal : ℝ) : EReal) := by
          change ((0 : ℝ) : EReal) ≤
            (((xStar ⬝ᵥ xStar : ℝ) / (k xStar).toReal : ℝ) : EReal)
          exact (EReal.coe_le_coe_iff).2 hratio_nonneg_real
        have hratio_le :
            (((xStar ⬝ᵥ xStar : ℝ) / (k xStar).toReal : ℝ) : EReal) ≤ μ0 :=
          le_sSup hrmem
        exact le_trans hratio_nonneg hratio_le
    have hμ0_mem : μ0 ∈ M := by
      refine ⟨hμ0_nonneg, ?_⟩
      intro x
      by_cases hx : x = 0
      · subst hx
        have hk0 : k 0 = 0 := hk.2.2.2
        simp [hk0]
      · have hrmem :
            (((x ⬝ᵥ xStar : ℝ) / (k x).toReal : ℝ) : EReal) ∈ R := by
          exact ⟨x, hx, rfl⟩
        have hratio_le :
            (((x ⬝ᵥ xStar : ℝ) / (k x).toReal : ℝ) : EReal) ≤ μ0 :=
          le_sSup hrmem
        by_cases hμ0_top : μ0 = ⊤
        · have hkx_pos : (0 : EReal) < k x := hk_pos x hx
          have htop : (⊤ : EReal) * k x = ⊤ := EReal.top_mul_of_pos hkx_pos
          simp [hμ0_top, htop]
        · have hμ0_ne_bot : μ0 ≠ ⊥ := by
            have hbot0 : (⊥ : EReal) < (0 : EReal) := by simp
            have hbotμ0 : (⊥ : EReal) < μ0 := lt_of_lt_of_le hbot0 hμ0_nonneg
            exact ne_of_gt hbotμ0
          exact
            polarGauge_mul_le_of_ratio_le (hk := hk) (hk_finite := hk_finite) (hk_pos := hk_pos)
              (xStar := xStar) (μ := μ0) hμ0_top hμ0_ne_bot hx hratio_le
    exact sInf_le hμ0_mem
  have hSup_le' : sSup R ≤ polarGauge k xStar := by
    simpa [polarGauge, M] using hSup_le
  have hInf_le' : polarGauge k xStar ≤ sSup R := by
    simpa [polarGauge, M] using hInf_le
  exact le_antisymm hInf_le' hSup_le'



end Section15
end Chap03
