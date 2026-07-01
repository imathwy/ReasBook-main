/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yijie Wang, Yunxi Duan, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part9

section Chap03
section Section15

open scoped BigOperators
open scoped Pointwise
open scoped Topology
open Filter

lemma bddAbove_sublevel_real_of_mono_convex_strict_nonneg {g : EReal → EReal}
    (hg_mono : Monotone g)
    (hg_conv : ConvexFunctionOn (S := {t : Fin 1 → ℝ | 0 ≤ t 0}) (fun t => g (t 0 : EReal)))
    (hstrict : ∃ s : ℝ, 0 < s ∧ g (0 : EReal) < g (s : EReal)) {αr : ℝ}
    (hα0 : g (0 : EReal) < (αr : EReal)) :
    BddAbove {s : ℝ | 0 ≤ s ∧ g (s : EReal) ≤ (αr : EReal)} := by
classical
rcases hstrict with ⟨s0, hs0pos, hs0lt⟩
let S : Set (Fin 1 → ℝ) := {t | 0 ≤ t 0}
have hconv :
    Convex ℝ (epigraph (S := S) (fun t => g (t 0 : EReal))) := by
  simpa [ConvexFunctionOn, S] using hg_conv
by_cases hs0top : g (s0 : EReal) = ⊤
·
  refine ⟨s0, ?_⟩
  intro s hs
  rcases hs with ⟨hs0, hsle⟩
  by_contra hgt
  have hle : (s0 : EReal) ≤ (s : EReal) := by
    exact_mod_cast (le_of_lt (lt_of_not_ge hgt))
  have hgs : g (s0 : EReal) ≤ g (s : EReal) := hg_mono hle
  have htop_le : (⊤ : EReal) ≤ (αr : EReal) := by
    calc
      (⊤ : EReal) ≤ g (s0 : EReal) := by
        simp [hs0top]
      _ ≤ (αr : EReal) := hgs.trans hsle
  exact (not_top_le_coe αr) htop_le
·
  have hs0ne_top : g (s0 : EReal) ≠ ⊤ := hs0top
  by_cases h0bot : g (0 : EReal) = ⊥
  ·
    have hs0ne_bot : g (s0 : EReal) ≠ ⊥ := by
      have : (⊥ : EReal) < g (s0 : EReal) := lt_of_le_of_lt bot_le hs0lt
      exact ne_of_gt this
    set r0 : ℝ := (g (s0 : EReal)).toReal
    have hr0 : g (s0 : EReal) = (r0 : EReal) := by
      simpa [r0] using
        (EReal.coe_toReal (x := g (s0 : EReal)) hs0ne_top hs0ne_bot).symm
    refine ⟨s0, ?_⟩
    intro s hs
    rcases hs with ⟨hs0, hsle⟩
    by_contra hgt
    have hspos : 0 < s := lt_trans hs0pos (lt_of_not_ge hgt)
    set t : ℝ := s0 / s
    have ht0 : 0 < t := by
      exact div_pos hs0pos hspos
    have ht1 : t < 1 := by
      have hlt : s0 < s := lt_of_not_ge hgt
      have hlt' : s0 / s < 1 := by
        exact (div_lt_one (by linarith [hspos])).2 hlt
      simpa [t] using hlt'
    have ht1ne : 1 - t ≠ 0 := by linarith
    set μ : ℝ := (r0 - 1 - t * αr) / (1 - t)
    have hμ : g (0 : EReal) ≤ (μ : EReal) := by
      simp [h0bot]
    let x : Fin 1 → ℝ := fun _ => 0
    let y : Fin 1 → ℝ := fun _ => s
    have hxS : x ∈ S := by simp [S, x]
    have hyS : y ∈ S := by
      simp [S, y, hs0]
    have hineq :=
      epigraph_combo_ineq_aux (S := S) (f := fun t => g (t 0 : EReal))
        (x := x) (y := y) (μ := μ) (v := αr) (t := t)
        hconv hxS hyS hμ hsle (le_of_lt ht0) (le_of_lt ht1)
    have hcomb : (1 - t) * μ + t * αr = r0 - 1 := by
      have hμ_def : (1 - t) * μ = r0 - 1 - t * αr := by
        dsimp [μ]
        field_simp [ht1ne]
      calc
        (1 - t) * μ + t * αr = (r0 - 1 - t * αr) + t * αr := by simp [hμ_def]
        _ = r0 - 1 := by ring
    have hts : t * s = s0 := by
      have hs_ne : s ≠ 0 := by linarith [hspos]
      calc
        t * s = (s0 / s) * s := by rfl
        _ = s0 := by field_simp [hs_ne]
    have hineq' :
        g (s0 : EReal) ≤ ((r0 - 1 : ℝ) : EReal) := by
      have hineq' :
          g (((1 - t) • x + t • y) 0 : EReal) ≤
            (((1 - t) * μ + t * αr : ℝ) : EReal) := by
        simpa using hineq
      have hineq'' :
          g (s0 : EReal) ≤ (((1 - t) * μ + t * αr : ℝ) : EReal) := by
        simpa [x, y, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hts] using hineq'
      simpa [hcomb] using hineq''
    have hcontr : (r0 : EReal) ≤ ((r0 - 1 : ℝ) : EReal) := by
      simpa [hr0] using hineq'
    have hcontr' : r0 ≤ r0 - 1 := (EReal.coe_le_coe_iff).1 hcontr
    linarith
  ·
    have h0top : g (0 : EReal) ≠ ⊤ := by
      exact ne_of_lt (lt_of_lt_of_le hα0 le_top)
    set r0 : ℝ := (g (0 : EReal)).toReal
    have hr0 : g (0 : EReal) = (r0 : EReal) := by
      simpa [r0] using
        (EReal.coe_toReal (x := g (0 : EReal)) h0top h0bot).symm
    have hs0ne_bot : g (s0 : EReal) ≠ ⊥ := by
      have : (⊥ : EReal) < g (s0 : EReal) := lt_of_le_of_lt bot_le hs0lt
      exact ne_of_gt this
    set r1 : ℝ := (g (s0 : EReal)).toReal
    have hr1 : g (s0 : EReal) = (r1 : EReal) := by
      simpa [r1] using
        (EReal.coe_toReal (x := g (s0 : EReal)) hs0ne_top hs0ne_bot).symm
    have hr0_lt : r0 < αr := by
      have : (r0 : EReal) < (αr : EReal) := by simpa [hr0] using hα0
      exact (EReal.coe_lt_coe_iff).1 this
    have hr1_gt : r0 < r1 := by
      have : (r0 : EReal) < (r1 : EReal) := by simpa [hr0, hr1] using hs0lt
      exact (EReal.coe_lt_coe_iff).1 this
    have hden_pos : 0 < r1 - r0 := by linarith [hr1_gt]
    by_cases hs0_le : g (s0 : EReal) ≤ (αr : EReal)
    ·
      set B : ℝ := s0 * (αr - r0) / (r1 - r0)
      have hnum_ge : r1 - r0 ≤ αr - r0 := by
        have : (r1 : EReal) ≤ (αr : EReal) := by simpa [hr1] using hs0_le
        have : r1 ≤ αr := (EReal.coe_le_coe_iff).1 this
        linarith
      have hratio_ge : 1 ≤ (αr - r0) / (r1 - r0) := by
        have hpos : 0 < r1 - r0 := hden_pos
        exact (one_le_div hpos).2 hnum_ge
      have hB_ge : s0 ≤ B := by
        have hs0pos' : 0 ≤ s0 := le_of_lt hs0pos
        have hmul := mul_le_mul_of_nonneg_left hratio_ge hs0pos'
        simpa [B, mul_div_assoc] using hmul
      refine ⟨B, ?_⟩
      intro s hs
      rcases hs with ⟨hs0, hsle⟩
      by_cases hle : s ≤ s0
      · exact hle.trans hB_ge
      ·
        have hspos : 0 < s := lt_trans hs0pos (lt_of_not_ge hle)
        set t : ℝ := s0 / s
        have ht0 : 0 < t := div_pos hs0pos hspos
        have ht1 : t < 1 := by
          have hlt : s0 < s := lt_of_not_ge hle
          have hlt' : s0 / s < 1 := by
            exact (div_lt_one (by linarith [hspos])).2 hlt
          simpa [t] using hlt'
        let x : Fin 1 → ℝ := fun _ => 0
        let y : Fin 1 → ℝ := fun _ => s
        have hxS : x ∈ S := by simp [S, x]
        have hyS : y ∈ S := by simp [S, y, hs0]
        have hineq :=
          epigraph_combo_ineq_aux (S := S) (f := fun t => g (t 0 : EReal))
            (x := x) (y := y) (μ := r0) (v := αr) (t := t)
          hconv hxS hyS (by simp [x, hr0]) hsle (le_of_lt ht0) (le_of_lt ht1)
        have hts : t * s = s0 := by
          have hs_ne : s ≠ 0 := by linarith [hspos]
          calc
            t * s = (s0 / s) * s := by rfl
            _ = s0 := by field_simp [hs_ne]
        have hineq' :
            g (s0 : EReal) ≤ (((1 - t) * r0 + t * αr : ℝ) : EReal) := by
          have hineq' :
              g (((1 - t) • x + t • y) 0 : EReal) ≤
                (((1 - t) * r0 + t * αr : ℝ) : EReal) := by
            simpa using hineq
          simpa [x, y, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hts] using hineq'
        have hineq_real : r1 ≤ (1 - t) * r0 + t * αr := by
          have : (r1 : EReal) ≤ ((1 - t) * r0 + t * αr : ℝ) := by
            simpa [hr1] using hineq'
          exact (EReal.coe_le_coe_iff).1 this
        have hineq_real' : r1 - r0 ≤ t * (αr - r0) := by
          nlinarith [hineq_real]
        have hineq_real'' :
            (r1 - r0) / (αr - r0) ≤ t := by
          have hpos : 0 < αr - r0 := by linarith [hr0_lt]
          exact (div_le_iff₀ hpos).2 hineq_real'
        have hs_le : s ≤ B := by
          have hs_pos : 0 < s := hspos
          have hs_pos' : 0 ≤ s := le_of_lt hs_pos
          have hpos : 0 < (r1 - r0) / (αr - r0) := by
            have hpos1 : 0 < r1 - r0 := hden_pos
            have hpos2 : 0 < αr - r0 := by linarith [hr0_lt]
            exact div_pos hpos1 hpos2
          have hs_le' : (r1 - r0) / (αr - r0) * s ≤ s0 := by
            have hmul := mul_le_mul_of_nonneg_right hineq_real'' hs_pos'
            have hs0' : (s0 / s) * s = s0 := by
              have hs_ne : s ≠ 0 := by linarith [hs_pos]
              field_simp [hs_ne]
            simpa [t, hs0'] using hmul
          have hs_le'' : s ≤ s0 / ((r1 - r0) / (αr - r0)) := by
            have hpos' : 0 < (r1 - r0) / (αr - r0) := hpos
            have : s * ((r1 - r0) / (αr - r0)) ≤ s0 := by
              simpa [mul_comm] using hs_le'
            exact (le_div_iff₀ hpos').2 this
          have hB : s0 / ((r1 - r0) / (αr - r0)) = B := by
            have hpos' : (r1 - r0) / (αr - r0) ≠ 0 := by
              exact ne_of_gt hpos
            simp [B]
            field_simp [hpos']
          simpa [hB] using hs_le''
        exact hs_le
    ·
      refine ⟨s0, ?_⟩
      intro s hs
      rcases hs with ⟨hs0, hsle⟩
      by_contra hgt
      have hle : (s0 : EReal) ≤ (s : EReal) := by
        exact_mod_cast (le_of_lt (lt_of_not_ge hgt))
      have hgs : g (s0 : EReal) ≤ g (s : EReal) := hg_mono hle
      have hbound : g (s0 : EReal) ≤ (αr : EReal) := hgs.trans hsle
      have hgtα : (αr : EReal) < g (s0 : EReal) := lt_of_not_ge hs0_le
      exact (not_le_of_gt hgtα) hbound

/-- There is a positive real in the cutoff sublevel once `g` is finite at some positive point. -/
lemma exists_pos_mem_sublevel_real_of_convex_finite_at_pos {g : EReal → EReal}
    (hg_conv : ConvexFunctionOn (S := {t : Fin 1 → ℝ | 0 ≤ t 0}) (fun t => g (t 0 : EReal)))
    (hζ : ∃ ζ : ℝ, 0 < ζ ∧ g (ζ : EReal) ≠ ⊤ ∧ g (ζ : EReal) ≠ ⊥) {αr : ℝ}
    (hα0 : g (0 : EReal) < (αr : EReal)) :
    ∃ s : ℝ, 0 < s ∧ g (s : EReal) ≤ (αr : EReal) := by
  classical
  rcases hζ with ⟨ζ, hζpos, hζtop, hζbot⟩
  let S : Set (Fin 1 → ℝ) := {t | 0 ≤ t 0}
  have hconv :
      Convex ℝ (epigraph (S := S) (fun t => g (t 0 : EReal))) := by
    simpa [ConvexFunctionOn, S] using hg_conv
  let x : Fin 1 → ℝ := fun _ => 0
  let y : Fin 1 → ℝ := fun _ => ζ
  have hxS : x ∈ S := by simp [S, x]
  have hyS : y ∈ S := by
    simp [S, y, hζpos.le]
  set r1 : ℝ := (g (ζ : EReal)).toReal
  have hr1 : g (ζ : EReal) = (r1 : EReal) := by
    simpa [r1] using (EReal.coe_toReal (x := g (ζ : EReal)) hζtop hζbot).symm
  by_cases h0bot : g (0 : EReal) = ⊥
  ·
    set μ : ℝ := 2 * αr - r1
    have hμ : g (0 : EReal) ≤ (μ : EReal) := by
      simp [h0bot]
    have hv : g (ζ : EReal) ≤ (r1 : EReal) := by
      simp [hr1]
    have hineq :=
      epigraph_combo_ineq_aux (S := S) (f := fun t => g (t 0 : EReal))
        (x := x) (y := y) (μ := μ) (v := r1) (t := (1 / 2 : ℝ))
        hconv hxS hyS hμ hv (by norm_num) (by norm_num)
    have hcomb : (1 - (1 / 2 : ℝ)) * μ + (1 / 2 : ℝ) * r1 = αr := by
      simp [μ]
      ring_nf
    have hcomb' :
        (((1 - (1 / 2 : ℝ)) * μ + (1 / 2 : ℝ) * r1 : ℝ) : EReal) = (αr : EReal) := by
      exact_mod_cast hcomb
    have hle :
        g (((1 / 2 : ℝ) * ζ : ℝ) : EReal) ≤ (αr : EReal) := by
      have hineq' :
          g (((1 - (1 / 2 : ℝ)) • x + (1 / 2 : ℝ) • y) 0 : EReal) ≤
            (((1 - (1 / 2 : ℝ)) * μ + (1 / 2 : ℝ) * r1 : ℝ) : EReal) := by
        simpa using hineq
      have hineq'' :
          g (((1 / 2 : ℝ) * ζ : ℝ) : EReal) ≤
            (((1 - (1 / 2 : ℝ)) * μ + (1 / 2 : ℝ) * r1 : ℝ) : EReal) := by
        simpa [x, y, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hineq'
      calc
        g (((1 / 2 : ℝ) * ζ : ℝ) : EReal) ≤
            (((1 - (1 / 2 : ℝ)) * μ + (1 / 2 : ℝ) * r1 : ℝ) : EReal) := hineq''
        _ = (αr : EReal) := hcomb'
    exact ⟨(1 / 2 : ℝ) * ζ, by nlinarith [hζpos], hle⟩
  ·
    have h0top : g (0 : EReal) ≠ ⊤ := by
      exact ne_of_lt (lt_of_lt_of_le hα0 le_top)
    set r0 : ℝ := (g (0 : EReal)).toReal
    have hr0 : g (0 : EReal) = (r0 : EReal) := by
      simpa [r0] using (EReal.coe_toReal (x := g (0 : EReal)) h0top h0bot).symm
    by_cases hle : g (ζ : EReal) ≤ (αr : EReal)
    · exact ⟨ζ, hζpos, hle⟩
    ·
      have hr0_lt : r0 < αr := by
        have : (r0 : EReal) < (αr : EReal) := by simpa [hr0] using hα0
        exact (EReal.coe_lt_coe_iff).1 this
      have hr1_gt : αr < r1 := by
        have : (αr : EReal) < (r1 : EReal) := by
          simpa [hr1] using (lt_of_not_ge hle)
        exact (EReal.coe_lt_coe_iff).1 this
      have hden_pos : 0 < r1 - r0 := by linarith [hr0_lt, hr1_gt]
      set t : ℝ := (αr - r0) / (r1 - r0)
      have ht0 : 0 < t := by
        exact div_pos (by linarith [hr0_lt]) hden_pos
      have ht1 : t < 1 := by
        have hnum_lt : αr - r0 < r1 - r0 := by linarith [hr1_gt]
        exact (div_lt_one hden_pos).2 hnum_lt
      have hμ : g (0 : EReal) ≤ (r0 : EReal) := by
        simp [hr0]
      have hv : g (ζ : EReal) ≤ (r1 : EReal) := by
        simp [hr1]
      have hineq :=
        epigraph_combo_ineq_aux (S := S) (f := fun t => g (t 0 : EReal))
          hconv hxS hyS hμ hv (le_of_lt ht0) (le_of_lt ht1)
      have hcomb : (1 - t) * r0 + t * r1 = αr := by
        have ht : t * (r1 - r0) = αr - r0 := by
          have hne : r1 - r0 ≠ 0 := by linarith [hden_pos]
          calc
            t * (r1 - r0) = ((αr - r0) / (r1 - r0)) * (r1 - r0) := by rfl
            _ = αr - r0 := by field_simp [hne]
        calc
          (1 - t) * r0 + t * r1 = r0 + t * (r1 - r0) := by ring
          _ = r0 + (αr - r0) := by simp [ht]
          _ = αr := by ring
      have hle :
          g ((t * ζ : ℝ) : EReal) ≤ (αr : EReal) := by
        have hineq' :
            g (((1 - t) • x + t • y) 0 : EReal) ≤
              (((1 - t) * r0 + t * r1 : ℝ) : EReal) := by
          simpa using hineq
        have hineq'' :
            g ((t * ζ : ℝ) : EReal) ≤
              (((1 - t) * r0 + t * r1 : ℝ) : EReal) := by
          simpa [x, y, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hineq'
        simpa [hcomb] using hineq''
      exact ⟨t * ζ, mul_pos ht0 hζpos, hle⟩

/-- A composition with a closed gauge is gauge-like closed proper convex under the hypotheses. -/
lemma comp_closedGauge_gives_gaugeLikeClosedProperConvex {n : ℕ} {k : (Fin n → ℝ) → EReal}
    {g : EReal → EReal} (hk : IsClosedGauge k) (hg_mono : Monotone g)
    (hg_conv : ConvexFunctionOn (S := {t : Fin 1 → ℝ | 0 ≤ t 0}) (fun t => g (t 0 : EReal)))
    (hg_closed :
      IsClosed
        (epigraph (S := {t : Fin 1 → ℝ | 0 ≤ t 0}) (fun t => g (t 0 : EReal))))
    (hg_top : g ⊤ = ⊤)
    (hζ : ∃ ζ : ℝ, 0 < ζ ∧ g (ζ : EReal) ≠ ⊤ ∧ g (ζ : EReal) ≠ ⊥)
    (hstrict : ∃ s : ℝ, 0 < s ∧ g (0 : EReal) < g (s : EReal)) :
    IsGaugeLikeClosedProperConvex (fun x : Fin n → ℝ => g (k x)) := by
  classical
  let f : (Fin n → ℝ) → EReal := fun x => g (k x)
  have hk_gauge : IsGauge k := hk.1
  have h0_ne_bot : g (0 : EReal) ≠ ⊥ :=
    g0_ne_bot_of_convex_closed_and_exists_finite_nonneg (g := g) hg_conv hg_closed hζ
  have h0_ne_top : g (0 : EReal) ≠ ⊤ := by
    rcases hζ with ⟨ζ, hζpos, hζtop, _⟩
    have hle : g (0 : EReal) ≤ g (ζ : EReal) := by
      have hz : (0 : EReal) ≤ (ζ : EReal) := by exact_mod_cast (le_of_lt hζpos)
      exact hg_mono hz
    intro h0top
    have : (⊤ : EReal) ≤ g (ζ : EReal) := by simpa [h0top] using hle
    exact hζtop (top_le_iff.mp this)
  have hnotbot_f :
      ∀ x ∈ (Set.univ : Set (Fin n → ℝ)), f x ≠ ⊥ := by
    intro x hx
    have hk_nonneg : (0 : EReal) ≤ k x := hk_gauge.2.1 x
    exact monotone_ne_bot_of_nonneg (g := g) hg_mono h0_ne_bot (k x) hk_nonneg
  have hnotbot_k :
      ∀ x ∈ (Set.univ : Set (Fin n → ℝ)), k x ≠ ⊥ := by
    intro x hx
    exact IsGauge.ne_bot hk_gauge x
  have hseg_k :
      ∀ x ∈ (Set.univ : Set (Fin n → ℝ)),
        ∀ y ∈ (Set.univ : Set (Fin n → ℝ)),
          ∀ t : ℝ, 0 < t → t < 1 →
            k ((1 - t) • x + t • y) ≤
              ((1 - t : ℝ) : EReal) * k x + ((t : ℝ) : EReal) * k y :=
    (convexFunctionOn_iff_segment_inequality (C := (Set.univ : Set (Fin n → ℝ))) (f := k)
        (hC := convex_univ) (hnotbot := hnotbot_k)).1 hk_gauge.1
  let S : Set (Fin 1 → ℝ) := {t : Fin 1 → ℝ | 0 ≤ t 0}
  have hSconv : Convex ℝ S := by
    intro x hx y hy a b ha hb hab
    have hx0 : 0 ≤ x 0 := hx
    have hy0 : 0 ≤ y 0 := hy
    have hcomb : 0 ≤ a * x 0 + b * y 0 := by nlinarith
    simpa [S, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hcomb
  have hnotbot_g : ∀ t ∈ S, g (t 0 : EReal) ≠ ⊥ := by
    intro t ht
    have ht0 : 0 ≤ t 0 := by simpa [S] using ht
    have hmono_ne_bot := monotone_ne_bot_of_nonneg (g := g) hg_mono h0_ne_bot
    exact hmono_ne_bot (t 0 : EReal) (by exact_mod_cast ht0)
  have hseg_g :
      ∀ x ∈ S, ∀ y ∈ S, ∀ t : ℝ, 0 < t → t < 1 →
        g (((1 - t) • x + t • y) 0 : EReal) ≤
          ((1 - t : ℝ) : EReal) * g (x 0 : EReal) + ((t : ℝ) : EReal) * g (y 0 : EReal) :=
    (convexFunctionOn_iff_segment_inequality (C := S)
        (f := fun t : Fin 1 → ℝ => g (t 0 : EReal)) (hC := hSconv) (hnotbot := hnotbot_g)).1
      hg_conv
  have hseg_f :
      ∀ x ∈ (Set.univ : Set (Fin n → ℝ)),
        ∀ y ∈ (Set.univ : Set (Fin n → ℝ)),
          ∀ t : ℝ, 0 < t → t < 1 →
            f ((1 - t) • x + t • y) ≤
              ((1 - t : ℝ) : EReal) * f x + ((t : ℝ) : EReal) * f y := by
    intro x hx y hy t ht0 ht1
    by_cases hkx_top : k x = ⊤
    · have hfx : f x = ⊤ := by simp [f, hkx_top, hg_top]
      have ht1E : (0 : EReal) < ((1 - t) : EReal) :=
        (EReal.coe_pos).2 (sub_pos.mpr ht1)
      have hmul :
          ((1 - t : ℝ) : EReal) * f x = ⊤ := by
        simpa [hfx] using (EReal.mul_top_of_pos ht1E)
      have hne_bot : ((t : ℝ) : EReal) * f y ≠ ⊥ := by
        by_cases hfy_top : f y = ⊤
        ·
          have ht0E : (0 : EReal) < ((t : ℝ) : EReal) := (EReal.coe_pos).2 ht0
          have htop : ((t : ℝ) : EReal) * f y = ⊤ := by
            simpa [hfy_top] using (EReal.mul_top_of_pos ht0E)
          simp [htop]
        · have hfy_bot : f y ≠ ⊥ := hnotbot_f y (by simp)
          have hfy :
              ((t : ℝ) : EReal) * f y = ((t * (f y).toReal : ℝ) : EReal) := by
            have hfy' : ((f y).toReal : EReal) = f y :=
              EReal.coe_toReal hfy_top hfy_bot
            calc
              ((t : ℝ) : EReal) * f y =
                  ((t : ℝ) : EReal) * ((f y).toReal : EReal) := by
                    simp [hfy']
              _ = ((t * (f y).toReal : ℝ) : EReal) := by
                    simp [EReal.coe_mul]
          simpa [hfy] using (EReal.coe_ne_bot (t * (f y).toReal))
      have htop :
          ((1 - t : ℝ) : EReal) * f x + ((t : ℝ) : EReal) * f y = ⊤ := by
        rw [hmul]
        exact EReal.top_add_of_ne_bot hne_bot
      calc
        f ((1 - t) • x + t • y) ≤ ⊤ := le_top
        _ = ((1 - t : ℝ) : EReal) * f x + ((t : ℝ) : EReal) * f y := by
              simpa using htop.symm
    · by_cases hky_top : k y = ⊤
      · have hfy : f y = ⊤ := by simp [f, hky_top, hg_top]
        have ht0E : (0 : EReal) < ((t : ℝ) : EReal) := (EReal.coe_pos).2 ht0
        have hmul :
            ((t : ℝ) : EReal) * f y = ⊤ := by
          simpa [hfy] using (EReal.mul_top_of_pos ht0E)
        have hne_bot : ((1 - t : ℝ) : EReal) * f x ≠ ⊥ := by
          by_cases hfx_top : f x = ⊤
          ·
            have ht1E : (0 : EReal) < ((1 - t) : EReal) :=
              (EReal.coe_pos).2 (sub_pos.mpr ht1)
            have htop : ((1 - t : ℝ) : EReal) * f x = ⊤ := by
              simpa [hfx_top] using (EReal.mul_top_of_pos ht1E)
            have htop' : (1 - (t : EReal)) * f x = ⊤ := by
              simpa using htop
            simp [htop']
          · have hfx_bot : f x ≠ ⊥ := hnotbot_f x (by simp)
            have hfx :
                ((1 - t : ℝ) : EReal) * f x =
                  (((1 - t) * (f x).toReal : ℝ) : EReal) := by
              have hfx' : ((f x).toReal : EReal) = f x :=
                EReal.coe_toReal hfx_top hfx_bot
              calc
                ((1 - t : ℝ) : EReal) * f x =
                    ((1 - t : ℝ) : EReal) * ((f x).toReal : EReal) := by
                      simp [hfx']
                _ = (((1 - t) * (f x).toReal : ℝ) : EReal) := by
                      simp [EReal.coe_mul]
            have hfx' :
                (1 - (t : EReal)) * f x =
                  (((1 - t) * (f x).toReal : ℝ) : EReal) := by
              simpa using hfx
            intro hbot
            have hbot' : ((1 - t) * (f x).toReal : ℝ) = (⊥ : EReal) := by
              simpa [hfx'] using hbot
            exact (EReal.coe_ne_bot ((1 - t) * (f x).toReal)) hbot'
        have htop :
            ((1 - t : ℝ) : EReal) * f x + ((t : ℝ) : EReal) * f y = ⊤ := by
          rw [hmul]
          simpa [add_comm] using (EReal.top_add_of_ne_bot hne_bot)
        calc
          f ((1 - t) • x + t • y) ≤ ⊤ := le_top
          _ = ((1 - t : ℝ) : EReal) * f x + ((t : ℝ) : EReal) * f y := by
                simpa using htop.symm
      ·
        have hk_ineq := hseg_k x (by simp) y (by simp) t ht0 ht1
        have hmono_ineq :
            g (k ((1 - t) • x + t • y)) ≤
              g (((1 - t : ℝ) : EReal) * k x + ((t : ℝ) : EReal) * k y) := hg_mono hk_ineq
        have hkx_bot : k x ≠ (⊥ : EReal) := IsGauge.ne_bot hk_gauge x
        have hky_bot : k y ≠ (⊥ : EReal) := IsGauge.ne_bot hk_gauge y
        set rx : ℝ := (k x).toReal
        set ry : ℝ := (k y).toReal
        have hkx : k x = (rx : EReal) := by
          simpa [rx] using (EReal.coe_toReal (x := k x) hkx_top hkx_bot).symm
        have hky : k y = (ry : EReal) := by
          simpa [ry] using (EReal.coe_toReal (x := k y) hky_top hky_bot).symm
        have hcomb :
            ((1 - t : ℝ) : EReal) * k x + ((t : ℝ) : EReal) * k y =
              (((1 - t) * rx + t * ry : ℝ) : EReal) := by
          simp [hkx, hky, EReal.coe_mul, EReal.coe_add]
        let tx : Fin 1 → ℝ := fun _ => rx
        let ty : Fin 1 → ℝ := fun _ => ry
        have htx : tx ∈ S := by
          have hkx_nonneg : (0 : EReal) ≤ k x := hk_gauge.2.1 x
          have hkx_nonneg' : (0 : EReal) ≤ (rx : EReal) := by
            simpa [hkx] using hkx_nonneg
          have : 0 ≤ rx := (EReal.coe_le_coe_iff).1 hkx_nonneg'
          simpa [S, tx] using this
        have hty : ty ∈ S := by
          have hky_nonneg : (0 : EReal) ≤ k y := hk_gauge.2.1 y
          have hky_nonneg' : (0 : EReal) ≤ (ry : EReal) := by
            simpa [hky] using hky_nonneg
          have : 0 ≤ ry := (EReal.coe_le_coe_iff).1 hky_nonneg'
          simpa [S, ty] using this
        have hseg_g' := hseg_g tx htx ty hty t ht0 ht1
        have hconv_g' :
            g (((1 - t) * rx + t * ry : ℝ) : EReal) ≤
              ((1 - t : ℝ) : EReal) * g (rx : EReal) + ((t : ℝ) : EReal) * g (ry : EReal) := by
          simpa [tx, ty, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hseg_g'
        have hmono_ineq' :
            f ((1 - t) • x + t • y) ≤ g (((1 - t) * rx + t * ry : ℝ) : EReal) := by
          simpa [f, hkx, hky, hcomb] using hmono_ineq
        have hconv_g'' :
            g (((1 - t) * rx + t * ry : ℝ) : EReal) ≤
              ((1 - t : ℝ) : EReal) * f x + ((t : ℝ) : EReal) * f y := by
          simpa [f, hkx, hky] using hconv_g'
        exact hmono_ineq'.trans hconv_g''
  have hconv_on :
      ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f := by
    refine (convexFunctionOn_iff_segment_inequality (C := (Set.univ : Set (Fin n → ℝ)))
        (f := f) (hC := convex_univ) (hnotbot := hnotbot_f)).2 ?_
    exact hseg_f
  have hconv : ConvexFunction f := by
    simpa [ConvexFunction] using hconv_on
  have hk0 : k 0 = 0 := hk_gauge.2.2.2
  have h0_le_fx : ∀ x : Fin n → ℝ, f 0 ≤ f x := by
    intro x
    have hk_nonneg : (0 : EReal) ≤ k x := hk_gauge.2.1 x
    have hmono0 : g (0 : EReal) ≤ g (k x) := hg_mono hk_nonneg
    simpa [f, hk0] using hmono0
  have hmin : f 0 = sInf (Set.range f) := by
    apply le_antisymm
    · refine le_sInf ?_
      intro y hy
      rcases hy with ⟨x, rfl⟩
      exact h0_le_fx x
    · exact sInf_le ⟨0, rfl⟩
  have hlsc :
      LowerSemicontinuousOn (fun t : Fin 1 → ℝ => g (t 0 : EReal)) S :=
    lscOn_g_nonneg_of_isClosed_epigraph (g := g) hg_closed
  have hsublevel_real :
      ∀ {α : ℝ}, g (0 : EReal) ≤ (α : EReal) →
        {x | f x ≤ (α : EReal)} =
          {x | k x ≤
            ((sSup {s : ℝ | 0 ≤ s ∧ g (s : EReal) ≤ (α : EReal)} : ℝ) : EReal)} := by
    intro α h0α
    let A : Set ℝ := {s : ℝ | 0 ≤ s ∧ g (s : EReal) ≤ (α : EReal)}
    have hA_bdd : BddAbove A := by
      by_cases hα0 : g (0 : EReal) < (α : EReal)
      ·
        exact
          bddAbove_sublevel_real_of_mono_convex_strict_nonneg (g := g)
            hg_mono hg_conv hstrict hα0
      ·
        have hα_eq : (α : EReal) = g (0 : EReal) :=
          le_antisymm (le_of_not_gt hα0) h0α
        rcases hstrict with ⟨s0, hs0pos, hs0lt⟩
        refine ⟨s0, ?_⟩
        intro s hs
        rcases hs with ⟨hs0, hgs⟩
        by_contra hgt
        have hs0' : (s0 : EReal) ≤ (s : EReal) := by
          exact_mod_cast (le_of_lt (lt_of_not_ge hgt))
        have hmono0 : g (s0 : EReal) ≤ g (s : EReal) := hg_mono hs0'
        have hle : g (s0 : EReal) ≤ (α : EReal) := hmono0.trans hgs
        have hle' : g (s0 : EReal) ≤ g (0 : EReal) := by simpa [hα_eq] using hle
        exact (not_lt_of_ge hle') hs0lt
    have hgr_le :
        g ((sSup A : ℝ) : EReal) ≤ (α : EReal) :=
      g_le_csSup_of_lscOn_nonneg (g := g) hlsc h0α hA_bdd
    ext x
    constructor
    · intro hx
      have hkx_top : k x ≠ (⊤ : EReal) := by
        intro hkx_top
        have : f x = ⊤ := by simp [f, hkx_top, hg_top]
        have htop_le : (⊤ : EReal) ≤ (α : EReal) := by
          have htop_le_fx : (⊤ : EReal) ≤ f x := by
            simp [this]
          exact htop_le_fx.trans hx
        exact (not_top_le_coe α) htop_le
      have hkx_bot : k x ≠ (⊥ : EReal) := IsGauge.ne_bot hk_gauge x
      set r : ℝ := (k x).toReal
      have hkx_coe : (r : EReal) = k x := by
        simpa [r] using (EReal.coe_toReal (x := k x) hkx_top hkx_bot)
      have hr_nonneg : 0 ≤ r := by
        have hk_nonneg : (0 : EReal) ≤ k x := hk_gauge.2.1 x
        have : (0 : EReal) ≤ (r : EReal) := by simpa [hkx_coe] using hk_nonneg
        exact (EReal.coe_le_coe_iff).1 this
      have hgr : g (r : EReal) ≤ (α : EReal) := by
        simpa [f, hkx_coe] using hx
      have hr_mem : r ∈ A := ⟨hr_nonneg, hgr⟩
      have hr_le : r ≤ sSup A := le_csSup hA_bdd hr_mem
      have hr_le' : (r : EReal) ≤ ((sSup A : ℝ) : EReal) := by
        exact_mod_cast hr_le
      simpa [hkx_coe] using hr_le'
    · intro hx
      have hmono1 : g (k x) ≤ g ((sSup A : ℝ) : EReal) := hg_mono hx
      exact hmono1.trans hgr_le
  have hgl : IsGaugeLike f := by
    refine ⟨hconv_on, hmin, ?_⟩
    intro α β hα0 hαtop hβ0 hβtop
    have hα_ne_top : α ≠ ⊤ := ne_of_lt hαtop
    have hβ_ne_top : β ≠ ⊤ := ne_of_lt hβtop
    have hα_ne_bot : α ≠ ⊥ := by
      intro hbot
      rw [hbot] at hα0
      exact (not_lt_bot hα0)
    have hβ_ne_bot : β ≠ ⊥ := by
      intro hbot
      rw [hbot] at hβ0
      exact (not_lt_bot hβ0)
    set αr : ℝ := α.toReal
    set βr : ℝ := β.toReal
    have hα_eq : (αr : EReal) = α := by
      simpa [αr] using (EReal.coe_toReal (x := α) hα_ne_top hα_ne_bot)
    have hβ_eq : (βr : EReal) = β := by
      simpa [βr] using (EReal.coe_toReal (x := β) hβ_ne_top hβ_ne_bot)
    have hα0' : g (0 : EReal) < (αr : EReal) := by
      simpa [f, hk0, hα_eq] using hα0
    have hβ0' : g (0 : EReal) < (βr : EReal) := by
      simpa [f, hk0, hβ_eq] using hβ0
    set Aα : Set ℝ := {s : ℝ | 0 ≤ s ∧ g (s : EReal) ≤ (αr : EReal)}
    set Aβ : Set ℝ := {s : ℝ | 0 ≤ s ∧ g (s : EReal) ≤ (βr : EReal)}
    have hAα_bdd : BddAbove Aα :=
      bddAbove_sublevel_real_of_mono_convex_strict_nonneg (g := g)
        hg_mono hg_conv hstrict hα0'
    have hAβ_bdd : BddAbove Aβ :=
      bddAbove_sublevel_real_of_mono_convex_strict_nonneg (g := g)
        hg_mono hg_conv hstrict hβ0'
    have hα_mem :
        ∃ s : ℝ, 0 < s ∧ g (s : EReal) ≤ (αr : EReal) :=
      exists_pos_mem_sublevel_real_of_convex_finite_at_pos (g := g) hg_conv hζ hα0'
    have hβ_mem :
        ∃ s : ℝ, 0 < s ∧ g (s : EReal) ≤ (βr : EReal) :=
      exists_pos_mem_sublevel_real_of_convex_finite_at_pos (g := g) hg_conv hζ hβ0'
    rcases hα_mem with ⟨sα, hsαpos, hsαle⟩
    rcases hβ_mem with ⟨sβ, hsβpos, hsβle⟩
    have hsα_mem : sα ∈ Aα := ⟨le_of_lt hsαpos, hsαle⟩
    have hsβ_mem : sβ ∈ Aβ := ⟨le_of_lt hsβpos, hsβle⟩
    set rα : ℝ := sSup Aα
    set rβ : ℝ := sSup Aβ
    have hrα_pos : 0 < rα := by
      have hsα_le : sα ≤ rα := le_csSup hAα_bdd hsα_mem
      exact lt_of_lt_of_le hsαpos hsα_le
    have hrβ_pos : 0 < rβ := by
      have hsβ_le : sβ ≤ rβ := le_csSup hAβ_bdd hsβ_mem
      exact lt_of_lt_of_le hsβpos hsβ_le
    have hsubα :
        {x | f x ≤ α} = {x | k x ≤ (rα : EReal)} := by
      have hEq :=
        hsublevel_real (α := αr) (le_of_lt hα0')
      simpa [hα_eq, rα, Aα] using hEq
    have hsubβ :
        {x | f x ≤ β} = {x | k x ≤ (rβ : EReal)} := by
      have hEq :=
        hsublevel_real (α := βr) (le_of_lt hβ0')
      simpa [hβ_eq, rβ, Aβ] using hEq
    refine ⟨rα / rβ, div_pos hrα_pos hrβ_pos, ?_⟩
    have hsubα1 :
        {x | k x ≤ (rα : EReal)} = rα • {x | k x ≤ (1 : EReal)} :=
      sublevel_eq_smul_sublevel_one_of_isGauge (hk := hk_gauge) hrα_pos
    have hsubβ1 :
        {x | k x ≤ (rβ : EReal)} = rβ • {x | k x ≤ (1 : EReal)} :=
      sublevel_eq_smul_sublevel_one_of_isGauge (hk := hk_gauge) hrβ_pos
    have hsubβ1' :
        rβ • {x | k x ≤ (1 : EReal)} = {x | k x ≤ (rβ : EReal)} := by
      simpa using hsubβ1.symm
    have hrβ_ne : rβ ≠ 0 := ne_of_gt hrβ_pos
    calc
      {x | f x ≤ α} = {x | k x ≤ (rα : EReal)} := hsubα
      _ = rα • {x | k x ≤ (1 : EReal)} := hsubα1
      _ = (rα / rβ) • (rβ • {x | k x ≤ (1 : EReal)}) := by
        have hmul : (rα / rβ) * rβ = rα := by field_simp [hrβ_ne]
        simp [smul_smul, hmul]
      _ = (rα / rβ) • {x | k x ≤ (rβ : EReal)} := by
        simp [hsubβ1']
      _ = (rα / rβ) • {x | f x ≤ β} := by
        simp [hsubβ]
  have hk_sub :
      ∀ α : ℝ, IsClosed {x | k x ≤ (α : EReal)} :=
    (lowerSemicontinuous_iff_closed_sublevel_iff_closed_epigraph (f := k)).2.mpr hk.2
  have hsub_f : ∀ α : ℝ, IsClosed {x | f x ≤ (α : EReal)} := by
    intro α
    by_cases hα : (α : EReal) < g (0 : EReal)
    ·
      have hset : {x | f x ≤ (α : EReal)} = (∅ : Set (Fin n → ℝ)) := by
        ext x
        constructor
        · intro hx
          have h0le : g (0 : EReal) ≤ f x := by
            have h0le' : f 0 ≤ f x := h0_le_fx x
            simp [f, hk0] at h0le'
            exact h0le'
          have : g (0 : EReal) ≤ (α : EReal) := h0le.trans hx
          exact (not_lt_of_ge this) hα
        · intro hx
          exact hx.elim
      simp [hset]
    ·
      have h0α : g (0 : EReal) ≤ (α : EReal) := le_of_not_gt hα
      have hEq := hsublevel_real (α := α) h0α
      have hclosed :
          IsClosed {x | k x ≤
            ((sSup {s : ℝ | 0 ≤ s ∧ g (s : EReal) ≤ (α : EReal)} : ℝ) : EReal)} :=
        hk_sub (sSup {s : ℝ | 0 ≤ s ∧ g (s : EReal) ≤ (α : EReal)})
      simpa [hEq] using hclosed
  have hls : LowerSemicontinuous f :=
    (lowerSemicontinuous_iff_closed_sublevel (f := f)).2 hsub_f
  have hclosed : ClosedConvexFunction f := ⟨hconv, hls⟩
  have hne_epi : Set.Nonempty (epigraph (S := (Set.univ : Set (Fin n → ℝ))) f) := by
    refine ⟨(0, (g (0 : EReal)).toReal), ?_⟩
    have hco : ((g (0 : EReal)).toReal : EReal) = g (0 : EReal) := by
      simpa using (EReal.coe_toReal (x := g (0 : EReal)) h0_ne_top h0_ne_bot)
    have h0 : f 0 ≤ ((g (0 : EReal)).toReal : EReal) := by
      have : f 0 = g (0 : EReal) := by simp [f, hk0]
      simp [this, hco]
    have h0mem : (0 : Fin n → ℝ) ∈ (Set.univ : Set (Fin n → ℝ)) := by simp
    exact ⟨h0mem, h0⟩
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f :=
    ⟨hconv_on, hne_epi, hnotbot_f⟩
  exact ⟨hgl, hclosed, hproper⟩

/-- Theorem 15.3: A function `f` is a gauge-like closed proper convex function if and only if it
can be expressed as `f(x) = g (k x)`, where `k` is a closed gauge and
`g : [0, +∞] → (-∞, +∞]` is a non-decreasing, lower semicontinuous convex function which
strictly increases at some positive point and satisfies `g(ζ)` finite for some `ζ > 0`
(with the convention `g(+∞) = +∞`). -/
theorem gaugeLikeClosedProperConvex_iff_exists_closedGauge_comp {n : ℕ}
    (f : (Fin n → ℝ) → EReal) :
    IsGaugeLikeClosedProperConvex f ↔
      ∃ (k : (Fin n → ℝ) → EReal) (g : EReal → EReal),
        IsClosedGauge k ∧
          (∃ ζ : ℝ, 0 < ζ ∧ g (ζ : EReal) ≠ ⊤ ∧ g (ζ : EReal) ≠ ⊥) ∧
            (∃ s : ℝ, 0 < s ∧ g (0 : EReal) < g (s : EReal)) ∧
              Monotone g ∧
                ConvexFunctionOn (S := {t : Fin 1 → ℝ | 0 ≤ t 0}) (fun t => g (t 0 : EReal)) ∧
                  IsClosed
                    (epigraph (S := {t : Fin 1 → ℝ | 0 ≤ t 0}) (fun t => g (t 0 : EReal))) ∧
                    g ⊤ = ⊤ ∧
                      f = fun x => g (k x) := by
  classical
  constructor
  · intro hf
    rcases exists_closedGauge_unitSublevel_eq_baseSublevel (f := f) hf with
      ⟨β, hβ0, hβtop, k, hk, hsub⟩
    -- TODO: define the profile `g` from the scaled sublevels and show `f = g ∘ k`.
    -- TODO: establish the required properties of `g`.
    let g : EReal → EReal := fun z => if z = ⊤ then ⊤ else sInf (profileSet f k z)
    have hg_mono : Monotone g := by
      simpa [g] using (profileFun_with_top_mono (f := f) (k := k))
    have hg_top : g ⊤ = ⊤ := by
      simp [g]
    have h1top : (1 : EReal) ≠ ⊤ := by
      exact ne_of_lt (EReal.coe_lt_top (1 : ℝ))
    have hβ_mem : (β : EReal) ∈ profileSet f k (1 : EReal) := by
      refine ⟨hβ0, hβtop, ?_⟩
      intro x hx
      have hx' : x ∈ {x | k x ≤ (1 : EReal)} := hx
      have hx'' : x ∈ {x | f x ≤ (β : EReal)} := by simpa [hsub] using hx'
      exact hx''
    have hg1_le : g (1 : EReal) ≤ (β : EReal) := by
      have hle : sInf (profileSet f k (1 : EReal)) ≤ (β : EReal) := sInf_le hβ_mem
      simpa [g, h1top] using hle
    have h0_ne_bot : f 0 ≠ ⊥ := by
      rcases hf with ⟨_hgl, _hclosed, hproper⟩
      rcases hproper with ⟨_hconv', _hne_epi, hne_bot⟩
      exact hne_bot 0 (by simp)
    have h0_le_g1 : f 0 ≤ g (1 : EReal) := by
      have hle : f 0 ≤ sInf (profileSet f k (1 : EReal)) := by
        refine le_sInf ?_
        intro α hα
        exact le_of_lt hα.1
      simpa [g, h1top] using hle
    have hg1_ne_top : g (1 : EReal) ≠ ⊤ := by
      intro htop
      have hg1_le' := hg1_le
      rw [htop] at hg1_le'
      exact (not_top_le_coe β) hg1_le'
    have hg1_ne_bot : g (1 : EReal) ≠ ⊥ := by
      intro hbot
      have : f 0 ≤ (⊥ : EReal) := by simpa [hbot] using h0_le_g1
      have h0_bot : f 0 = ⊥ := (le_bot_iff.mp this)
      exact h0_ne_bot h0_bot
    have hmin : f 0 = sInf (Set.range f) := (hf.1).2.1
    have h0_le_fx : ∀ x : Fin n → ℝ, f 0 ≤ f x := by
      intro x
      have hx : f x ∈ Set.range f := ⟨x, rfl⟩
      have hle : sInf (Set.range f) ≤ f x := sInf_le hx
      simpa [hmin] using hle
    have hsublevel :
        ∀ {α : EReal}, f 0 < α → α < ⊤ →
          ∃ t : ℝ, 0 < t ∧ {x | f x ≤ α} = {x | k x ≤ (t : EReal)} := by
      intro α hα0 hαtop
      rcases
          sublevel_sets_homothetic_of_IsGaugeLike (f := f) (hf := hf.1) hα0 hαtop hβ0 hβtop with
        ⟨t, ht, hα⟩
      have hsub' : {x | f x ≤ (β : EReal)} = {x | k x ≤ (1 : EReal)} := hsub.symm
      refine ⟨t, ht, ?_⟩
      calc
        {x | f x ≤ α} = t • {x | f x ≤ (β : EReal)} := hα
        _ = t • {x | k x ≤ (1 : EReal)} := by simp [hsub']
        _ = {x | k x ≤ (t : EReal)} := (sublevel_eq_smul_sublevel_one_of_isGauge hk.1 ht).symm
    have hfg : f = fun x => g (k x) := by
      ext x
      by_cases hkx_top : k x = ⊤
      ·
        have hfx_top : f x = ⊤ := by
          by_contra hfx_ne_top
          have hfx_lt_top : f x < ⊤ := lt_of_le_of_ne le_top hfx_ne_top
          rcases exists_between hfx_lt_top with ⟨α, hfx_lt, hα_top⟩
          have h0_lt_α : f 0 < α := lt_of_le_of_lt (h0_le_fx x) hfx_lt
          rcases hsublevel h0_lt_α hα_top with ⟨t, ht, hsubα⟩
          have hxmem : x ∈ {x | f x ≤ α} := by
            have : f x ≤ α := le_of_lt hfx_lt
            simpa using this
          have hxmemk : x ∈ {x | k x ≤ (t : EReal)} := by
            simpa [hsubα] using hxmem
          have hkx_le : k x ≤ (t : EReal) := by simpa using hxmemk
          have hkx_ne : k x ≠ (⊤ : EReal) := by
            intro hkx_top'
            have hkx_le' := hkx_le
            rw [hkx_top'] at hkx_le'
            exact (not_top_le_coe t) hkx_le'
          exact hkx_ne hkx_top
        simp [g, hkx_top, hfx_top]
      ·
        by_cases hfx_top : f x = ⊤
        ·
          have hprofile_empty : profileSet f k (k x) = ∅ := by
            apply Set.eq_empty_iff_forall_notMem.mpr
            intro α hα
            have hxmem : x ∈ {x | k x ≤ k x} := by simp
            have hxmem' : x ∈ {x | f x ≤ α} := hα.2.2 hxmem
            have htop_le : (⊤ : EReal) ≤ α := by simpa [hfx_top] using hxmem'
            have htop_eq : α = ⊤ := top_le_iff.mp htop_le
            have : (⊤ : EReal) < ⊤ := by simpa [htop_eq] using hα.2
            exact (lt_irrefl _ this)
          have hgx_top : g (k x) = ⊤ := by simp [g, hkx_top, hprofile_empty]
          simp [hfx_top, hgx_top]
        ·
          apply le_antisymm
          ·
            have hle : f x ≤ sInf (profileSet f k (k x)) := by
              refine le_sInf ?_
              intro α hα
              have hxmem : x ∈ {x | k x ≤ k x} := by simp
              have hxmem' : x ∈ {x | f x ≤ α} := hα.2.2 hxmem
              exact (show f x ≤ α from hxmem')
            simpa [g, hkx_top] using hle
          ·
            by_contra hgt
            have hlt : f x < g (k x) := lt_of_not_ge hgt
            rcases exists_between hlt with ⟨α, hfx_lt, hα_lt⟩
            have hα_top : α < ⊤ := lt_of_lt_of_le hα_lt le_top
            have h0_lt_α : f 0 < α := lt_of_le_of_lt (h0_le_fx x) hfx_lt
            rcases hsublevel h0_lt_α hα_top with ⟨t, ht, hsubα⟩
            have hxmem : x ∈ {x | f x ≤ α} := by
              have : f x ≤ α := le_of_lt hfx_lt
              simpa using this
            have hxmemk : x ∈ {x | k x ≤ (t : EReal)} := by
              simpa [hsubα] using hxmem
            have hkx_le : k x ≤ (t : EReal) := by simpa using hxmemk
            have hsubset : {y | k y ≤ k x} ⊆ {y | f y ≤ α} := by
              intro y hy
              have hy' : k y ≤ (t : EReal) := le_trans hy hkx_le
              have hy'' : y ∈ {x | k x ≤ (t : EReal)} := by simpa using hy'
              have hy''' : y ∈ {x | f x ≤ α} := by simpa [hsubα] using hy''
              exact hy'''
            have hα_mem : α ∈ profileSet f k (k x) := ⟨h0_lt_α, hα_top, hsubset⟩
            have hle : g (k x) ≤ α := by
              have : sInf (profileSet f k (k x)) ≤ α := sInf_le hα_mem
              simpa [g, hkx_top] using this
            exact (not_lt_of_ge hle) hα_lt
    by_cases hpos : ∃ y : Fin n → ℝ, (0 : EReal) < k y ∧ k y < ⊤
    ·
      have hstrict : ∃ s : ℝ, 0 < s ∧ g (0 : EReal) < g (s : EReal) := by
        rcases exists_unit_level_of_pos_finite (k := k) hk.1 hpos with ⟨y1, hky1⟩
        have hk0 : k 0 = 0 := (hk.1).2.2.2
        have hk2 : k (2 • y1) = (2 : EReal) := by
          have hhom := hk.1.2.2.1 y1 2 (by norm_num)
          simpa [hky1] using hhom
        have hnot_mem : ¬ f (2 • y1) ≤ (β : EReal) := by
          have hk_not : ¬ k (2 • y1) ≤ (1 : EReal) := by
            have hlt : (1 : EReal) < k (2 • y1) := by
              rw [hk2]
              exact (EReal.coe_lt_coe_iff).2 (by norm_num)
            exact not_le_of_gt hlt
          have hk_not' : ¬ (2 • y1) ∈ {x | k x ≤ (1 : EReal)} := by
            simpa [Set.mem_setOf_eq] using hk_not
          have hk_not'' : ¬ (2 • y1) ∈ {x | f x ≤ (β : EReal)} := by
            simpa [hsub] using hk_not'
          simpa [Set.mem_setOf_eq] using hk_not''
        have hfx_gt : (β : EReal) < f (2 • y1) := lt_of_not_ge hnot_mem
        have hfg0 : g (0 : EReal) = f 0 := by
          simp [hfg, hk0]
        have hfg2 : g (2 : EReal) = f (2 • y1) := by
          calc
            g (2 : EReal) = g (k (2 • y1)) := by rw [hk2]
            _ = f (2 • y1) := by simp [hfg]
        have hlt : g (0 : EReal) < g (2 : EReal) := by
          have h0lt : f 0 < f (2 • y1) := lt_trans hβ0 hfx_gt
          simpa [hfg0, hfg2] using h0lt
        exact ⟨2, by norm_num, hlt⟩
      refine ⟨k, g, hk, ?_, hstrict, hg_mono, ?_, ?_, hg_top, ?_⟩
      · refine ⟨1, by norm_num, ?_, ?_⟩
        · exact hg1_ne_top
        · exact hg1_ne_bot
      ·
        classical
        -- Convexity of the epigraph on the nonnegative ray.
        by_cases hpos : ∃ y : Fin n → ℝ, (0 : EReal) < k y ∧ k y < ⊤
        · rcases exists_unit_level_of_pos_finite (k := k) hk.1 hpos with ⟨y1, hky1⟩
          have hgy1 : ∀ s : ℝ, 0 ≤ s → g (s : EReal) = f (s • y1) := by
            intro s hs
            have hks : k (s • y1) = (s : EReal) := by
              have hhom := hk.1.2.2.1 y1 s hs
              simpa [hky1] using hhom
            simp [hfg, hks]
          let S : Set (Fin 1 → ℝ) := {t | 0 ≤ t 0}
          have hconvf :
              Convex ℝ (epigraph (S := (Set.univ : Set (Fin n → ℝ))) f) := by
            simpa [ConvexFunctionOn] using (hf.1).1
          have hconv_epi :
              Convex ℝ (epigraph (S := S) (fun t => g (t 0 : EReal))) := by
            intro p hp q hq a b ha hb hab
            have hp' : p.1 ∈ S ∧ g (p.1 0 : EReal) ≤ (p.2 : EReal) := by
              simpa [epigraph] using hp
            have hq' : q.1 ∈ S ∧ g (q.1 0 : EReal) ≤ (q.2 : EReal) := by
              simpa [epigraph] using hq
            have hp0 : 0 ≤ p.1 0 := by simpa [S] using hp'.1
            have hq0 : 0 ≤ q.1 0 := by simpa [S] using hq'.1
            have hp_f : f (p.1 0 • y1) ≤ (p.2 : EReal) := by
              have hgy : g (p.1 0 : EReal) = f (p.1 0 • y1) := hgy1 (p.1 0) hp0
              simpa [hgy] using hp'.2
            have hq_f : f (q.1 0 • y1) ≤ (q.2 : EReal) := by
              have hgy : g (q.1 0 : EReal) = f (q.1 0 • y1) := hgy1 (q.1 0) hq0
              simpa [hgy] using hq'.2
            have hp_epi :
                (p.1 0 • y1, p.2) ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) f := by
              exact ⟨by exact Set.mem_univ (α := Fin n → ℝ) (p.1 0 • y1), hp_f⟩
            have hq_epi :
                (q.1 0 • y1, q.2) ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) f := by
              exact ⟨by exact Set.mem_univ (α := Fin n → ℝ) (q.1 0 • y1), hq_f⟩
            have hcomb :
                (a • (p.1 0 • y1, p.2) + b • (q.1 0 • y1, q.2)) ∈
                  epigraph (S := (Set.univ : Set (Fin n → ℝ))) f :=
              hconvf hp_epi hq_epi ha hb hab
            have hcomb' :
                f (a • (p.1 0 • y1) + b • (q.1 0 • y1)) ≤
                  ((a * p.2 + b * q.2) : EReal) := by
              simpa [smul_add, smul_smul, Prod.smul_mk, smul_eq_mul] using hcomb.2
            have hlin :
                a • (p.1 0 • y1) + b • (q.1 0 • y1) =
                  (a * p.1 0 + b * q.1 0) • y1 := by
              simp [smul_smul, add_smul]
            have hnonneg :
                0 ≤ a * p.1 0 + b * q.1 0 := by
              nlinarith [ha, hb, hp0, hq0]
            have hgy :
                g ((a * p.1 0 + b * q.1 0 : ℝ) : EReal) =
                  f ((a * p.1 0 + b * q.1 0) • y1) := hgy1 _ hnonneg
            have hcomb'' :
                g ((a * p.1 0 + b * q.1 0 : ℝ) : EReal) ≤
                  ((a * p.2 + b * q.2) : EReal) := by
              have hcomb'' :
                  f ((a * p.1 0 + b * q.1 0) • y1) ≤ ((a * p.2 + b * q.2) : EReal) := by
                simpa [hlin] using hcomb'
              simpa using (hgy.symm ▸ hcomb'')
            have hScomb : (a • p + b • q).1 ∈ S := by
              have hnonneg' : 0 ≤ a * p.1 0 + b * q.1 0 := by
                nlinarith [ha, hb, hp0, hq0]
              simpa [S, Prod.smul_mk, smul_eq_mul, Pi.add_apply] using hnonneg'
            have hcomb''' :
                g ((a • p + b • q).1 0 : EReal) ≤ ((a • p + b • q).2 : EReal) := by
              simpa [Prod.smul_mk, smul_eq_mul, Pi.add_apply] using hcomb''
            exact ⟨hScomb, hcomb'''⟩
          simpa [ConvexFunctionOn] using hconv_epi
        ·
          have hdeg : ∀ y : Fin n → ℝ, k y = 0 ∨ k y = ⊤ := by
            intro y
            by_contra h
            have hy0 : (0 : EReal) < k y := by
              have hnonneg : 0 ≤ k y := hk.1.2.1 y
              have hne0 : k y ≠ 0 := by
                intro h0
                exact h (Or.inl h0)
              exact lt_of_le_of_ne hnonneg (Ne.symm hne0)
            have hytop : k y < ⊤ := by
              have hne_top : k y ≠ ⊤ := by
                intro htop
                exact h (Or.inr htop)
              exact lt_of_le_of_ne le_top hne_top
            exact hpos ⟨y, hy0, hytop⟩
          let S : Set (Fin 1 → ℝ) := {t | 0 ≤ t 0}
          have hconst :
              ∀ s : ℝ, 0 ≤ s → g (s : EReal) = g (1 : EReal) := by
            intro s hs
            have hsub :
                {x | k x ≤ (s : EReal)} = {x | k x ≤ (1 : EReal)} := by
              ext x
              rcases hdeg x with hx | hx
              · have hs' : (0 : EReal) ≤ (s : EReal) := by
                  exact_mod_cast hs
                have h1' : (0 : EReal) ≤ (1 : EReal) := by simp
                simp [hx, hs', h1']
              · have hs' : ¬ (⊤ : EReal) ≤ (s : EReal) := not_top_le_coe s
                have h1' : ¬ (⊤ : EReal) ≤ (1 : EReal) := not_top_le_coe 1
                simp [hx, hs', h1']
            have hprof :
                profileSet f k (s : EReal) = profileSet f k (1 : EReal) := by
              ext α
              constructor
              · intro hα
                rcases hα with ⟨h0, htop, hsub'⟩
                refine ⟨h0, htop, ?_⟩
                simpa [hsub] using hsub'
              · intro hα
                rcases hα with ⟨h0, htop, hsub'⟩
                refine ⟨h0, htop, ?_⟩
                simpa [hsub] using hsub'
            have hsne : (s : EReal) ≠ ⊤ := by
              exact ne_of_lt (EReal.coe_lt_top s)
            have h1ne : (1 : EReal) ≠ ⊤ := by
              exact ne_of_lt (EReal.coe_lt_top (1 : ℝ))
            simp [g, hsne, h1ne, hprof]
          let c : EReal := g (1 : EReal)
          have hSconv : Convex ℝ {p : (Fin 1 → ℝ) × ℝ | 0 ≤ p.1 0} := by
            intro p hp q hq a b ha hb hab
            have hp0 : 0 ≤ p.1 0 := by simpa using hp
            have hq0 : 0 ≤ q.1 0 := by simpa using hq
            have hnonneg : 0 ≤ a * p.1 0 + b * q.1 0 := by
              nlinarith [ha, hb, hp0, hq0]
            simpa [Prod.smul_mk, smul_eq_mul, Pi.add_apply] using hnonneg
          have hHconv : Convex ℝ {p : (Fin 1 → ℝ) × ℝ | c ≤ (p.2 : EReal)} := by
            by_cases htop : c = ⊤
            · have hset : {p : (Fin 1 → ℝ) × ℝ | c ≤ (p.2 : EReal)} = ∅ := by
                ext p
                simp [htop]
              simpa [hset] using (convex_empty : Convex ℝ (∅ : Set ((Fin 1 → ℝ) × ℝ)))
            · by_cases hbot : c = ⊥
              · have hset : {p : (Fin 1 → ℝ) × ℝ | c ≤ (p.2 : EReal)} = Set.univ := by
                  ext p
                  simp [hbot]
                simpa [hset] using (convex_univ : Convex ℝ (Set.univ : Set ((Fin 1 → ℝ) × ℝ)))
              · set r : ℝ := c.toReal
                have hco : c = (r : EReal) := by
                  simpa [r] using (EReal.coe_toReal (x := c) htop hbot).symm
                have hset :
                    {p : (Fin 1 → ℝ) × ℝ | c ≤ (p.2 : EReal)} =
                      {p : (Fin 1 → ℝ) × ℝ | r ≤ p.2} := by
                  ext p
                  simp [hco]
                have hconv : Convex ℝ {p : (Fin 1 → ℝ) × ℝ | r ≤ p.2} := by
                  intro p hp q hq a b ha hb hab
                  have hp2 : r ≤ p.2 := by simpa using hp
                  have hq2 : r ≤ q.2 := by simpa using hq
                  have hle : r ≤ a * p.2 + b * q.2 := by
                    have hr : a * r + b * r = r := by
                      calc
                        a * r + b * r = (a + b) * r := by ring
                        _ = r := by simp [hab]
                    have hle0 : r ≤ a * r + b * r := by
                      simp [hr]
                    have hle1 : a * r ≤ a * p.2 := by nlinarith [hp2, ha]
                    have hle2 : b * r ≤ b * q.2 := by nlinarith [hq2, hb]
                    have hle' : a * r + b * r ≤ a * p.2 + b * q.2 := by nlinarith [hle1, hle2]
                    exact hle0.trans hle'
                  simpa [Prod.smul_mk, smul_eq_mul, Pi.add_apply] using hle
                simpa [hset] using hconv
          have hset :
              epigraph (S := S) (fun t => g (t 0 : EReal)) =
                {p : (Fin 1 → ℝ) × ℝ | 0 ≤ p.1 0} ∩
                  {p : (Fin 1 → ℝ) × ℝ | c ≤ (p.2 : EReal)} := by
            ext p
            constructor
            · intro hp
              have hp' : p.1 ∈ S ∧ g (p.1 0 : EReal) ≤ (p.2 : EReal) := by
                simpa [epigraph] using hp
              have hp0 : 0 ≤ p.1 0 := by simpa [S] using hp'.1
              have hgy : g (p.1 0 : EReal) = c := by simpa [c] using hconst _ hp0
              exact ⟨by simpa using hp0, by simpa [hgy] using hp'.2⟩
            · rintro ⟨hp0, hpμ⟩
              have hp0' : p.1 ∈ S := by simpa [S] using hp0
              have hgy : g (p.1 0 : EReal) = c := by simpa [c] using hconst _ hp0
              exact ⟨hp0', by simpa [hgy] using hpμ⟩
          have hconv_epi :
              Convex ℝ (epigraph (S := S) (fun t => g (t 0 : EReal))) := by
            simpa [hset] using hSconv.inter hHconv
          simpa [ConvexFunctionOn] using hconv_epi
      ·
        classical
        -- Closedness of the epigraph on the nonnegative ray.
        by_cases hpos : ∃ y : Fin n → ℝ, (0 : EReal) < k y ∧ k y < ⊤
        · rcases exists_unit_level_of_pos_finite (k := k) hk.1 hpos with ⟨y1, hky1⟩
          have hgy1 : ∀ s : ℝ, 0 ≤ s → g (s : EReal) = f (s • y1) := by
            intro s hs
            have hks : k (s • y1) = (s : EReal) := by
              have hhom := hk.1.2.2.1 y1 s hs
              simpa [hky1] using hhom
            simp [hfg, hks]
          let S : Set (Fin 1 → ℝ) := {t | 0 ≤ t 0}
          have hsub : ∀ α : ℝ, IsClosed {x | f x ≤ (α : EReal)} :=
            (lowerSemicontinuous_iff_closed_sublevel (f := f)).1 hf.2.1.2
          have hclosed_epi_f :
              IsClosed (epigraph (S := (Set.univ : Set (Fin n → ℝ))) f) :=
            closed_epigraph_of_closed_sublevel (f := f) hsub
          -- Define the ray map.
          let rayMap : (Fin 1 → ℝ) × ℝ →ₗ[ℝ] (Fin n → ℝ) × ℝ :=
            { toFun := fun p => ((p.1 0) • y1, p.2)
              map_add' := by
                intro p q
                ext i <;> simp [Pi.add_apply, smul_eq_mul, add_mul]
              map_smul' := by
                intro c p
                ext i <;> simp [smul_smul, mul_comm, mul_left_comm] }
          have hcont : Continuous rayMap :=
            LinearMap.continuous_of_finiteDimensional (f := rayMap)
          have hpre :
              rayMap ⁻¹' (epigraph (S := (Set.univ : Set (Fin n → ℝ))) f) =
                {p : (Fin 1 → ℝ) × ℝ | f ((p.1 0) • y1) ≤ (p.2 : EReal)} := by
            ext p
            constructor
            · intro hp
              exact hp.2
            · intro hp
              have hp0 : (rayMap p).1 ∈ (Set.univ : Set (Fin n → ℝ)) := by
                simp
              exact ⟨hp0, hp⟩
          have hclosed_pre :
              IsClosed {p : (Fin 1 → ℝ) × ℝ | f ((p.1 0) • y1) ≤ (p.2 : EReal)} := by
            have hpre' :
                {p : (Fin 1 → ℝ) × ℝ | f ((p.1 0) • y1) ≤ (p.2 : EReal)} =
                  rayMap ⁻¹' (epigraph (S := (Set.univ : Set (Fin n → ℝ))) f) := by
              simp [hpre]
            simpa [hpre'] using hclosed_epi_f.preimage hcont
          have hSclosed : IsClosed {p : (Fin 1 → ℝ) × ℝ | 0 ≤ p.1 0} := by
            have hcont' : Continuous fun p : (Fin 1 → ℝ) × ℝ => p.1 0 := by
              simpa using (continuous_apply (0 : Fin 1)).comp continuous_fst
            simpa [Set.preimage] using (isClosed_Ici (a := (0 : ℝ))).preimage hcont'
          have hclosed :
              IsClosed (epigraph (S := S) (fun t => g (t 0 : EReal))) := by
            have hset :
                epigraph (S := S) (fun t => g (t 0 : EReal)) =
                  {p : (Fin 1 → ℝ) × ℝ | 0 ≤ p.1 0} ∩
                    {p : (Fin 1 → ℝ) × ℝ | f ((p.1 0) • y1) ≤ (p.2 : EReal)} := by
              ext p
              constructor
              · intro hp
                have hp' : p.1 ∈ S ∧ g (p.1 0 : EReal) ≤ (p.2 : EReal) := by
                  simpa [epigraph] using hp
                have hp0 : 0 ≤ p.1 0 := by simpa [S] using hp'.1
                have hgy : g (p.1 0 : EReal) = f ((p.1 0) • y1) := hgy1 _ hp0
                exact ⟨by simpa using hp0, by simpa [hgy] using hp'.2⟩
              · rintro ⟨hp0, hp_f⟩
                have hp0' : p.1 ∈ S := by simpa [S] using hp0
                have hgy : g (p.1 0 : EReal) = f ((p.1 0) • y1) := hgy1 _ hp0
                exact ⟨hp0', by simpa [hgy] using hp_f⟩
            simpa [hset] using hSclosed.inter hclosed_pre
          simpa [S] using hclosed
        ·
          -- Degenerate case: the epigraph is closed because `g` is constant on `ℝ≥0`.
          have hdeg : ∀ y : Fin n → ℝ, k y = 0 ∨ k y = ⊤ := by
            intro y
            by_contra h
            have hy0 : (0 : EReal) < k y := by
              have hnonneg : 0 ≤ k y := hk.1.2.1 y
              have hne0 : k y ≠ 0 := by
                intro h0
                exact h (Or.inl h0)
              exact lt_of_le_of_ne hnonneg (Ne.symm hne0)
            have hytop : k y < ⊤ := by
              have hne_top : k y ≠ ⊤ := by
                intro htop
                exact h (Or.inr htop)
              exact lt_of_le_of_ne le_top hne_top
            exact hpos ⟨y, hy0, hytop⟩
          let S : Set (Fin 1 → ℝ) := {t | 0 ≤ t 0}
          have hconst :
              ∀ s : ℝ, 0 ≤ s → g (s : EReal) = g (1 : EReal) := by
            intro s hs
            have hsub :
                {x | k x ≤ (s : EReal)} = {x | k x ≤ (1 : EReal)} := by
              ext x
              rcases hdeg x with hx | hx
              · have hs' : (0 : EReal) ≤ (s : EReal) := by
                  exact_mod_cast hs
                have h1' : (0 : EReal) ≤ (1 : EReal) := by simp
                simp [hx, hs', h1']
              · have hs' : ¬ (⊤ : EReal) ≤ (s : EReal) := not_top_le_coe s
                have h1' : ¬ (⊤ : EReal) ≤ (1 : EReal) := not_top_le_coe 1
                simp [hx, hs', h1']
            have hprof :
                profileSet f k (s : EReal) = profileSet f k (1 : EReal) := by
              ext α
              constructor
              · intro hα
                rcases hα with ⟨h0, htop, hsub'⟩
                refine ⟨h0, htop, ?_⟩
                simpa [hsub] using hsub'
              · intro hα
                rcases hα with ⟨h0, htop, hsub'⟩
                refine ⟨h0, htop, ?_⟩
                simpa [hsub] using hsub'
            have hsne : (s : EReal) ≠ ⊤ := by
              exact ne_of_lt (EReal.coe_lt_top s)
            have h1ne : (1 : EReal) ≠ ⊤ := by
              exact ne_of_lt (EReal.coe_lt_top (1 : ℝ))
            simp [g, hsne, h1ne, hprof]
          have hconst0 : g (0 : EReal) = g (1 : EReal) := by
            have hsub :
                {x | k x ≤ (0 : EReal)} = {x | k x ≤ (1 : EReal)} := by
              ext x
              rcases hdeg x with hx | hx
              · simp [hx]
              · have h0' : ¬ (⊤ : EReal) ≤ (0 : EReal) := by
                  simp
                have h1' : ¬ (⊤ : EReal) ≤ (1 : EReal) := not_top_le_coe 1
                simp [hx, h0', h1']
            have hprof :
                profileSet f k (0 : EReal) = profileSet f k (1 : EReal) := by
              ext α
              constructor
              · intro hα
                rcases hα with ⟨h0, htop, hsub'⟩
                refine ⟨h0, htop, ?_⟩
                simpa [hsub] using hsub'
              · intro hα
                rcases hα with ⟨h0, htop, hsub'⟩
                refine ⟨h0, htop, ?_⟩
                simpa [hsub] using hsub'
            have h0ne : (0 : EReal) ≠ ⊤ := by
              exact ne_of_lt (EReal.coe_lt_top (0 : ℝ))
            have h1ne : (1 : EReal) ≠ ⊤ := by
              exact ne_of_lt (EReal.coe_lt_top (1 : ℝ))
            simp [g, h0ne, h1ne, hprof]
          have hclosed :
              IsClosed (epigraph (S := S) (fun t => g (t 0 : EReal))) := by
            have hSclosed : IsClosed {p : (Fin 1 → ℝ) × ℝ | 0 ≤ p.1 0} := by
              have hcont' : Continuous fun p : (Fin 1 → ℝ) × ℝ => p.1 0 := by
                simpa using (continuous_apply (0 : Fin 1)).comp continuous_fst
              simpa [Set.preimage] using (isClosed_Ici (a := (0 : ℝ))).preimage hcont'
            have hmuclosed :
                IsClosed {p : (Fin 1 → ℝ) × ℝ | g (1 : EReal) ≤ (p.2 : EReal)} := by
              have hcont' : Continuous fun p : (Fin 1 → ℝ) × ℝ => p.2 := continuous_snd
              by_cases htop : g (1 : EReal) = ⊤
              · have hset : {p : (Fin 1 → ℝ) × ℝ | g (1 : EReal) ≤ (p.2 : EReal)} = ∅ := by
                  ext p
                  simp [htop]
                simp [hset]
              · by_cases hbot : g (1 : EReal) = ⊥
                · have hset :
                      {p : (Fin 1 → ℝ) × ℝ | g (1 : EReal) ≤ (p.2 : EReal)} = Set.univ := by
                    ext p
                    simp [hbot]
                  simp [hset]
                · set r : ℝ := (g (1 : EReal)).toReal
                  have hco : g (1 : EReal) = (r : EReal) := by
                    simpa [r] using (EReal.coe_toReal (x := g (1 : EReal)) htop hbot).symm
                  have hset :
                      {p : (Fin 1 → ℝ) × ℝ | g (1 : EReal) ≤ (p.2 : EReal)} =
                        {p : (Fin 1 → ℝ) × ℝ | r ≤ p.2} := by
                    ext p
                    simp [hco]
                  simpa [hset] using (isClosed_le continuous_const hcont')
            have hset :
                epigraph (S := S) (fun t => g (t 0 : EReal)) =
                  {p : (Fin 1 → ℝ) × ℝ | 0 ≤ p.1 0} ∩
                    {p : (Fin 1 → ℝ) × ℝ | g (1 : EReal) ≤ (p.2 : EReal)} := by
              ext p
              constructor
              · intro hp
                have hp' : p.1 ∈ S ∧ g (p.1 0 : EReal) ≤ (p.2 : EReal) := by
                  simpa [epigraph] using hp
                have hp0 : 0 ≤ p.1 0 := by simpa [S] using hp'.1
                have hgy : g (p.1 0 : EReal) = g (1 : EReal) := hconst _ hp0
                exact ⟨by simpa using hp0, by simpa [hgy] using hp'.2⟩
              · rintro ⟨hp0, hpμ⟩
                have hp0' : p.1 ∈ S := by simpa [S] using hp0
                have hgy : g (p.1 0 : EReal) = g (1 : EReal) := hconst _ hp0
                exact ⟨hp0', by simpa [hgy] using hpμ⟩
            simpa [hset] using hSclosed.inter hmuclosed
          simpa [S] using hclosed
      · exact hfg
    ·
      -- Degenerate case: no positive finite values of `k`.
      have hdeg : ∀ y : Fin n → ℝ, k y = 0 ∨ k y = ⊤ := by
        intro y
        by_contra h
        have hy0 : (0 : EReal) < k y := by
          have hnonneg : 0 ≤ k y := hk.1.2.1 y
          have hne0 : k y ≠ 0 := by
            intro h0
            exact h (Or.inl h0)
          exact lt_of_le_of_ne hnonneg (Ne.symm hne0)
        have hytop : k y < ⊤ := by
          have hne_top : k y ≠ ⊤ := by
            intro htop
            exact h (Or.inr htop)
          exact lt_of_le_of_ne le_top hne_top
        exact hpos ⟨y, hy0, hytop⟩
      have hk0 : k 0 = 0 := (hk.1).2.2.2
      have hc_eq : g (0 : EReal) = f 0 := by
        simp [hfg, hk0]
      have hc_ne_top : g (0 : EReal) ≠ ⊤ := by
        have h0lt : f 0 < ⊤ := lt_of_lt_of_le hβ0 le_top
        simpa [hc_eq] using (ne_of_lt h0lt)
      have hc_ne_bot : g (0 : EReal) ≠ ⊥ := by
        simpa [hc_eq] using h0_ne_bot
      let g' : EReal → EReal := fun z =>
        if z = ⊤ then ⊤ else if z ≤ (1 : EReal) then g (0 : EReal) else ⊤
      have hg'_mono : Monotone g' := by
        intro z1 z2 hz
        by_cases hz2 : z2 = ⊤
        · simp [g', hz2]
        ·
          have hz1 : z1 ≠ ⊤ := by
            intro hz1
            apply hz2
            have : (⊤ : EReal) ≤ z2 := by simpa [hz1] using hz
            exact (top_le_iff.mp this)
          by_cases hz2le : z2 ≤ (1 : EReal)
          · have hz1le : z1 ≤ (1 : EReal) := le_trans hz hz2le
            simp [g', hz1, hz2, hz1le, hz2le]
          · simp [g', hz1, hz2, hz2le]
      have hg'_top : g' ⊤ = ⊤ := by
        simp [g']
      have hζ' : ∃ ζ : ℝ, 0 < ζ ∧ g' (ζ : EReal) ≠ ⊤ ∧ g' (ζ : EReal) ≠ ⊥ := by
        refine ⟨1, by norm_num, ?_, ?_⟩
        · simp [g', h1top, hc_ne_top]
        · simp [g', h1top, hc_ne_bot]
      have hstrict' : ∃ s : ℝ, 0 < s ∧ g' (0 : EReal) < g' (s : EReal) := by
        refine ⟨2, by norm_num, ?_⟩
        have h0 : g' (0 : EReal) = g (0 : EReal) := by
          simp [g']
        have h2 : g' ((2 : ℝ) : EReal) = ⊤ := by
          have hlt : (1 : EReal) < ((2 : ℝ) : EReal) := by
            exact_mod_cast (by norm_num : (1 : ℝ) < (2 : ℝ))
          have hnot : ¬ ((2 : ℝ) : EReal) ≤ (1 : EReal) := not_le_of_gt hlt
          simp [g', hnot]
        have hlt : g (0 : EReal) < ⊤ := by
          have h0lt : f 0 < ⊤ := lt_of_lt_of_le hβ0 le_top
          simpa [hc_eq] using h0lt
        simpa [h0, h2] using hlt
      have hfg' : f = fun x => g' (k x) := by
        ext x
        rcases hdeg x with hx | hx
        · have hx' : f x = g (0 : EReal) := by
            simp [hfg, hx]
          simpa [g', hx, hc_eq] using hx'
        · have hx' : f x = g ⊤ := by
            simp [hfg, hx]
          simp [g', hx, hg_top, hx']
      let S : Set (Fin 1 → ℝ) := {t | 0 ≤ t 0}
      have hSconv : Convex ℝ S := by
        intro x hx y hy a b ha hb hab
        have hx0 : 0 ≤ x 0 := hx
        have hy0 : 0 ≤ y 0 := hy
        have hcomb : 0 ≤ a * x 0 + b * y 0 := by
          nlinarith [ha, hb, hx0, hy0]
        simpa [S, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hcomb
      have hnotbot : ∀ t ∈ S, g' (t 0 : EReal) ≠ ⊥ := by
        intro t ht
        by_cases ht1 : t 0 ≤ 1
        ·
          have ht1' : (t 0 : EReal) ≤ (1 : EReal) := by exact_mod_cast ht1
          simp [g', ht1', hc_ne_bot]
        ·
          have ht1lt : (1 : EReal) < (t 0 : EReal) := by
            exact_mod_cast (lt_of_not_ge ht1)
          have ht1' : ¬ (t 0 : EReal) ≤ (1 : EReal) := not_le_of_gt ht1lt
          simp [g', ht1']
      have hg'_conv :
          ConvexFunctionOn (S := S) (fun t => g' (t 0 : EReal)) := by
        refine
          (convexFunctionOn_iff_segment_inequality (C := S)
            (f := fun t : Fin 1 → ℝ => g' (t 0 : EReal))
            (hC := hSconv) (hnotbot := hnotbot)).2 ?_
        intro x hx y hy t ht0 ht1
        have ht0' : 0 ≤ t := le_of_lt ht0
        have ht1' : 0 ≤ 1 - t := by linarith
        by_cases hx1 : x 0 ≤ 1
        · by_cases hy1 : y 0 ≤ 1
          ·
            have hcomb : (1 - t) * x 0 + t * y 0 ≤ 1 := by
              nlinarith [hx1, hy1, ht0', ht1']
            have hcomb' :
                ((1 - t) * x 0 + t * y 0 : EReal) ≤ (1 : EReal) := by
              exact_mod_cast hcomb
            have hcomb_top :
                ((1 - t) * x 0 + t * y 0 : EReal) ≠ ⊤ := by
              exact EReal.coe_ne_top _
            have hL :
                g' (((1 - t) • x + t • y) 0 : EReal) = g (0 : EReal) := by
              simp [g', hcomb', hcomb_top, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            have hx1' : (x 0 : EReal) ≤ (1 : EReal) := by exact_mod_cast hx1
            have hy1' : (y 0 : EReal) ≤ (1 : EReal) := by exact_mod_cast hy1
            have hx0_top : (x 0 : EReal) ≠ ⊤ := by exact EReal.coe_ne_top _
            have hy0_top : (y 0 : EReal) ≠ ⊤ := by exact EReal.coe_ne_top _
            have hxg : g' (x 0 : EReal) = g (0 : EReal) := by
              simp [g', hx0_top, hx1']
            have hyg : g' (y 0 : EReal) = g (0 : EReal) := by
              simp [g', hy0_top, hy1']
            set r : ℝ := (g (0 : EReal)).toReal
            have hc : g (0 : EReal) = (r : EReal) := by
              simpa [r] using
                (EReal.coe_toReal (x := g (0 : EReal)) hc_ne_top hc_ne_bot).symm
            have hsum :
                ((1 - t : ℝ) : EReal) * g (0 : EReal) +
                  ((t : ℝ) : EReal) * g (0 : EReal) = g (0 : EReal) := by
              have hsum' : (1 - t) * r + t * r = r := by ring
              have hsum'' :
                  ((1 - t : ℝ) : EReal) * (r : EReal) +
                    ((t : ℝ) : EReal) * (r : EReal) = (r : EReal) := by
                exact_mod_cast hsum'
              simpa [hc] using hsum''
            calc
              g' (((1 - t) • x + t • y) 0 : EReal) = g (0 : EReal) := hL
              _ ≤ ((1 - t : ℝ) : EReal) * g (0 : EReal) +
                    ((t : ℝ) : EReal) * g (0 : EReal) := by
                exact le_of_eq hsum.symm
              _ = ((1 - t : ℝ) : EReal) * g' (x 0 : EReal) +
                    ((t : ℝ) : EReal) * g' (y 0 : EReal) := by
                simp [hxg, hyg]
          ·
            have hy1lt : (1 : EReal) < (y 0 : EReal) := by
              exact_mod_cast (lt_of_not_ge hy1)
            have hy1' : ¬ (y 0 : EReal) ≤ (1 : EReal) := not_le_of_gt hy1lt
            have hyg : g' (y 0 : EReal) = ⊤ := by
              simp [g', hy1']
            have hR :
                ((1 - t : ℝ) : EReal) * g' (x 0 : EReal) +
                  ((t : ℝ) : EReal) * g' (y 0 : EReal) = ⊤ := by
              have ht0' : (0 : EReal) < ((t : ℝ) : EReal) := by
                exact_mod_cast ht0
              have hmul_top : ((t : ℝ) : EReal) * (⊤ : EReal) = ⊤ := by
                simpa using (EReal.mul_top_of_pos ht0')
              have hx1' : (x 0 : EReal) ≤ (1 : EReal) := by exact_mod_cast hx1
              have hx0_top : (x 0 : EReal) ≠ ⊤ := by exact EReal.coe_ne_top _
              have hxg : g' (x 0 : EReal) = g (0 : EReal) := by
                simp [g', hx0_top, hx1']
              set r : ℝ := (g (0 : EReal)).toReal
              have hc : g (0 : EReal) = (r : EReal) := by
                simpa [r] using
                  (EReal.coe_toReal (x := g (0 : EReal)) hc_ne_top hc_ne_bot).symm
              have hx_term_ne_bot :
                  ((1 - t : ℝ) : EReal) * g' (x 0 : EReal) ≠ ⊥ := by
                have hx_term_eq :
                    ((1 - t : ℝ) : EReal) * g' (x 0 : EReal) =
                      (((1 - t) * r : ℝ) : EReal) := by
                  calc
                    ((1 - t : ℝ) : EReal) * g' (x 0 : EReal) =
                        ((1 - t : ℝ) : EReal) * g (0 : EReal) := by
                      simp [hxg]
                    _ = ((1 - t : ℝ) : EReal) * (r : EReal) := by
                      simp [hc]
                    _ = (((1 - t) * r : ℝ) : EReal) := by
                      simp [EReal.coe_mul]
                simpa [hx_term_eq.symm] using (EReal.coe_ne_bot ((1 - t) * r))
              calc
                ((1 - t : ℝ) : EReal) * g' (x 0 : EReal) +
                    ((t : ℝ) : EReal) * g' (y 0 : EReal) =
                    ((1 - t : ℝ) : EReal) * g' (x 0 : EReal) + ⊤ := by
                  simp [hyg, hmul_top]
                _ = ⊤ := by
                  simpa using (EReal.add_top_of_ne_bot hx_term_ne_bot)
            rw [hR]
            exact le_top
        ·
          have hx1lt : (1 : EReal) < (x 0 : EReal) := by
            exact_mod_cast (lt_of_not_ge hx1)
          have hx1' : ¬ (x 0 : EReal) ≤ (1 : EReal) := not_le_of_gt hx1lt
          have hxg : g' (x 0 : EReal) = ⊤ := by
            simp [g', hx1']
          have ht1pos : 0 < 1 - t := by linarith
          have hR :
              ((1 - t : ℝ) : EReal) * g' (x 0 : EReal) +
                ((t : ℝ) : EReal) * g' (y 0 : EReal) = ⊤ := by
            have ht1' : (0 : EReal) < ((1 - t : ℝ) : EReal) := by
              exact_mod_cast ht1pos
            have hmul_top : ((1 - t : ℝ) : EReal) * (⊤ : EReal) = ⊤ := by
              simpa using (EReal.mul_top_of_pos ht1')
            by_cases hy1 : y 0 ≤ 1
            ·
              have hy1' : (y 0 : EReal) ≤ (1 : EReal) := by exact_mod_cast hy1
              have hy0_top : (y 0 : EReal) ≠ ⊤ := by exact EReal.coe_ne_top _
              have hyg : g' (y 0 : EReal) = g (0 : EReal) := by
                simp [g', hy0_top, hy1']
              set r : ℝ := (g (0 : EReal)).toReal
              have hc : g (0 : EReal) = (r : EReal) := by
                simpa [r] using
                  (EReal.coe_toReal (x := g (0 : EReal)) hc_ne_top hc_ne_bot).symm
              have hy_term_ne_bot :
                  ((t : ℝ) : EReal) * g' (y 0 : EReal) ≠ ⊥ := by
                have hy_term_eq :
                    ((t : ℝ) : EReal) * g' (y 0 : EReal) = ((t * r : ℝ) : EReal) := by
                  calc
                    ((t : ℝ) : EReal) * g' (y 0 : EReal) =
                        ((t : ℝ) : EReal) * g (0 : EReal) := by
                      simp [hyg]
                    _ = ((t : ℝ) : EReal) * (r : EReal) := by
                      simp [hc]
                    _ = ((t * r : ℝ) : EReal) := by
                      simp [EReal.coe_mul]
                simpa [hy_term_eq.symm] using (EReal.coe_ne_bot (t * r))
              calc
                ((1 - t : ℝ) : EReal) * g' (x 0 : EReal) +
                    ((t : ℝ) : EReal) * g' (y 0 : EReal) =
                    ((1 - t : ℝ) : EReal) * ⊤ +
                      ((t : ℝ) : EReal) * g' (y 0 : EReal) := by
                  rw [hxg]
                _ = ⊤ + ((t : ℝ) : EReal) * g' (y 0 : EReal) := by
                  rw [hmul_top]
                _ = ⊤ := by
                  simpa using (EReal.top_add_of_ne_bot hy_term_ne_bot)
            ·
              have hy1lt : (1 : EReal) < (y 0 : EReal) := by
                exact_mod_cast (lt_of_not_ge hy1)
              have hy1' : ¬ (y 0 : EReal) ≤ (1 : EReal) := not_le_of_gt hy1lt
              have hyg : g' (y 0 : EReal) = ⊤ := by
                simp [g', hy1']
              have ht0' : (0 : EReal) < ((t : ℝ) : EReal) := by
                exact_mod_cast ht0
              have hmul_top' : ((t : ℝ) : EReal) * (⊤ : EReal) = ⊤ := by
                simpa using (EReal.mul_top_of_pos ht0')
              calc
                ((1 - t : ℝ) : EReal) * g' (x 0 : EReal) +
                    ((t : ℝ) : EReal) * g' (y 0 : EReal) =
                    ((1 - t : ℝ) : EReal) * ⊤ + ((t : ℝ) : EReal) * ⊤ := by
                  rw [hxg, hyg]
                _ = ⊤ + ⊤ := by
                  rw [hmul_top, hmul_top']
                _ = ⊤ := by simp
          rw [hR]
          exact le_top
      have hg'_closed :
          IsClosed (epigraph (S := S) (fun t => g' (t 0 : EReal))) := by
        have hSclosed : IsClosed {p : (Fin 1 → ℝ) × ℝ | 0 ≤ p.1 0} := by
          have hcont' : Continuous fun p : (Fin 1 → ℝ) × ℝ => p.1 0 := by
            simpa using (continuous_apply (0 : Fin 1)).comp continuous_fst
          simpa [Set.preimage] using (isClosed_Ici (a := (0 : ℝ))).preimage hcont'
        have hSclosed1 : IsClosed {p : (Fin 1 → ℝ) × ℝ | p.1 0 ≤ (1 : ℝ)} := by
          have hcont' : Continuous fun p : (Fin 1 → ℝ) × ℝ => p.1 0 := by
            simpa using (continuous_apply (0 : Fin 1)).comp continuous_fst
          simpa [Set.preimage] using (isClosed_Iic (a := (1 : ℝ))).preimage hcont'
        set r : ℝ := (g (0 : EReal)).toReal
        have hc : g (0 : EReal) = (r : EReal) := by
          simpa [r] using
            (EReal.coe_toReal (x := g (0 : EReal)) hc_ne_top hc_ne_bot).symm
        have hmuclosed :
            IsClosed {p : (Fin 1 → ℝ) × ℝ | g (0 : EReal) ≤ (p.2 : EReal)} := by
          have hset :
              {p : (Fin 1 → ℝ) × ℝ | g (0 : EReal) ≤ (p.2 : EReal)} =
                {p : (Fin 1 → ℝ) × ℝ | r ≤ p.2} := by
            ext p
            simp [hc]
          have hcont' : Continuous fun p : (Fin 1 → ℝ) × ℝ => p.2 := continuous_snd
          simpa [hset] using (isClosed_le continuous_const hcont')
        have hset :
            epigraph (S := S) (fun t => g' (t 0 : EReal)) =
              {p : (Fin 1 → ℝ) × ℝ | 0 ≤ p.1 0} ∩
                {p : (Fin 1 → ℝ) × ℝ | p.1 0 ≤ (1 : ℝ)} ∩
                  {p : (Fin 1 → ℝ) × ℝ | g (0 : EReal) ≤ (p.2 : EReal)} := by
          ext p
          constructor
          · intro hp
            have hp' : p.1 ∈ S ∧ g' (p.1 0 : EReal) ≤ (p.2 : EReal) := by
              simpa [epigraph] using hp
            have hp0 : 0 ≤ p.1 0 := by simpa [S] using hp'.1
            have hp1 : p.1 0 ≤ 1 := by
              by_contra hp1
              have hp1lt : (1 : EReal) < (p.1 0 : EReal) := by
                exact_mod_cast (lt_of_not_ge hp1)
              have hp1' : ¬ (p.1 0 : EReal) ≤ (1 : EReal) := not_le_of_gt hp1lt
              have htop : g' (p.1 0 : EReal) = ⊤ := by
                simp [g', hp1']
              have : ¬ g' (p.1 0 : EReal) ≤ (p.2 : EReal) := by
                simp [htop]
              exact this hp'.2
            have hp1' : (p.1 0 : EReal) ≤ (1 : EReal) := by exact_mod_cast hp1
            have hgc : g' (p.1 0 : EReal) = g (0 : EReal) := by
              simp [g', hp1']
            have hmu : g (0 : EReal) ≤ (p.2 : EReal) := by
              simpa [hgc] using hp'.2
            exact ⟨⟨by simpa using hp0, by simpa using hp1⟩, hmu⟩
          · rintro ⟨⟨hp0, hp1⟩, hmu⟩
            have hp0' : p.1 ∈ S := by simpa [S] using hp0
            have hp1' : (p.1 0 : EReal) ≤ (1 : EReal) := by exact_mod_cast hp1
            have hgc : g' (p.1 0 : EReal) = g (0 : EReal) := by
              simp [g', hp1']
            have hmu' : g' (p.1 0 : EReal) ≤ (p.2 : EReal) := by
              simpa [hgc] using hmu
            exact ⟨hp0', hmu'⟩
        simpa [hset, Set.inter_assoc] using hSclosed.inter (hSclosed1.inter hmuclosed)
      exact ⟨k, g', hk, hζ', hstrict', hg'_mono, hg'_conv, hg'_closed, hg'_top, hfg'⟩
  · rintro ⟨k, g, hk, hζ, hstrict, hmono, hconv, hclosed, htop, hfg⟩
    rcases hζ with ⟨ζ, hζpos, hζtop, hζbot⟩
    have h0_ne_bot : g (0 : EReal) ≠ ⊥ :=
      g0_ne_bot_of_convex_closed_and_exists_finite_nonneg (g := g)
        hconv hclosed ⟨ζ, hζpos, hζtop, hζbot⟩
    have h0_ne_top : g (0 : EReal) ≠ ⊤ := by
      have hle : g (0 : EReal) ≤ g (ζ : EReal) := by
        have hz : (0 : EReal) ≤ (ζ : EReal) := by exact_mod_cast (le_of_lt hζpos)
        exact hmono hz
      intro h0top
      have : (⊤ : EReal) ≤ g (ζ : EReal) := by simpa [h0top] using hle
      exact hζtop (top_le_iff.mp this)
    have hnotbot : ∀ x : Fin n → ℝ, g (k x) ≠ ⊥ := by
      intro x
      exact monotone_ne_bot_of_nonneg (g := g) hmono h0_ne_bot (k x) ((hk.1).2.1 x)
    have hne_epi : Set.Nonempty (epigraph (S := (Set.univ : Set (Fin n → ℝ))) f) := by
      refine ⟨(0, (g (0 : EReal)).toReal), ?_⟩
      have hco : ((g (0 : EReal)).toReal : EReal) = g (0 : EReal) := by
        simpa using (EReal.coe_toReal (x := g (0 : EReal)) h0_ne_top h0_ne_bot)
      have hk0 : k 0 = 0 := (hk.1).2.2.2
      have h0 : f 0 ≤ ((g (0 : EReal)).toReal : EReal) := by
        have : f 0 = g (0 : EReal) := by simp [hfg, hk0]
        simp [this, hco]
      have h0mem : (0 : Fin n → ℝ) ∈ (Set.univ : Set (Fin n → ℝ)) := by
        simp
      exact ⟨h0mem, h0⟩
    have hk0 : k 0 = 0 := (hk.1).2.2.2
    have h0_le_fx : ∀ x : Fin n → ℝ, f 0 ≤ f x := by
      intro x
      have hk_nonneg : (0 : EReal) ≤ k x := (hk.1).2.1 x
      have hmono0 : g (0 : EReal) ≤ g (k x) := hmono hk_nonneg
      simpa [hfg, hk0] using hmono0
    have hmin : f 0 = sInf (Set.range f) := by
      apply le_antisymm
      · refine le_sInf ?_
        intro y hy
        rcases hy with ⟨x, rfl⟩
        exact h0_le_fx x
      · exact sInf_le ⟨0, rfl⟩
    have hcomp :
        IsGaugeLikeClosedProperConvex (fun x : Fin n → ℝ => g (k x)) :=
      comp_closedGauge_gives_gaugeLikeClosedProperConvex (n := n) (k := k) (g := g) hk hmono
        hconv hclosed htop ⟨ζ, hζpos, hζtop, hζbot⟩ hstrict
    simpa [hfg] using hcomp

/-- Formula part of Theorem 15.3 for the conjugate of `g ∘ k`. -/
lemma fenchelConjugate_eq_monotoneConjugate_polarGauge_of_comp_formula {n : ℕ}
    {f : (Fin n → ℝ) → EReal} {k : (Fin n → ℝ) → EReal} {g : EReal → EReal}
    (hk : IsClosedGauge k) (hfg : f = fun x => g (k x)) (hg_mono : Monotone g)
    (hg_top : g ⊤ = ⊤)
    (hζ : ∃ ζ : ℝ, 0 < ζ ∧ g (ζ : EReal) ≠ ⊤ ∧ g (ζ : EReal) ≠ ⊥) :
    ∀ xStar : Fin n → ℝ,
      fenchelConjugate n f xStar = monotoneConjugateERealNonneg g (polarGauge k xStar) := by
  classical
  intro xStar
  apply le_antisymm
  · by_cases hpol_top : polarGauge k xStar = ⊤
    · have htop' :
          monotoneConjugateERealNonneg g (polarGauge k xStar) = ⊤ := by
        simpa [hpol_top] using
          monotoneConjugateERealNonneg_top_of_exists_finite (g := g) hζ
      simp [htop']
    ·
      have hle : ∀ x : Fin n → ℝ,
          ((x ⬝ᵥ xStar : ℝ) : EReal) - f x ≤
            monotoneConjugateERealNonneg g (polarGauge k xStar) := by
        intro x
        by_cases hkx_top : k x = ⊤
        · have hfx : f x = ⊤ := by simp [hfg, hkx_top, hg_top]
          simp [hfx]
        · have hkx_nonneg : (0 : EReal) ≤ k x := (hk.1).2.1 x
          have hdot_le :
              ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ k x * polarGauge k xStar :=
            inner_le_mul_polarGauge (hk := hk.1) (x := x) (xStar := xStar) hkx_top hpol_top
          have hterm_le :
              ((x ⬝ᵥ xStar : ℝ) : EReal) - g (k x) ≤
                k x * polarGauge k xStar - g (k x) :=
            by
              have h := add_le_add_left hdot_le (- g (k x))
              simpa [sub_eq_add_neg] using h
          have hterm_le2 :
              k x * polarGauge k xStar - g (k x) ≤
                monotoneConjugateERealNonneg g (polarGauge k xStar) :=
            term_le_monotoneConjugateERealNonneg (g := g) (s := polarGauge k xStar)
              (t := k x) hkx_nonneg
          simpa [hfg] using hterm_le.trans hterm_le2
      have hle_iSup :
          iSup (fun x : Fin n → ℝ => ((x ⬝ᵥ xStar : ℝ) : EReal) - f x) ≤
            monotoneConjugateERealNonneg g (polarGauge k xStar) :=
        iSup_le hle
      simpa [fenchelConjugate_eq_iSup] using hle_iSup
  ·
    unfold monotoneConjugateERealNonneg
    refine sSup_le ?_
    rintro _ ⟨t, ht, rfl⟩
    by_cases ht_top : t = ⊤
    · simp [ht_top, hg_top]
    ·
      have ht_ne_bot : t ≠ (⊥ : EReal) := by
        intro hbot
        rw [hbot] at ht
        have hbot_lt : (⊥ : EReal) < (0 : EReal) := by
          simp
        exact (not_le_of_gt hbot_lt) ht
      set r : ℝ := t.toReal
      have ht_eq : (r : EReal) = t := by
        exact EReal.coe_toReal (x := t) ht_top ht_ne_bot
      have hr_nonneg : 0 ≤ r := by
        have : (0 : EReal) ≤ (r : EReal) := by simpa [ht_eq] using ht
        exact (EReal.coe_le_coe_iff).1 this
      let C : Set (Fin n → ℝ) := {y | k y ≤ (1 : EReal)}
      have hpol_r : t * polarGauge k xStar = polarGauge k (r • xStar) := by
        have hkpol : IsGauge (polarGauge k) := polarGauge_isGauge (k := k)
        calc
          t * polarGauge k xStar = ((r : ℝ) : EReal) * polarGauge k xStar := by
            simp [ht_eq]
          _ = polarGauge k (r • xStar) := by
            simpa using (hkpol.2.2.1 xStar r hr_nonneg).symm
      have hpol_support :
          polarGauge k (r • xStar) = supportFunctionEReal C (r • xStar) := by
        have h :=
          supportFunction_unitSublevel_eq_polarGauge_of_isGauge (hk := hk.1) (xStar := r • xStar)
        simpa [C] using h.symm
      have hle_support :
          supportFunctionEReal C (r • xStar) - g t ≤ fenchelConjugate n f xStar := by
        by_cases hgtop : g t = ⊤
        ·
          have hbot : supportFunctionEReal C (r • xStar) - g t = (⊥ : EReal) := by
            simp [hgtop, sub_eq_add_neg, EReal.neg_top, EReal.add_bot]
          simp [hbot]
        ·
          by_cases hgbot : g t = ⊥
          ·
            have h0bot : g (0 : EReal) = ⊥ := by
              have hle0 : g (0 : EReal) ≤ g t := hg_mono (by simpa using ht)
              have hle0' : g (0 : EReal) ≤ (⊥ : EReal) := by simpa [hgbot] using hle0
              exact le_bot_iff.mp hle0'
            have hf0 : f 0 = ⊥ := by
              have hk0 : k 0 = 0 := (hk.1).2.2.2
              simp [hfg, hk0, h0bot]
            have htop_term :
                ((0 ⬝ᵥ xStar : ℝ) : EReal) - f 0 = (⊤ : EReal) := by
              have hdot : (0 ⬝ᵥ xStar : ℝ) = 0 := by simp
              simp [hdot, hf0]
            have htop_le : (⊤ : EReal) ≤ fenchelConjugate n f xStar := by
              have hle' :
                  ((0 ⬝ᵥ xStar : ℝ) : EReal) - f 0 ≤
                    iSup (fun x : Fin n → ℝ => ((x ⬝ᵥ xStar : ℝ) : EReal) - f x) :=
                le_iSup (fun x : Fin n → ℝ => ((x ⬝ᵥ xStar : ℝ) : EReal) - f x) 0
              have hle'' :
                  (⊤ : EReal) ≤
                    iSup (fun x : Fin n → ℝ => ((x ⬝ᵥ xStar : ℝ) : EReal) - f x) := by
                have hle'' := hle'
                rw [htop_term] at hle''
                exact hle''
              simpa [fenchelConjugate_eq_iSup] using hle''
            have hfen_top : fenchelConjugate n f xStar = ⊤ := top_le_iff.mp htop_le
            simp [hfen_top]
          ·
            lift g t to ℝ using ⟨hgtop, hgbot⟩ with μ hμ
            have hμ' : g t = (μ : EReal) := hμ.symm
            set A : Set EReal :=
              {z : EReal | ∃ y ∈ C, z = ((dotProduct y (r • xStar) : ℝ) : EReal)}
            set B : Set EReal :=
              {z : EReal | ∃ y ∈ C, z = ((dotProduct y (r • xStar) : ℝ) : EReal) - g t}
            have hterm :
                ∀ y ∈ C,
                  ((y ⬝ᵥ (r • xStar) : ℝ) : EReal) - g t ≤
                    fenchelConjugate n f xStar := by
              intro y hyC
              have hdot :
                  (y ⬝ᵥ (r • xStar) : ℝ) = ((r • y) ⬝ᵥ xStar : ℝ) := by
                simp [dotProduct_smul, smul_dotProduct]
              have hk_y : k y ≤ (1 : EReal) := hyC
              have hkxy : k (r • y) = ((r : ℝ) : EReal) * k y :=
                hk.1.2.2.1 y r hr_nonneg
              have hkxy_le : k (r • y) ≤ (r : EReal) := by
                have hmul_le :
                    ((r : ℝ) : EReal) * k y ≤ ((r : ℝ) : EReal) * (1 : EReal) := by
                  refine mul_le_mul_of_nonneg_left hk_y ?_
                  exact_mod_cast hr_nonneg
                have hmul : ((r : ℝ) : EReal) * (1 : EReal) = (r : EReal) := by simp
                simpa [hkxy, hmul] using hmul_le
              have hgle : g (k (r • y)) ≤ g t := by
                have hle : g (k (r • y)) ≤ g ((r : ℝ) : EReal) := hg_mono hkxy_le
                simpa [ht_eq] using hle
              have hsub :
                  ((r • y ⬝ᵥ xStar : ℝ) : EReal) - g t ≤
                    ((r • y ⬝ᵥ xStar : ℝ) : EReal) - g (k (r • y)) := by
                have hneg : - g t ≤ - g (k (r • y)) := (EReal.neg_le_neg_iff).2 hgle
                have hle' := add_le_add_left hneg ((r • y ⬝ᵥ xStar : ℝ) : EReal)
                simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hle'
              have hfenchel :
                  ((r • y ⬝ᵥ xStar : ℝ) : EReal) - g (k (r • y)) ≤
                    fenchelConjugate n f xStar := by
                have hle :
                    ((r • y ⬝ᵥ xStar : ℝ) : EReal) - f (r • y) ≤
                      fenchelConjugate n f xStar := by
                  have hle' :
                      ((r • y ⬝ᵥ xStar : ℝ) : EReal) - f (r • y) ≤
                        iSup (fun x : Fin n → ℝ => ((x ⬝ᵥ xStar : ℝ) : EReal) - f x) :=
                    le_iSup (fun x : Fin n → ℝ => ((x ⬝ᵥ xStar : ℝ) : EReal) - f x) (r • y)
                  simpa [fenchelConjugate_eq_iSup] using hle'
                simpa [hfg] using hle
              have hterm :
                  ((y ⬝ᵥ (r • xStar) : ℝ) : EReal) - g t ≤
                    fenchelConjugate n f xStar := by
                simpa [hdot] using hsub.trans hfenchel
              exact hterm
            have hLUB : IsLUB B (supportFunctionEReal C (r • xStar) - g t) := by
              refine ⟨?ub, ?lub⟩
              · intro z hz
                rcases hz with ⟨y, hyC, rfl⟩
                have hmem :
                    ((dotProduct y (r • xStar) : ℝ) : EReal) ∈ A := ⟨y, hyC, rfl⟩
                have hle : ((dotProduct y (r • xStar) : ℝ) : EReal) ≤ sSup A := le_sSup hmem
                have hle' := add_le_add_right hle (- g t)
                simpa [supportFunctionEReal, A, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
                  using hle'
              · intro u hu
                have hupperA : ∀ z ∈ A, z ≤ u + g t := by
                  intro z hz
                  rcases hz with ⟨y, hyC, rfl⟩
                  have hzB :
                      ((dotProduct y (r • xStar) : ℝ) : EReal) - g t ∈ B := ⟨y, hyC, rfl⟩
                  have hleB : ((dotProduct y (r • xStar) : ℝ) : EReal) - g t ≤ u := hu hzB
                  have hleB' := add_le_add_left hleB (g t)
                  have hleB'' :
                      ((dotProduct y (r • xStar) : ℝ) : EReal) - (μ : EReal) + (μ : EReal) ≤
                        u + (μ : EReal) := by
                    simpa [hμ'] using hleB'
                  have hleB''' :
                      ((dotProduct y (r • xStar) : ℝ) : EReal) ≤ u + (μ : EReal) := by
                    simpa [EReal.sub_add_cancel] using hleB''
                  simpa [hμ', add_comm] using hleB'''
                have hsup_le : sSup A ≤ u + g t := sSup_le hupperA
                have hle' := add_le_add_right hsup_le (- g t)
                have hle'' :
                    supportFunctionEReal C (r • xStar) - g t ≤ u + g t - g t := by
                  simpa [supportFunctionEReal, A, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
                    using hle'
                have hle''' :
                    supportFunctionEReal C (r • xStar) - (μ : EReal) ≤ u + (μ : EReal) - (μ : EReal) := by
                  simpa [hμ'] using hle''
                have hle'''' : supportFunctionEReal C (r • xStar) - (μ : EReal) ≤ u := by
                  simpa [EReal.add_sub_cancel_right] using hle'''
                simpa [hμ] using hle''''
            have hsup_eq : sSup B = supportFunctionEReal C (r • xStar) - g t :=
              (IsLUB.sSup_eq hLUB)
            have hsup_le : sSup B ≤ fenchelConjugate n f xStar := by
              refine sSup_le ?_
              rintro _ ⟨y, hyC, rfl⟩
              exact hterm y hyC
            have hsup_le' :
                supportFunctionEReal C (r • xStar) - (μ : EReal) ≤ fenchelConjugate n f xStar := by
              have hsup_le'' := hsup_le
              rw [hsup_eq] at hsup_le''
              rw [hμ'] at hsup_le''
              exact hsup_le''
            exact hsup_le'
      calc
        t * polarGauge k xStar - g t =
            polarGauge k (r • xStar) - g t := by simp [hpol_r]
        _ = supportFunctionEReal C (r • xStar) - g t := by simp [hpol_support]
        _ ≤ fenchelConjugate n f xStar := hle_support

end Section15
end Chap03
