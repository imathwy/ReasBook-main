/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yijie Wang, Yunxi Duan, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part8

section Chap03
section Section15

open scoped BigOperators
open scoped Pointwise
open scoped Topology
open Filter

/-- The polar gauge is bounded above by the support function of the unit sublevel. -/
lemma polarGauge_le_supportFunction_unitSublevel_of_isGauge {n : ℕ} {k : (Fin n → ℝ) → EReal}
    (hk : IsGauge k) (xStar : Fin n → ℝ) :
    polarGauge k xStar ≤ supportFunctionEReal {x | k x ≤ (1 : EReal)} xStar := by
  classical
  set C : Set (Fin n → ℝ) := {x | k x ≤ (1 : EReal)}
  set μ : EReal := supportFunctionEReal C xStar
  by_cases hμtop : μ = ⊤
  · simp [μ, hμtop]
  · have hC0 : (0 : Fin n → ℝ) ∈ C := by
      have hk0 : k 0 = 0 := hk.2.2.2
      have : k 0 ≤ (1 : EReal) := by simp [hk0]
      simpa [C] using this
    have hμ_nonneg : (0 : EReal) ≤ μ :=
      supportFunctionEReal_nonneg_of_zero_mem (C := C) hC0 xStar
    have hμtop' : μ ≠ ⊤ := hμtop
    have hdot_le_mu : ∀ y ∈ C, ((y ⬝ᵥ xStar : ℝ) : EReal) ≤ μ := by
      intro y hy
      unfold μ supportFunctionEReal
      refine le_sSup ?_
      exact ⟨y, hy, rfl⟩
    have hdot_le_zero :
        ∀ x : Fin n → ℝ, k x = 0 → ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ 0 := by
      intro x hx0
      exact
        dotProduct_le_zero_of_k_eq_zero_of_supportFunction_ne_top
          (hk := hk) (xStar := xStar) (x := x) (hμtop := by simpa [μ, C]) hx0
    by_cases hμ0 : μ = 0
    · have hfeasible_pos :
          ∀ r : ℝ, 0 < r →
            (0 : EReal) ≤ (r : EReal) ∧
              ∀ x : Fin n → ℝ, ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ (r : EReal) * k x := by
        intro r hr
        refine ⟨by exact_mod_cast (le_of_lt hr), ?_⟩
        intro x
        by_cases hkx_top : k x = ⊤
        · have : (r : EReal) * k x = ⊤ := by
            simpa [hkx_top] using (EReal.coe_mul_top_of_pos hr)
          simp [this]
        · by_cases hkx0 : k x = 0
          · have hdot0 : ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ 0 := hdot_le_zero x hkx0
            simpa [hkx0] using hdot0
          ·
            have hkx_ne_bot : k x ≠ (⊥ : EReal) := IsGauge.ne_bot hk x
            set t : ℝ := (k x).toReal
            have hkx_eq : (t : EReal) = k x := by
              simpa [t] using (EReal.coe_toReal (x := k x) hkx_top hkx_ne_bot)
            have hkx_pos : (0 : EReal) < k x :=
              lt_of_le_of_ne (hk.2.1 x) (Ne.symm hkx0)
            have htpos : 0 < t := by
              have : (0 : EReal) < (t : EReal) := by simpa [hkx_eq] using hkx_pos
              exact (EReal.coe_pos).1 this
            set y : Fin n → ℝ := (t⁻¹) • x
            have hyC : y ∈ C := by
              have hhom : k y = ((t⁻¹ : ℝ) : EReal) * k x :=
                hk.2.2.1 x t⁻¹ (le_of_lt (inv_pos.mpr htpos))
              have hmul :
                  ((t⁻¹ : ℝ) : EReal) * k x = (1 : EReal) := by
                have htne : t ≠ 0 := ne_of_gt htpos
                calc
                  ((t⁻¹ : ℝ) : EReal) * k x =
                  ((t⁻¹ : ℝ) : EReal) * (t : EReal) := by simp [hkx_eq]
                  _ = ((t⁻¹ * t : ℝ) : EReal) := by
                      simp [EReal.coe_mul]
                  _ = (1 : EReal) := by
                      have : (t⁻¹ * t : ℝ) = 1 := by field_simp [htne]
                      simp [this]
              have hle : k y ≤ (1 : EReal) := by simp [hhom, hmul]
              simpa [C, y] using hle
            have hdot_le0 : ((y ⬝ᵥ xStar : ℝ) : EReal) ≤ μ := hdot_le_mu y hyC
            have hdot_le0' : ((y ⬝ᵥ xStar : ℝ) : EReal) ≤ 0 := by
              simpa [hμ0] using hdot_le0
            have hnonneg_rhs : (0 : EReal) ≤ (r : EReal) * k x := by
              exact EReal.mul_nonneg (by exact_mod_cast (le_of_lt hr)) (hk.2.1 x)
            have hx_eq : x = t • y := by
              have htne : t ≠ 0 := ne_of_gt htpos
              simp [y, smul_smul, htne]
            have hdot_eq :
                ((x ⬝ᵥ xStar : ℝ) : EReal) =
                  (t : EReal) * ((y ⬝ᵥ xStar : ℝ) : EReal) := by
              have hdot_eq_real : (x ⬝ᵥ xStar : ℝ) = t * (y ⬝ᵥ xStar : ℝ) := by
                simp [hx_eq, smul_dotProduct]
              simp [hdot_eq_real, EReal.coe_mul]
            have hdot_le0x : ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ 0 := by
              have hmul :
                  (t : EReal) * ((y ⬝ᵥ xStar : ℝ) : EReal) ≤ (t : EReal) * (0 : EReal) := by
                have ht_nonneg : (0 : EReal) ≤ (t : EReal) := by exact_mod_cast (le_of_lt htpos)
                exact mul_le_mul_of_nonneg_left hdot_le0' ht_nonneg
              simpa [hdot_eq] using hmul
            exact le_trans hdot_le0x hnonneg_rhs
      have hle_pos :
          ∀ r : ℝ, 0 < r → polarGauge k xStar ≤ (r : EReal) := by
        intro r hr
        unfold polarGauge
        exact sInf_le (hfeasible_pos r hr)
      by_contra hpos
      have hpos' : (0 : EReal) < polarGauge k xStar :=
        lt_of_not_ge (by simpa [hμ0] using hpos)
      obtain ⟨r, hr0, hrlt⟩ := EReal.exists_between_coe_real hpos'
      have hr0' : 0 < r := (EReal.coe_pos).1 hr0
      have hle := hle_pos r hr0'
      exact (not_lt_of_ge hle) hrlt
    · have hμpos : (0 : EReal) < μ := lt_of_le_of_ne hμ_nonneg (Ne.symm hμ0)
      unfold polarGauge
      refine sInf_le ?_
      refine ⟨hμ_nonneg, ?_⟩
      intro x
      by_cases hkx_top : k x = ⊤
      · have : μ * k x = ⊤ := by
          simpa [hkx_top] using (EReal.mul_top_of_pos hμpos)
        simp [this]
      · by_cases hkx0 : k x = 0
        · have hdot0 : ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ 0 := hdot_le_zero x hkx0
          simpa [hkx0] using hdot0
        · have hkx_ne_bot : k x ≠ (⊥ : EReal) := IsGauge.ne_bot hk x
          set t : ℝ := (k x).toReal
          have hkx_eq : (t : EReal) = k x := by
            simpa [t] using (EReal.coe_toReal (x := k x) hkx_top hkx_ne_bot)
          have hkx_pos : (0 : EReal) < k x :=
            lt_of_le_of_ne (hk.2.1 x) (Ne.symm hkx0)
          have htpos : 0 < t := by
            have : (0 : EReal) < (t : EReal) := by simpa [hkx_eq] using hkx_pos
            exact (EReal.coe_pos).1 this
          set y : Fin n → ℝ := (t⁻¹) • x
          have hyC : y ∈ C := by
            have hhom : k y = ((t⁻¹ : ℝ) : EReal) * k x :=
              hk.2.2.1 x t⁻¹ (le_of_lt (inv_pos.mpr htpos))
            have hmul :
                ((t⁻¹ : ℝ) : EReal) * k x = (1 : EReal) := by
              have htne : t ≠ 0 := ne_of_gt htpos
              calc
                ((t⁻¹ : ℝ) : EReal) * k x =
                    ((t⁻¹ : ℝ) : EReal) * (t : EReal) := by simp [hkx_eq]
                _ = ((t⁻¹ * t : ℝ) : EReal) := by
                    simp [EReal.coe_mul]
                _ = (1 : EReal) := by
                    have : (t⁻¹ * t : ℝ) = 1 := by field_simp [htne]
                    simp [this]
            have hle : k y ≤ (1 : EReal) := by simp [hhom, hmul]
            simpa [C, y] using hle
          have hdot_le : ((y ⬝ᵥ xStar : ℝ) : EReal) ≤ μ := hdot_le_mu y hyC
          have hx_eq : x = t • y := by
            have htne : t ≠ 0 := ne_of_gt htpos
            simp [y, smul_smul, htne]
          have hdot_eq :
              ((x ⬝ᵥ xStar : ℝ) : EReal) =
                (t : EReal) * ((y ⬝ᵥ xStar : ℝ) : EReal) := by
            have hdot_eq_real : (x ⬝ᵥ xStar : ℝ) = t * (y ⬝ᵥ xStar : ℝ) := by
              simp [hx_eq, smul_dotProduct]
            simp [hdot_eq_real, EReal.coe_mul]
          have hmul :
              (t : EReal) * ((y ⬝ᵥ xStar : ℝ) : EReal) ≤ (t : EReal) * μ := by
            have ht_nonneg : (0 : EReal) ≤ (t : EReal) := by exact_mod_cast (le_of_lt htpos)
            exact mul_le_mul_of_nonneg_left hdot_le ht_nonneg
          have hmul' :
              (t : EReal) * μ = μ * k x := by
            simp [hkx_eq, EReal.mul_comm]
          simpa [hdot_eq, hmul'] using hmul

/-- The support function of a gauge's unit sublevel equals the polar gauge. -/
lemma supportFunction_unitSublevel_eq_polarGauge_of_isGauge {n : ℕ} {k : (Fin n → ℝ) → EReal}
    (hk : IsGauge k) (xStar : Fin n → ℝ) :
    supportFunctionEReal {x | k x ≤ (1 : EReal)} xStar = polarGauge k xStar := by
  apply le_antisymm
  · exact supportFunction_unitSublevel_le_polarGauge_of_isGauge (k := k) xStar
  · exact polarGauge_le_supportFunction_unitSublevel_of_isGauge hk xStar

/-- The monotone conjugate `g⁺` of a function `g : [0, +∞] → (-∞, +∞]`, defined by
`g⁺(s) = sup_{t ≥ 0} (t * s - g t)`. -/
noncomputable def monotoneConjugateERealNonneg (g : EReal → EReal) (s : EReal) : EReal :=
  sSup ((fun t : EReal => t * s - g t) '' {t : EReal | 0 ≤ t})

/-- The monotone conjugate is monotone in its argument. -/
lemma monotoneConjugateERealNonneg_mono {g : EReal → EReal} :
    Monotone (monotoneConjugateERealNonneg g) := by
  intro s1 s2 hs
  unfold monotoneConjugateERealNonneg
  refine sSup_le ?_
  rintro _ ⟨t, ht, rfl⟩
  have hmul : t * s1 ≤ t * s2 := by
    exact mul_le_mul_of_nonneg_left hs ht
  exact (EReal.sub_le_sub hmul le_rfl).trans (le_sSup ⟨t, ht, rfl⟩)

/-- Each affine term lies below the monotone conjugate. -/
lemma term_le_monotoneConjugateERealNonneg {g : EReal → EReal} {s t : EReal} (ht : 0 ≤ t) :
    t * s - g t ≤ monotoneConjugateERealNonneg g s := by
  unfold monotoneConjugateERealNonneg
  exact le_sSup ⟨t, ht, rfl⟩

/-- The monotone conjugate takes value `⊤` at `⊤` once `g` is finite at some positive point. -/
lemma monotoneConjugateERealNonneg_top_of_exists_finite {g : EReal → EReal}
    (hζ : ∃ ζ : ℝ, 0 < ζ ∧ g (ζ : EReal) ≠ ⊤ ∧ g (ζ : EReal) ≠ ⊥) :
    monotoneConjugateERealNonneg g ⊤ = ⊤ := by
  rcases hζ with ⟨ζ, hζpos, hζtop, hζbot⟩
  have hpos : (0 : EReal) ≤ (ζ : EReal) := by exact_mod_cast (le_of_lt hζpos)
  have hmul : (ζ : EReal) * (⊤ : EReal) = (⊤ : EReal) := by
    have hpos' : (0 : EReal) < (ζ : EReal) := by exact_mod_cast hζpos
    simpa using (EReal.mul_top_of_pos hpos')
  have hterm : (ζ : EReal) * (⊤ : EReal) - g (ζ : EReal) = (⊤ : EReal) := by
    simpa [hmul] using (EReal.top_sub hζtop)
  have hle : (⊤ : EReal) ≤ monotoneConjugateERealNonneg g ⊤ := by
    have h :=
      term_le_monotoneConjugateERealNonneg (g := g) (s := (⊤ : EReal)) (t := (ζ : EReal)) hpos
    simpa [hterm] using h
  exact le_antisymm le_top hle

/-- Real cutoffs for the monotone conjugate are bounded above once `g` is finite at some
positive point. -/
lemma bddAbove_cutoff_real_of_monotoneConjugateERealNonneg_of_exists_finite {g : EReal → EReal}
    (hζ : ∃ ζ : ℝ, 0 < ζ ∧ g (ζ : EReal) ≠ ⊤ ∧ g (ζ : EReal) ≠ ⊥) {αr : ℝ} :
    BddAbove
      {s : ℝ | 0 ≤ s ∧ monotoneConjugateERealNonneg g (s : EReal) ≤ (αr : EReal)} := by
  classical
  rcases hζ with ⟨ζ, hζpos, hζtop, hζbot⟩
  let z : ℝ := (g (ζ : EReal)).toReal
  have hz_coe : (z : EReal) = g (ζ : EReal) := by
    simpa [z] using (EReal.coe_toReal (x := g (ζ : EReal)) hζtop hζbot)
  refine ⟨(αr + z) / ζ, ?_⟩
  intro s hs
  rcases hs with ⟨_hs0, hsα⟩
  have hterm :
      (ζ : EReal) * (s : EReal) - g (ζ : EReal) ≤
        monotoneConjugateERealNonneg g (s : EReal) :=
    term_le_monotoneConjugateERealNonneg (g := g) (s := (s : EReal)) (t := (ζ : EReal))
      (by exact_mod_cast (le_of_lt hζpos))
  have hle : (ζ : EReal) * (s : EReal) - g (ζ : EReal) ≤ (αr : EReal) :=
    hterm.trans hsα
  have hle' : ζ * s - z ≤ αr := by
    have hle'' : ((ζ * s - z) : EReal) ≤ (αr : EReal) := by
      simpa [hz_coe] using hle
    exact (EReal.coe_le_coe_iff).1 hle''
  have hineq : s * ζ ≤ αr + z := by
    nlinarith
  have hbound : s ≤ (αr + z) / ζ := by
    exact (le_div_iff₀ hζpos).2 hineq
  exact hbound

/-- The cutoff for a monotone conjugate lies in its real sublevel. -/
lemma csSup_cutoff_mem_sublevel_monotoneConjugateERealNonneg {g : EReal → EReal}
    (hg_top : g ⊤ = ⊤) {αr : ℝ}
    (hA_bdd : BddAbove
      {s : ℝ | 0 ≤ s ∧ monotoneConjugateERealNonneg g (s : EReal) ≤ (αr : EReal)})
    (hA_nonempty :
      ({s : ℝ | 0 ≤ s ∧ monotoneConjugateERealNonneg g (s : EReal) ≤ (αr : EReal)}).Nonempty) :
    0 ≤ (sSup
      {s : ℝ | 0 ≤ s ∧ monotoneConjugateERealNonneg g (s : EReal) ≤ (αr : EReal)} : ℝ) ∧
      monotoneConjugateERealNonneg g
          ((sSup {s : ℝ | 0 ≤ s ∧
            monotoneConjugateERealNonneg g (s : EReal) ≤ (αr : EReal)} : ℝ) : EReal)
        ≤ (αr : EReal) := by
  classical
  let A : Set ℝ :=
    {s : ℝ | 0 ≤ s ∧ monotoneConjugateERealNonneg g (s : EReal) ≤ (αr : EReal)}
  let rα : ℝ := sSup A
  have hr_nonneg : 0 ≤ rα := by
    rcases hA_nonempty with ⟨s, hs⟩
    have hs_le : s ≤ rα := le_csSup hA_bdd (by simpa [A] using hs)
    exact le_trans hs.1 hs_le
  have hA0 : monotoneConjugateERealNonneg g (0 : EReal) ≤ (αr : EReal) := by
    rcases hA_nonempty with ⟨s, hs⟩
    have hs0 : 0 ≤ s := hs.1
    have hmon := monotoneConjugateERealNonneg_mono (g := g)
    have hle : monotoneConjugateERealNonneg g (0 : EReal) ≤
        monotoneConjugateERealNonneg g (s : EReal) := hmon (by exact_mod_cast hs0)
    exact hle.trans hs.2
  have hterm_le :
      ∀ t : EReal, 0 ≤ t → t * (rα : EReal) - g t ≤ (αr : EReal) := by
    intro t ht
    by_cases ht_top : t = ⊤
    · simp [ht_top, hg_top]
    by_cases ht0 : t = 0
    · rcases hA_nonempty with ⟨s0, hs0⟩
      have hterm0 :
          t * (s0 : EReal) - g t ≤ monotoneConjugateERealNonneg g (s0 : EReal) :=
        term_le_monotoneConjugateERealNonneg (g := g) (s := (s0 : EReal)) (t := t) ht
      have hle0 : t * (s0 : EReal) - g t ≤ (αr : EReal) := hterm0.trans hs0.2
      simpa [ht0] using hle0
    have ht_bot : t ≠ (⊥ : EReal) := by
      intro ht_bot
      have ht' := ht
      simp [ht_bot] at ht'
    have ht_pos : (0 : EReal) < t := lt_of_le_of_ne ht (Ne.symm ht0)
    have hgt_bot : g t ≠ (⊥ : EReal) := by
      intro hgt_bot
      have hterm_top : (⊤ : EReal) ≤ monotoneConjugateERealNonneg g (0 : EReal) := by
        have hmem : (⊤ : EReal) ∈
            (fun t : EReal => t * (0 : EReal) - g t) '' {t : EReal | 0 ≤ t} := by
          refine ⟨t, ht, ?_⟩
          simp [hgt_bot]
        exact le_sSup hmem
      have : (⊤ : EReal) ≤ (αr : EReal) := hterm_top.trans hA0
      exact (not_top_le_coe αr) this
    by_cases hgtop : g t = ⊤
    · simp [hgtop]
    set r : ℝ := t.toReal
    set z : ℝ := (g t).toReal
    have ht_eq : (r : EReal) = t := by
      simpa [r] using (EReal.coe_toReal (x := t) ht_top ht_bot)
    have hz_eq : (z : EReal) = g t := by
      simpa [z] using (EReal.coe_toReal (x := g t) hgtop hgt_bot)
    have hr_nonneg : 0 ≤ r := by
      have : (0 : EReal) ≤ (r : EReal) := by simpa [ht_eq] using ht
      exact (EReal.coe_le_coe_iff).1 this
    have hr_ne : r ≠ 0 := by
      intro hr0
      have : (t : EReal) = (0 : EReal) := by
        have : (r : EReal) = (0 : EReal) := by simp [hr0]
        simpa [ht_eq] using this
      exact ht0 (by simpa using this)
    have hr_pos : 0 < r := lt_of_le_of_ne hr_nonneg (by symm; exact hr_ne)
    have hr_le : rα ≤ (αr + z) / r := by
      refine csSup_le hA_nonempty ?_
      intro s hs
      have hterm :
          t * (s : EReal) - g t ≤ (αr : EReal) :=
        (term_le_monotoneConjugateERealNonneg (g := g) (s := (s : EReal)) (t := t) ht).trans hs.2
      have hle' : r * s - z ≤ αr := by
        have hle'' : ((r * s - z) : EReal) ≤ (αr : EReal) := by
          simpa [ht_eq, hz_eq] using hterm
        exact (EReal.coe_le_coe_iff).1 hle''
      have hineq : s * r ≤ αr + z := by
        nlinarith
      have hbound : s ≤ (αr + z) / r := by
        exact (le_div_iff₀ hr_pos).2 hineq
      exact hbound
    have hineq : r * rα ≤ αr + z := by
      have h := (le_div_iff₀ hr_pos).1 hr_le
      simpa [mul_comm] using h
    have hle'' : ((r * rα - z) : EReal) ≤ (αr : EReal) := by
      exact_mod_cast (by nlinarith)
    have hle : t * (rα : EReal) - g t ≤ (αr : EReal) := by
      simpa [ht_eq, hz_eq, mul_comm] using hle''
    exact hle
  have hsup :
      monotoneConjugateERealNonneg g ((rα : ℝ) : EReal) ≤ (αr : EReal) := by
    unfold monotoneConjugateERealNonneg
    refine sSup_le ?_
    rintro _ ⟨t, ht, rfl⟩
    exact hterm_le t ht
  exact ⟨hr_nonneg, by simpa [A, rα] using hsup⟩

/-- Sublevels of `g⁺ ∘ kᵒ` are `kᵒ`-sublevels at the real cutoff. -/
lemma sublevel_monotoneConjugate_comp_polarGauge_eq_sublevel_polarGauge_csSup {n : ℕ}
    {k : (Fin n → ℝ) → EReal} {g : EReal → EReal} (hg_top : g ⊤ = ⊤)
    (hζ : ∃ ζ : ℝ, 0 < ζ ∧ g (ζ : EReal) ≠ ⊤ ∧ g (ζ : EReal) ≠ ⊥) {αr : ℝ}
    (hA_bdd : BddAbove
      {s : ℝ | 0 ≤ s ∧ monotoneConjugateERealNonneg g (s : EReal) ≤ (αr : EReal)})
    (hA_nonempty :
      ({s : ℝ | 0 ≤ s ∧ monotoneConjugateERealNonneg g (s : EReal) ≤ (αr : EReal)}).Nonempty) :
    {xStar | monotoneConjugateERealNonneg g (polarGauge k xStar) ≤ (αr : EReal)} =
      {xStar |
        polarGauge k xStar ≤
          ((sSup
              {s : ℝ | 0 ≤ s ∧
                monotoneConjugateERealNonneg g (s : EReal) ≤ (αr : EReal)} : ℝ) : EReal)} := by
  classical
  let gPlus : EReal → EReal := monotoneConjugateERealNonneg g
  let kStar : (Fin n → ℝ) → EReal := polarGauge k
  let A : Set ℝ :=
    {s : ℝ | 0 ≤ s ∧ gPlus (s : EReal) ≤ (αr : EReal)}
  let rα : ℝ := sSup A
  have hkStar : IsGauge kStar := by
    simpa [kStar] using (polarGauge_isGauge (k := k))
  have hcutoff : 0 ≤ rα ∧ gPlus ((rα : ℝ) : EReal) ≤ (αr : EReal) := by
    simpa [A, rα, gPlus] using
      (csSup_cutoff_mem_sublevel_monotoneConjugateERealNonneg (g := g) hg_top hA_bdd hA_nonempty)
  ext xStar
  constructor
  · intro hx
    by_cases hk_top : kStar xStar = ⊤
    · have htop :
          gPlus (kStar xStar) = ⊤ := by
        simpa [kStar, hk_top, gPlus] using
          monotoneConjugateERealNonneg_top_of_exists_finite (g := g) hζ
      have hcontra : (⊤ : EReal) ≤ (αr : EReal) := by
        have hx' := hx
        simp [gPlus, kStar, htop] at hx'
      exfalso
      exact (not_top_le_coe αr) hcontra
    · have hk_bot : kStar xStar ≠ (⊥ : EReal) := IsGauge.ne_bot hkStar xStar
      set s : ℝ := (kStar xStar).toReal
      have hk_eq : (s : EReal) = kStar xStar := by
        simpa [s] using (EReal.coe_toReal (x := kStar xStar) hk_top hk_bot)
      have hs0 : 0 ≤ s := by
        have hk_nonneg : (0 : EReal) ≤ kStar xStar := hkStar.2.1 xStar
        have : (0 : EReal) ≤ (s : EReal) := by simpa [hk_eq] using hk_nonneg
        exact (EReal.coe_le_coe_iff).1 this
      have hs_mem : s ∈ A := by
        refine ⟨hs0, ?_⟩
        simpa [A, gPlus, hk_eq] using hx
      have hs_le : s ≤ rα := le_csSup hA_bdd (by simpa [A] using hs_mem)
      have : (s : EReal) ≤ (rα : EReal) := by exact_mod_cast hs_le
      simpa [kStar, hk_eq, rα] using this
  · intro hx
    have hmon := monotoneConjugateERealNonneg_mono (g := g)
    have hle : gPlus (kStar xStar) ≤ gPlus ((rα : ℝ) : EReal) := hmon hx
    exact hle.trans hcutoff.2

/-- A convex interpolation bound for the monotone conjugate on the nonnegative ray. -/
lemma monotoneConjugateERealNonneg_le_affine {g : EReal → EReal} (hg_top : g ⊤ = ⊤)
    (h0_ne_top : monotoneConjugateERealNonneg g (0 : EReal) ≠ ⊤) {s0 lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlam1 : lam ≤ 1) :
    monotoneConjugateERealNonneg g ((lam * s0 : ℝ) : EReal) ≤
      ((1 - lam : ℝ) : EReal) * monotoneConjugateERealNonneg g (0 : EReal) +
        ((lam : ℝ) : EReal) * monotoneConjugateERealNonneg g (s0 : EReal) := by
  classical
  unfold monotoneConjugateERealNonneg
  refine sSup_le ?_
  rintro _ ⟨t, ht, rfl⟩
  by_cases ht_top : t = ⊤
  · simp [ht_top, hg_top]
  have ht_bot : t ≠ (⊥ : EReal) := by
    intro ht_bot
    have ht' := ht
    simp [ht_bot] at ht'
  have hgt_bot : g t ≠ (⊥ : EReal) := by
    intro hgt_bot
    have hmem :
        (⊤ : EReal) ∈
          (fun u : EReal => u * (0 : EReal) - g u) '' {u : EReal | 0 ≤ u} := by
      refine ⟨t, ht, ?_⟩
      simp [hgt_bot]
    have htop :
        monotoneConjugateERealNonneg g (0 : EReal) = ⊤ := by
      apply le_antisymm le_top
      simpa [monotoneConjugateERealNonneg] using (le_sSup hmem)
    exact h0_ne_top htop
  by_cases hgt_top : g t = ⊤
  · simp [hgt_top]
  set r : ℝ := t.toReal
  set z : ℝ := (g t).toReal
  have ht_eq : (r : EReal) = t := by
    simpa [r] using (EReal.coe_toReal (x := t) ht_top ht_bot)
  have hz_eq : (z : EReal) = g t := by
    simpa [z] using (EReal.coe_toReal (x := g t) hgt_top hgt_bot)
  have hterm0 :
      t * (0 : EReal) - g t ≤ monotoneConjugateERealNonneg g (0 : EReal) :=
    term_le_monotoneConjugateERealNonneg (g := g) (s := (0 : EReal)) (t := t) ht
  have hterm1 :
      t * (s0 : EReal) - g t ≤ monotoneConjugateERealNonneg g (s0 : EReal) :=
    term_le_monotoneConjugateERealNonneg (g := g) (s := (s0 : EReal)) (t := t) ht
  have hterm0' :
      ((r * 0 - z : ℝ) : EReal) ≤ monotoneConjugateERealNonneg g (0 : EReal) := by
    simpa [ht_eq, hz_eq, EReal.coe_mul, EReal.coe_sub] using hterm0
  have hterm1' :
      ((r * s0 - z : ℝ) : EReal) ≤ monotoneConjugateERealNonneg g (s0 : EReal) := by
    simpa [ht_eq, hz_eq, EReal.coe_mul, EReal.coe_sub] using hterm1
  have hlam0' : (0 : EReal) ≤ ((1 - lam : ℝ) : EReal) := by
    exact_mod_cast (sub_nonneg.mpr hlam1)
  have hlam1' : (0 : EReal) ≤ ((lam : ℝ) : EReal) := by
    exact_mod_cast hlam0
  have hmul0 :
      ((1 - lam : ℝ) : EReal) * ((r * 0 - z : ℝ) : EReal) ≤
        ((1 - lam : ℝ) : EReal) * monotoneConjugateERealNonneg g (0 : EReal) :=
    mul_le_mul_of_nonneg_left hterm0' hlam0'
  have hmul1 :
      ((lam : ℝ) : EReal) * ((r * s0 - z : ℝ) : EReal) ≤
        ((lam : ℝ) : EReal) * monotoneConjugateERealNonneg g (s0 : EReal) :=
    mul_le_mul_of_nonneg_left hterm1' hlam1'
  have hsum :
      ((1 - lam : ℝ) : EReal) * ((r * 0 - z : ℝ) : EReal) +
          ((lam : ℝ) : EReal) * ((r * s0 - z : ℝ) : EReal) ≤
        ((1 - lam : ℝ) : EReal) * monotoneConjugateERealNonneg g (0 : EReal) +
          ((lam : ℝ) : EReal) * monotoneConjugateERealNonneg g (s0 : EReal) :=
    add_le_add hmul0 hmul1
  have hreal :
      r * (lam * s0) - z = (1 - lam) * (r * 0 - z) + lam * (r * s0 - z) := by
    ring
  have hlin :
      (r : EReal) * ((lam * s0 : ℝ) : EReal) - (z : EReal) =
        ((1 - lam : ℝ) : EReal) * ((r * 0 - z : ℝ) : EReal) +
          ((lam : ℝ) : EReal) * ((r * s0 - z : ℝ) : EReal) := by
    calc
      (r : EReal) * ((lam * s0 : ℝ) : EReal) - (z : EReal) =
          ((r * (lam * s0) - z : ℝ) : EReal) := by
        simp [EReal.coe_mul, mul_comm]
      _ = (( (1 - lam) * (r * 0 - z) + lam * (r * s0 - z) : ℝ) : EReal) := by
        simp [hreal]
      _ =
          ((1 - lam : ℝ) : EReal) * ((r * 0 - z : ℝ) : EReal) +
            ((lam : ℝ) : EReal) * ((r * s0 - z : ℝ) : EReal) := by
        simp [EReal.coe_mul, EReal.coe_add, sub_eq_add_neg, mul_comm]
  have hlin' :
      t * ((lam * s0 : ℝ) : EReal) - g t =
        ((1 - lam : ℝ) : EReal) * ((r * 0 - z : ℝ) : EReal) +
          ((lam : ℝ) : EReal) * ((r * s0 - z : ℝ) : EReal) := by
    simpa [ht_eq, hz_eq] using hlin
  have hlin'' :
      t * ((lam * s0 : ℝ) : EReal) - g t =
        ((1 - lam : ℝ) : EReal) * ((-z : ℝ) : EReal) +
          ((lam : ℝ) : EReal) * ((r * s0 - z : ℝ) : EReal) := by
    simpa [mul_zero, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hlin'
  have hsum' :
      ((1 - lam : ℝ) : EReal) * ((-z : ℝ) : EReal) +
          ((lam : ℝ) : EReal) * ((r * s0 - z : ℝ) : EReal) ≤
        ((1 - lam : ℝ) : EReal) * monotoneConjugateERealNonneg g (0 : EReal) +
          ((lam : ℝ) : EReal) * monotoneConjugateERealNonneg g (s0 : EReal) := by
    simpa [mul_zero, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsum
  calc
    t * ((lam * s0 : ℝ) : EReal) - g t =
        ((1 - lam : ℝ) : EReal) * ((-z : ℝ) : EReal) +
          ((lam : ℝ) : EReal) * ((r * s0 - z : ℝ) : EReal) := hlin''
    _ ≤ ((1 - lam : ℝ) : EReal) * monotoneConjugateERealNonneg g (0 : EReal) +
          ((lam : ℝ) : EReal) * monotoneConjugateERealNonneg g (s0 : EReal) := hsum'

/-- Cutoffs for the monotone conjugate are either both zero or both positive. -/
lemma cutoff_pos_or_all_zero_of_monotoneConjugateERealNonneg {g : EReal → EReal} (hg_top : g ⊤ = ⊤)
    (h0_ne_bot : monotoneConjugateERealNonneg g (0 : EReal) ≠ ⊥) {αr βr : ℝ}
    (hα0 : monotoneConjugateERealNonneg g (0 : EReal) < (αr : EReal))
    (hβ0 : monotoneConjugateERealNonneg g (0 : EReal) < (βr : EReal))
    (hAα_bdd : BddAbove
      {s : ℝ | 0 ≤ s ∧ monotoneConjugateERealNonneg g (s : EReal) ≤ (αr : EReal)})
    (hAβ_bdd : BddAbove
      {s : ℝ | 0 ≤ s ∧ monotoneConjugateERealNonneg g (s : EReal) ≤ (βr : EReal)}) :
    (sSup {s : ℝ | 0 ≤ s ∧ monotoneConjugateERealNonneg g (s : EReal) ≤ (αr : EReal)} = 0 ∧
        sSup {s : ℝ | 0 ≤ s ∧ monotoneConjugateERealNonneg g (s : EReal) ≤ (βr : EReal)} = 0) ∨
      (0 <
          sSup {s : ℝ | 0 ≤ s ∧ monotoneConjugateERealNonneg g (s : EReal) ≤ (αr : EReal)} ∧
        0 <
          sSup {s : ℝ | 0 ≤ s ∧ monotoneConjugateERealNonneg g (s : EReal) ≤ (βr : EReal)}) := by
  classical
  let gPlus : EReal → EReal := monotoneConjugateERealNonneg g
  let Aα : Set ℝ := {s : ℝ | 0 ≤ s ∧ gPlus (s : EReal) ≤ (αr : EReal)}
  let Aβ : Set ℝ := {s : ℝ | 0 ≤ s ∧ gPlus (s : EReal) ≤ (βr : EReal)}
  let rα : ℝ := sSup Aα
  let rβ : ℝ := sSup Aβ
  by_cases hdeg : ∀ s : ℝ, 0 < s → gPlus (s : EReal) = ⊤
  · have hAα_nonempty : Aα.Nonempty := by
      refine ⟨0, ?_⟩
      refine ⟨by exact le_rfl, ?_⟩
      exact le_of_lt (by simpa [gPlus] using hα0)
    have hAβ_nonempty : Aβ.Nonempty := by
      refine ⟨0, ?_⟩
      refine ⟨by exact le_rfl, ?_⟩
      exact le_of_lt (by simpa [gPlus] using hβ0)
    have hrα_le : rα ≤ 0 := by
      refine csSup_le hAα_nonempty ?_
      intro s hs
      by_contra hs0
      have hspos : 0 < s := lt_of_not_ge hs0
      have htop : gPlus (s : EReal) = ⊤ := hdeg s hspos
      have : (⊤ : EReal) ≤ (αr : EReal) := by simpa [htop] using hs.2
      exact (not_top_le_coe αr) this
    have hrβ_le : rβ ≤ 0 := by
      refine csSup_le hAβ_nonempty ?_
      intro s hs
      by_contra hs0
      have hspos : 0 < s := lt_of_not_ge hs0
      have htop : gPlus (s : EReal) = ⊤ := hdeg s hspos
      have : (⊤ : EReal) ≤ (βr : EReal) := by simpa [htop] using hs.2
      exact (not_top_le_coe βr) this
    have hrα_nonneg : 0 ≤ rα := by
      rcases hAα_nonempty with ⟨s, hs⟩
      have hs_le : s ≤ rα := le_csSup hAα_bdd (by simpa [Aα] using hs)
      exact le_trans hs.1 hs_le
    have hrβ_nonneg : 0 ≤ rβ := by
      rcases hAβ_nonempty with ⟨s, hs⟩
      have hs_le : s ≤ rβ := le_csSup hAβ_bdd (by simpa [Aβ] using hs)
      exact le_trans hs.1 hs_le
    exact Or.inl ⟨le_antisymm hrα_le hrα_nonneg, le_antisymm hrβ_le hrβ_nonneg⟩
  · have h0_ne_top : gPlus (0 : EReal) ≠ ⊤ := by
      intro h0top
      have hα0' := hα0
      simp [gPlus, h0top] at hα0'
    have hmon := monotoneConjugateERealNonneg_mono (g := g)
    obtain ⟨s0, hs0pos, hs0top⟩ : ∃ s0 : ℝ, 0 < s0 ∧ gPlus (s0 : EReal) ≠ ⊤ := by
      by_contra hnone
      apply hdeg
      intro s hs
      by_contra hne
      exact hnone ⟨s, hs, hne⟩
    have hs0bot : gPlus (s0 : EReal) ≠ (⊥ : EReal) := by
      intro hs0bot
      have hle : gPlus (0 : EReal) ≤ gPlus (s0 : EReal) :=
        hmon (by exact_mod_cast (le_of_lt hs0pos))
      have : gPlus (0 : EReal) = (⊥ : EReal) := le_bot_iff.mp (by simpa [hs0bot] using hle)
      exact h0_ne_bot this
    set r0 : ℝ := (gPlus (0 : EReal)).toReal
    set r1 : ℝ := (gPlus (s0 : EReal)).toReal
    have h0coe : (r0 : EReal) = gPlus (0 : EReal) := by
      simpa [r0] using (EReal.coe_toReal (x := gPlus (0 : EReal)) h0_ne_top h0_ne_bot)
    have h1coe : (r1 : EReal) = gPlus (s0 : EReal) := by
      simpa [r1] using (EReal.coe_toReal (x := gPlus (s0 : EReal)) hs0top hs0bot)
    have hr0_lt : r0 < αr := by
      have : (r0 : EReal) < (αr : EReal) := by simpa [h0coe] using hα0
      exact (EReal.coe_lt_coe_iff).1 this
    have hr0_lt' : r0 < βr := by
      have : (r0 : EReal) < (βr : EReal) := by simpa [h0coe] using hβ0
      exact (EReal.coe_lt_coe_iff).1 this
    by_cases hEq : r1 = r0
    · have hsα : gPlus ((s0 / 2 : ℝ) : EReal) ≤ (αr : EReal) := by
        have hle : gPlus ((s0 / 2 : ℝ) : EReal) ≤ gPlus (s0 : EReal) :=
          hmon (by exact_mod_cast (by linarith [hs0pos]))
        have hle' : gPlus (s0 : EReal) ≤ (αr : EReal) := by
          have hlt : (r1 : EReal) < (αr : EReal) := by
            simpa [h1coe, h0coe, hEq] using hα0
          have hle : (r1 : EReal) ≤ (αr : EReal) := le_of_lt hlt
          simpa [h1coe] using hle
        exact hle.trans hle'
      have hsβ : gPlus ((s0 / 2 : ℝ) : EReal) ≤ (βr : EReal) := by
        have hle : gPlus ((s0 / 2 : ℝ) : EReal) ≤ gPlus (s0 : EReal) :=
          hmon (by exact_mod_cast (by linarith [hs0pos]))
        have hle' : gPlus (s0 : EReal) ≤ (βr : EReal) := by
          have hlt : (r1 : EReal) < (βr : EReal) := by
            simpa [h1coe, h0coe, hEq] using hβ0
          have hle : (r1 : EReal) ≤ (βr : EReal) := le_of_lt hlt
          simpa [h1coe] using hle
        exact hle.trans hle'
      have hAα_pos : 0 < rα := by
        have hs_mem : (s0 / 2) ∈ Aα := by
          refine ⟨by linarith [hs0pos], ?_⟩
          simpa [Aα, gPlus] using hsα
        have hs_le : s0 / 2 ≤ rα := le_csSup hAα_bdd (by simpa [Aα] using hs_mem)
        exact lt_of_lt_of_le (by linarith [hs0pos]) hs_le
      have hAβ_pos : 0 < rβ := by
        have hs_mem : (s0 / 2) ∈ Aβ := by
          refine ⟨by linarith [hs0pos], ?_⟩
          simpa [Aβ, gPlus] using hsβ
        have hs_le : s0 / 2 ≤ rβ := le_csSup hAβ_bdd (by simpa [Aβ] using hs_mem)
        exact lt_of_lt_of_le (by linarith [hs0pos]) hs_le
      exact Or.inr ⟨hAα_pos, hAβ_pos⟩
    · have hgt : r0 < r1 := by
        have hle : (r0 : EReal) ≤ (r1 : EReal) := by
          have hle' : gPlus (0 : EReal) ≤ gPlus (s0 : EReal) :=
            hmon (by exact_mod_cast (le_of_lt hs0pos))
          simpa [h0coe, h1coe] using hle'
        have hle' : r0 ≤ r1 := (EReal.coe_le_coe_iff).1 hle
        exact lt_of_le_of_ne hle' (Ne.symm hEq)
      have hpos_of_level :
          ∀ γr : ℝ, gPlus (0 : EReal) < (γr : EReal) →
            ∃ s : ℝ, 0 < s ∧ gPlus (s : EReal) ≤ (γr : EReal) := by
        intro γr hγ0
        have hr0_ltγ : r0 < γr := by
          have : (r0 : EReal) < (γr : EReal) := by simpa [h0coe] using hγ0
          exact (EReal.coe_lt_coe_iff).1 this
        set lam : ℝ := min 1 ((γr - r0) / (2 * (r1 - r0)))
        have hlampos : 0 < lam := by
          have hpos1 : 0 < (1 : ℝ) := by linarith
          have hpos2 : 0 < (γr - r0) / (2 * (r1 - r0)) := by
            have hnum : 0 < γr - r0 := by linarith [hr0_ltγ]
            have hden : 0 < 2 * (r1 - r0) := by linarith [hgt]
            exact div_pos hnum hden
          exact lt_min_iff.mpr ⟨hpos1, hpos2⟩
        have hlam1 : lam ≤ 1 := by
          exact min_le_left _ _
        have hlam0 : 0 ≤ lam := le_of_lt hlampos
        have hconv :
            gPlus ((lam * s0 : ℝ) : EReal) ≤
              ((1 - lam : ℝ) : EReal) * gPlus (0 : EReal) +
                ((lam : ℝ) : EReal) * gPlus (s0 : EReal) := by
          simpa [gPlus] using
            (monotoneConjugateERealNonneg_le_affine (g := g) hg_top h0_ne_top (s0 := s0)
              (lam := lam) hlam0 hlam1)
        have hconv' :
            gPlus ((lam * s0 : ℝ) : EReal) ≤
              (((1 - lam) * r0 + lam * r1 : ℝ) : EReal) := by
          simpa [h0coe, h1coe, EReal.coe_add, EReal.coe_mul, mul_comm, mul_left_comm, mul_assoc]
            using hconv
        have hlamle :
            lam * (r1 - r0) ≤ (γr - r0) / 2 := by
          have hlamle' : lam ≤ (γr - r0) / (2 * (r1 - r0)) := by
            exact min_le_right _ _
          have hden : 0 < r1 - r0 := by linarith [hgt]
          have hmul := (mul_le_mul_of_nonneg_right hlamle' (le_of_lt hden))
          have : (γr - r0) / (2 * (r1 - r0)) * (r1 - r0) = (γr - r0) / 2 := by
            field_simp [ne_of_gt hden]
          simpa [this, mul_comm, mul_left_comm, mul_assoc] using hmul
        have hreal : (1 - lam) * r0 + lam * r1 ≤ γr := by
          have hcalc : r0 + lam * (r1 - r0) ≤ r0 + (γr - r0) / 2 := by
            nlinarith [hlamle]
          have hlt : r0 + (γr - r0) / 2 < γr := by linarith
          have hrewrite : (1 - lam) * r0 + lam * r1 = r0 + lam * (r1 - r0) := by
            ring
          nlinarith [hcalc, hlt, hrewrite]
        have hle : gPlus ((lam * s0 : ℝ) : EReal) ≤ (γr : EReal) :=
          hconv'.trans (by exact_mod_cast hreal)
        exact ⟨lam * s0, by nlinarith [hs0pos, hlampos], hle⟩
      obtain ⟨sα, hsαpos, hsαle⟩ := hpos_of_level αr (by simpa [gPlus] using hα0)
      obtain ⟨sβ, hsβpos, hsβle⟩ := hpos_of_level βr (by simpa [gPlus] using hβ0)
      have hAα_pos : 0 < rα := by
        have hs_mem : sα ∈ Aα := by
          refine ⟨le_of_lt hsαpos, ?_⟩
          simpa [Aα, gPlus] using hsαle
        have hs_le : sα ≤ rα := le_csSup hAα_bdd (by simpa [Aα] using hs_mem)
        exact lt_of_lt_of_le hsαpos hs_le
      have hAβ_pos : 0 < rβ := by
        have hs_mem : sβ ∈ Aβ := by
          refine ⟨le_of_lt hsβpos, ?_⟩
          simpa [Aβ, gPlus] using hsβle
        have hs_le : sβ ≤ rβ := le_csSup hAβ_bdd (by simpa [Aβ] using hs_mem)
        exact lt_of_lt_of_le hsβpos hs_le
      exact Or.inr ⟨hAα_pos, hAβ_pos⟩

/-- Admissible levels covering a `k`-sublevel by a sublevel of `f`. -/
def profileSet {n : ℕ} (f k : (Fin n → ℝ) → EReal) (z : EReal) : Set EReal :=
  {α : EReal | f 0 < α ∧ α < ⊤ ∧ {x | k x ≤ z} ⊆ {x | f x ≤ α}}

/-- The admissible sets are antitone in the threshold. -/
lemma profileSet_mono {n : ℕ} {f k : (Fin n → ℝ) → EReal} {z₁ z₂ : EReal}
    (hz : z₁ ≤ z₂) :
    profileSet f k z₂ ⊆ profileSet f k z₁ := by
  intro α hα
  rcases hα with ⟨h0, htop, hsub⟩
  refine ⟨h0, htop, ?_⟩
  intro x hx
  exact hsub (le_trans hx hz)

/-- The profile infimum is monotone in the threshold. -/
lemma profileFun_mono {n : ℕ} {f k : (Fin n → ℝ) → EReal} :
    Monotone (fun z : EReal => sInf (profileSet f k z)) := by
  intro z₁ z₂ hz
  exact sInf_le_sInf (profileSet_mono (f := f) (k := k) hz)

/-- The profile infimum with a `⊤` guard is monotone. -/
lemma profileFun_with_top_mono {n : ℕ} {f k : (Fin n → ℝ) → EReal} :
    Monotone (fun z : EReal => if z = ⊤ then ⊤ else sInf (profileSet f k z)) := by
  intro z₁ z₂ hz
  by_cases hz₂ : z₂ = ⊤
  · simp [hz₂]
  · have hz₁ : z₁ ≠ ⊤ := by
      intro hz₁
      apply hz₂
      have : (⊤ : EReal) ≤ z₂ := by simpa [hz₁] using hz
      exact (top_le_iff.mp this)
    have hmono := profileFun_mono (f := f) (k := k)
    simpa [hz₁, hz₂] using (hmono hz)

/-- The profile infimum with a `⊤` guard sends `⊤` to `⊤`. -/
lemma profileFun_with_top_top {n : ℕ} {f k : (Fin n → ℝ) → EReal} :
    (fun z : EReal => if z = ⊤ then ⊤ else sInf (profileSet f k z)) ⊤ = ⊤ := by
  simp

/-- A convex function on `t ≥ 0` with closed epigraph cannot take value `⊥` at `0`
if it is finite somewhere on the positive ray. -/
lemma g0_ne_bot_of_convex_closed_and_exists_finite_nonneg {g : EReal → EReal}
    (hg_conv :
      ConvexFunctionOn (S := {t : Fin 1 → ℝ | 0 ≤ t 0}) (fun t => g (t 0 : EReal)))
    (hg_closed :
      IsClosed (epigraph (S := {t : Fin 1 → ℝ | 0 ≤ t 0}) (fun t => g (t 0 : EReal))))
    (hζ : ∃ ζ : ℝ, 0 < ζ ∧ g (ζ : EReal) ≠ ⊤ ∧ g (ζ : EReal) ≠ ⊥) :
    g (0 : EReal) ≠ ⊥ := by
  classical
  by_contra h0
  rcases hζ with ⟨ζ, hζpos, hζtop, hζbot⟩
  let S : Set (Fin 1 → ℝ) := {t | 0 ≤ t 0}
  have hconv : Convex ℝ (epigraph (S := S) (fun t => g (t 0 : EReal))) := by
    simpa using hg_conv
  let tζ : Fin 1 → ℝ := fun _ => ζ
  have htζS : tζ ∈ S := by
    simp [S, hζpos.le, tζ]
  have h0S : (0 : Fin 1 → ℝ) ∈ S := by
    simp [S]
  have h0epi : ∀ μ : ℝ, (0, μ) ∈ epigraph (S := S) (fun t => g (t 0 : EReal)) := by
    intro μ
    refine ⟨h0S, ?_⟩
    simp [h0]
  set r : ℝ := (g (ζ : EReal)).toReal
  have hco : (r : EReal) = g (ζ : EReal) := by
    simpa [r] using (EReal.coe_toReal (x := g (ζ : EReal)) hζtop hζbot)
  have htζepi : (tζ, r) ∈ epigraph (S := S) (fun t => g (t 0 : EReal)) := by
    refine ⟨htζS, ?_⟩
    simp [tζ, hco]
  have hmem :
      ∀ n : ℕ, ∀ μ : ℝ,
        ((fun _ : Fin 1 => ((ζ : ℝ) * ((n : ℝ) / (n + 1)))), μ) ∈
          epigraph (S := S) (fun t => g (t 0 : EReal)) := by
    intro n μ
    set t : ℝ := (n : ℝ) / (n + 1)
    have ht0 : 0 ≤ t := by
      have hn : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
      have hpos : 0 < (n + 1 : ℝ) := by exact_mod_cast (Nat.succ_pos n)
      exact div_nonneg hn (le_of_lt hpos)
    have ht1 : t ≤ 1 := by
      have hpos : 0 < (n + 1 : ℝ) := by exact_mod_cast (Nat.succ_pos n)
      exact (div_le_iff₀ hpos).2 (by nlinarith)
    have hsum : (1 - t) + t = (1 : ℝ) := by ring
    have h1t0 : 0 ≤ (1 - t) := by linarith
    have ht1' : t < 1 := by
      have hpos : 0 < (n + 1 : ℝ) := by exact_mod_cast (Nat.succ_pos n)
      exact (div_lt_iff₀ hpos).2 (by nlinarith)
    have h1t_ne : (1 - t) ≠ 0 := by linarith
    set μ0 : ℝ := (μ - t * r) / (1 - t)
    have hconv_mem :
        (1 - t) • (0, μ0) + t • (tζ, r) ∈
          epigraph (S := S) (fun t => g (t 0 : EReal)) :=
      hconv (h0epi μ0) htζepi h1t0 ht0 hsum
    have hμ : (1 - t) * μ0 + t * r = μ := by
      have h1t_ne' : (1 - t) ≠ 0 := h1t_ne
      calc
        (1 - t) * μ0 + t * r =
            (1 - t) * ((μ - t * r) / (1 - t)) + t * r := by
          simp [μ0]
        _ = μ - t * r + t * r := by
          field_simp [h1t_ne']
        _ = μ := by ring
    have hcomb1 : t • tζ = (fun _ : Fin 1 => (ζ : ℝ) * t) := by
      ext i
      simp [tζ, smul_eq_mul, mul_comm]
    have hcomb2 : (1 - t) * μ0 + t * r = μ := hμ
    simpa [hcomb1, hcomb2] using hconv_mem
  have hle_all : ∀ μ : ℝ, g (ζ : EReal) ≤ (μ : EReal) := by
    intro μ
    have htendsto_real :
        Tendsto (fun n : ℕ => (ζ : ℝ) * ((n : ℝ) / (n + 1)))
          atTop (𝓝 ((ζ : ℝ) * (1 : ℝ))) := by
      have ht :
          Tendsto (fun n : ℕ => (n : ℝ) / (n + 1)) atTop (𝓝 (1 : ℝ)) := by
        simpa using (tendsto_natCast_div_add_atTop (𝕜 := ℝ) (x := (1 : ℝ)))
      exact (tendsto_const_nhds.mul ht)
    have hlim :
        Tendsto
          (fun n : ℕ =>
            ((fun _ : Fin 1 => (ζ : ℝ) * ((n : ℝ) / (n + 1))), μ))
          atTop (𝓝 (tζ, μ)) := by
      have hfst : Tendsto
          (fun n : ℕ => (fun _ : Fin 1 => (ζ : ℝ) * ((n : ℝ) / (n + 1))))
          atTop (𝓝 tζ) := by
        refine (tendsto_pi_nhds.2 ?_)
        intro i
        have htendsto_real' :
            Tendsto (fun n : ℕ => (ζ : ℝ) * ((n : ℝ) / (n + 1))) atTop (𝓝 (ζ : ℝ)) := by
          simpa using htendsto_real
        simpa [tζ] using htendsto_real'
      have hsnd : Tendsto (fun _ : ℕ => μ) atTop (𝓝 μ) := tendsto_const_nhds
      have hprod :
          Tendsto
            (fun n : ℕ =>
              ((fun _ : Fin 1 => (ζ : ℝ) * ((n : ℝ) / (n + 1))), μ))
            atTop (𝓝 tζ ×ˢ 𝓝 μ) :=
        (Filter.Tendsto.prodMk hfst hsnd)
      simpa [nhds_prod_eq] using hprod
    have hmem_eventually :
        ∀ᶠ n in atTop,
          (fun n : ℕ =>
            ((fun _ : Fin 1 => (ζ : ℝ) * ((n : ℝ) / (n + 1))), μ)) n ∈
            epigraph (S := S) (fun t => g (t 0 : EReal)) :=
      Eventually.of_forall (fun n => hmem n μ)
    have hlimit :
        (tζ, μ) ∈ epigraph (S := S) (fun t => g (t 0 : EReal)) :=
      hg_closed.mem_of_tendsto hlim hmem_eventually
    exact hlimit.2
  set μ' : ℝ := r - 1
  have hlt : ((μ' : ℝ) : EReal) < g (ζ : EReal) := by
    have hlt' : (μ' : ℝ) < r := by
      simp [μ']
    have hlt'' : ((μ' : ℝ) : EReal) < (r : EReal) := by
      exact (EReal.coe_lt_coe_iff).2 hlt'
    simpa [hco] using hlt''
  have hle : g (ζ : EReal) ≤ (μ' : EReal) := hle_all μ'
  exact (not_lt_of_ge hle) hlt

/-- A monotone function is never `⊥` on nonnegative inputs once `g 0 ≠ ⊥`. -/
lemma monotone_ne_bot_of_nonneg {g : EReal → EReal} (hg_mono : Monotone g)
    (h0 : g (0 : EReal) ≠ ⊥) :
    ∀ t : EReal, (0 : EReal) ≤ t → g t ≠ ⊥ := by
  intro t ht hbot
  have hle : g (0 : EReal) ≤ g t := hg_mono ht
  have : g (0 : EReal) ≤ (⊥ : EReal) := by simpa [hbot] using hle
  exact h0 (le_bot_iff.mp this)

/-- Sublevels of `g ∘ k` are contained in the `k`-sublevel at the `sSup` cutoff. -/
lemma sublevel_comp_subset_sublevel_gauge_sSup {n : ℕ} {k : (Fin n → ℝ) → EReal}
    {g : EReal → EReal} (hk : IsGauge k) {α : EReal} :
    {x | g (k x) ≤ α} ⊆ {x | k x ≤ sSup {t : EReal | 0 ≤ t ∧ g t ≤ α}} := by
  intro x hx
  have hkx_nonneg : (0 : EReal) ≤ k x := hk.2.1 x
  have hxmem : k x ∈ {t : EReal | 0 ≤ t ∧ g t ≤ α} := ⟨hkx_nonneg, hx⟩
  exact le_sSup hxmem

/-- Closed epigraph on the nonnegative ray gives lower semicontinuity on that ray. -/
lemma lscOn_g_nonneg_of_isClosed_epigraph {g : EReal → EReal}
    (hg_closed :
      IsClosed
        (epigraph (S := {t : Fin 1 → ℝ | 0 ≤ t 0}) (fun t => g (t 0 : EReal)))) :
    LowerSemicontinuousOn (fun t : Fin 1 → ℝ => g (t 0 : EReal)) {t : Fin 1 → ℝ | 0 ≤ t 0} := by
  classical
  let S : Set (Fin 1 → ℝ) := {t | 0 ≤ t 0}
  let fS : (Fin 1 → ℝ) → EReal := fun t => if 0 ≤ t 0 then g (t 0 : EReal) else ⊤
  have hset :
      epigraph (S := (Set.univ : Set (Fin 1 → ℝ))) fS =
        epigraph (S := S) (fun t => g (t 0 : EReal)) := by
    ext p
    constructor
    · intro hp
      have hp' : fS p.1 ≤ (p.2 : EReal) := hp.2
      by_cases h0 : 0 ≤ p.1 0
      · have hp'' := hp'
        simp [fS, h0] at hp''
        have hle : g (p.1 0 : EReal) ≤ (p.2 : EReal) := hp''
        exact ⟨by simpa [S] using h0, hle⟩
      · have htop : (⊤ : EReal) ≤ (p.2 : EReal) := by
          have hp'' := hp'
          simp [fS, h0] at hp''
        exact (not_top_le_coe p.2 htop).elim
    · rintro ⟨hp0, hpμ⟩
      have h0 : 0 ≤ p.1 0 := by simpa [S] using hp0
      refine ⟨by exact Set.mem_univ (α := Fin 1 → ℝ) p.1, ?_⟩
      simpa [fS, h0] using hpμ
  have hclosed_univ :
      IsClosed (epigraph (S := (Set.univ : Set (Fin 1 → ℝ))) fS) := by
    simpa [hset, S] using hg_closed
  have hsub : ∀ α : ℝ, IsClosed {x | fS x ≤ (α : EReal)} :=
    (lowerSemicontinuous_iff_closed_sublevel_iff_closed_epigraph (f := fS)).2.mpr hclosed_univ
  have hls : LowerSemicontinuous fS :=
    (lowerSemicontinuous_iff_closed_sublevel (f := fS)).2 hsub
  have hls_on : LowerSemicontinuousOn fS S := hls.lowerSemicontinuousOn S
  have hEq : Set.EqOn fS (fun t => g (t 0 : EReal)) S := by
    intro t ht
    have ht' : 0 ≤ t 0 := by simpa [S] using ht
    simp [fS, ht']
  intro t ht
  have ht' : LowerSemicontinuousWithinAt fS S t := hls_on t ht
  have hEqEv :
      fS =ᶠ[𝓝[S] t] fun t => g (t 0 : EReal) :=
    hEq.eventuallyEq_nhdsWithin
  exact ht'.congr_of_eventuallyEq ht hEqEv

/-- Lower semicontinuity on `t ≥ 0` makes the `sSup` cutoff attainable. -/
lemma g_le_csSup_of_lscOn_nonneg {g : EReal → EReal}
    (hlsc :
      LowerSemicontinuousOn (fun t : Fin 1 → ℝ => g (t 0 : EReal)) {t : Fin 1 → ℝ | 0 ≤ t 0})
    {α : ℝ} (h0α : g (0 : EReal) ≤ (α : EReal))
    (hA_bdd : BddAbove {s : ℝ | 0 ≤ s ∧ g (s : EReal) ≤ (α : EReal)}) :
    g ((sSup {s : ℝ | 0 ≤ s ∧ g (s : EReal) ≤ (α : EReal)} : ℝ) : EReal) ≤ (α : EReal) := by
  classical
  let A : Set ℝ := {s : ℝ | 0 ≤ s ∧ g (s : EReal) ≤ (α : EReal)}
  have hA_nonempty : A.Nonempty := by
    refine ⟨0, ?_⟩
    exact ⟨le_rfl, h0α⟩
  let S : Set (Fin 1 → ℝ) := {t | 0 ≤ t 0}
  let f : (Fin 1 → ℝ) → EReal := fun t => g (t 0 : EReal)
  have hSclosed : IsClosed S := by
    have hcont' : Continuous fun t : Fin 1 → ℝ => t 0 := continuous_apply (0 : Fin 1)
    simpa [S, Set.preimage] using (isClosed_Ici (a := (0 : ℝ))).preimage hcont'
  have hclosedB : IsClosed (S ∩ f ⁻¹' Set.Iic (α : EReal)) := by
    rcases
        (lowerSemicontinuousOn_iff_preimage_Iic (f := f) (s := S)).1 hlsc (α : EReal) with
      ⟨v, hv_closed, hEq⟩
    simpa [hEq] using hSclosed.inter hv_closed
  let ι : ℝ → (Fin 1 → ℝ) := fun s _ => s
  have hcontι : Continuous ι := by
    refine continuous_pi ?_
    intro i
    simpa using (continuous_id : Continuous fun s : ℝ => s)
  have hpre :
      A = ι ⁻¹' (S ∩ f ⁻¹' Set.Iic (α : EReal)) := by
    ext s
    constructor
    · intro hs
      rcases hs with ⟨hs0, hsα⟩
      have hS : ι s ∈ S := by
        simpa [S, ι] using hs0
      have hF : f (ι s) ≤ (α : EReal) := by
        simpa [f, ι] using hsα
      exact ⟨hS, hF⟩
    · intro hs
      rcases hs with ⟨hsS, hsα⟩
      have hs0 : 0 ≤ s := by
        simpa [S, ι] using hsS
      have hsα' : g (s : EReal) ≤ (α : EReal) := by
        simpa [f, ι] using hsα
      exact ⟨hs0, hsα'⟩
  have hclosedA : IsClosed A := by
    have : IsClosed (ι ⁻¹' (S ∩ f ⁻¹' Set.Iic (α : EReal))) :=
      hclosedB.preimage hcontι
    simpa [hpre] using this
  have hmem : sSup A ∈ A := hclosedA.csSup_mem hA_nonempty hA_bdd
  simpa [A] using hmem.2

end Section15
end Chap03
