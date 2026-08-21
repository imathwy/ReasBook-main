/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yijie Wang, Yunxi Duan, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section15_part10

section Chap03
section Section15

open scoped BigOperators
open scoped Pointwise
open scoped Topology
open Filter

/-- Theorem 15.3 (conjugate formula): If `f(x) = g (k x)` with `k` a closed gauge and `g` as above,
then `f*` is gauge-like and satisfies
`f*(x⋆) = g⁺ (kᵒ x⋆)`, where `g⁺` is `monotoneConjugateERealNonneg g` and `kᵒ` is the polar gauge
`polarGauge k`. -/
theorem fenchelConjugate_eq_monotoneConjugate_polarGauge_of_comp {n : ℕ}
    {f : (Fin n → ℝ) → EReal} {k : (Fin n → ℝ) → EReal} {g : EReal → EReal}
    (hk : IsClosedGauge k) (hfg : f = fun x => g (k x)) (hg_mono : Monotone g)
    (hg_top : g ⊤ = ⊤)
    (hζ : ∃ ζ : ℝ, 0 < ζ ∧ g (ζ : EReal) ≠ ⊤ ∧ g (ζ : EReal) ≠ ⊥) :
    IsGaugeLike (fenchelConjugate n f) ∧
      ∀ xStar : Fin n → ℝ,
        fenchelConjugate n f xStar = monotoneConjugateERealNonneg g (polarGauge k xStar) := by
  classical
  have hformula :
      ∀ xStar : Fin n → ℝ,
        fenchelConjugate n f xStar = monotoneConjugateERealNonneg g (polarGauge k xStar) :=
    fenchelConjugate_eq_monotoneConjugate_polarGauge_of_comp_formula (hk := hk) (hfg := hfg)
      (hg_mono := hg_mono) (hg_top := hg_top) hζ
  have hgl : IsGaugeLike (fenchelConjugate n f) := by
    let gPlus : EReal → EReal := monotoneConjugateERealNonneg g
    let kStar : (Fin n → ℝ) → EReal := polarGauge k
    have hkStar : IsGauge kStar := by
      simpa [kStar] using (polarGauge_isGauge (k := k))
    have hconv : ConvexFunctionOn (S := (Set.univ : Set (Fin n → ℝ))) (fenchelConjugate n f) := by
      have hclosed := fenchelConjugate_closedConvex (n := n) (f := f)
      have hconv' : ConvexFunction (fenchelConjugate n f) := hclosed.2
      simpa [ConvexFunction] using hconv'
    have h0_le :
        ∀ xStar : Fin n → ℝ, fenchelConjugate n f 0 ≤ fenchelConjugate n f xStar := by
      intro xStar
      have hmon := monotoneConjugateERealNonneg_mono (g := g)
      have hk0 : kStar 0 = 0 := by simpa [kStar] using hkStar.2.2.2
      have hk_nonneg : (0 : EReal) ≤ kStar xStar := by
        simpa [kStar] using hkStar.2.1 xStar
      have hle : gPlus (kStar 0) ≤ gPlus (kStar xStar) :=
        hmon (by simpa [hk0] using hk_nonneg)
      simpa [hformula, gPlus, kStar, hk0] using hle
    have hmin : fenchelConjugate n f 0 = sInf (Set.range (fenchelConjugate n f)) := by
      apply le_antisymm
      · refine le_sInf ?_
        intro y hy
        rcases hy with ⟨x, rfl⟩
        exact h0_le x
      · exact sInf_le ⟨0, rfl⟩
    refine ⟨hconv, hmin, ?_⟩
    intro α β hα0 hαtop hβ0 hβtop
    have hαtop' : α ≠ ⊤ := ne_of_lt hαtop
    have hβtop' : β ≠ ⊤ := ne_of_lt hβtop
    have hαbot : α ≠ ⊥ := by
      intro hbot
      have hα0' := hα0
      simp [hbot] at hα0'
    have hβbot : β ≠ ⊥ := by
      intro hbot
      have hβ0' := hβ0
      simp [hbot] at hβ0'
    set αr : ℝ := α.toReal
    set βr : ℝ := β.toReal
    have hαcoe : (αr : EReal) = α := by
      simpa [αr] using (EReal.coe_toReal (x := α) hαtop' hαbot)
    have hβcoe : (βr : EReal) = β := by
      simpa [βr] using (EReal.coe_toReal (x := β) hβtop' hβbot)
    have hα0' : gPlus (0 : EReal) < α := by
      have hk0 : kStar 0 = 0 := by simpa [kStar] using hkStar.2.2.2
      simpa [hformula, gPlus, kStar, hk0] using hα0
    have hβ0' : gPlus (0 : EReal) < β := by
      have hk0 : kStar 0 = 0 := by simpa [kStar] using hkStar.2.2.2
      simpa [hformula, gPlus, kStar, hk0] using hβ0
    let Aα : Set ℝ := {s : ℝ | 0 ≤ s ∧ gPlus (s : EReal) ≤ (αr : EReal)}
    let Aβ : Set ℝ := {s : ℝ | 0 ≤ s ∧ gPlus (s : EReal) ≤ (βr : EReal)}
    let rα : ℝ := sSup Aα
    let rβ : ℝ := sSup Aβ
    have hAα_bdd : BddAbove Aα := by
      simpa [Aα, gPlus] using
        (bddAbove_cutoff_real_of_monotoneConjugateERealNonneg_of_exists_finite (g := g) hζ
          (αr := αr))
    have hAβ_bdd : BddAbove Aβ := by
      simpa [Aβ, gPlus] using
        (bddAbove_cutoff_real_of_monotoneConjugateERealNonneg_of_exists_finite (g := g) hζ
          (αr := βr))
    have hAα_nonempty : Aα.Nonempty := by
      refine ⟨0, ?_⟩
      refine ⟨by simp, ?_⟩
      exact le_of_lt (by simpa [hαcoe] using hα0')
    have hAβ_nonempty : Aβ.Nonempty := by
      refine ⟨0, ?_⟩
      refine ⟨by simp, ?_⟩
      exact le_of_lt (by simpa [hβcoe] using hβ0')
    have hsubα :
        {xStar | gPlus (kStar xStar) ≤ (αr : EReal)} =
          {xStar | kStar xStar ≤ (rα : EReal)} := by
      simpa [Aα, rα, gPlus, kStar] using
        (sublevel_monotoneConjugate_comp_polarGauge_eq_sublevel_polarGauge_csSup (k := k) (g := g)
          hg_top hζ (αr := αr) hAα_bdd hAα_nonempty)
    have hsubβ :
        {xStar | gPlus (kStar xStar) ≤ (βr : EReal)} =
          {xStar | kStar xStar ≤ (rβ : EReal)} := by
      simpa [Aβ, rβ, gPlus, kStar] using
        (sublevel_monotoneConjugate_comp_polarGauge_eq_sublevel_polarGauge_csSup (k := k) (g := g)
          hg_top hζ (αr := βr) hAβ_bdd hAβ_nonempty)
    have h0_ne_bot : gPlus (0 : EReal) ≠ ⊥ := by
      rcases hζ with ⟨ζ, hζpos, hζtop, hζbot⟩
      have hterm :
          (ζ : EReal) * (0 : EReal) - g (ζ : EReal) ≤ gPlus (0 : EReal) :=
        term_le_monotoneConjugateERealNonneg (g := g) (s := (0 : EReal)) (t := (ζ : EReal))
          (by exact_mod_cast (le_of_lt hζpos))
      have hterm' : (- g (ζ : EReal)) ≤ gPlus (0 : EReal) := by simpa using hterm
      intro hbot
      have hle : (- g (ζ : EReal)) ≤ (⊥ : EReal) := by simpa [hbot] using hterm'
      have hbot' : - g (ζ : EReal) = (⊥ : EReal) := le_bot_iff.mp hle
      have hco : ((g (ζ : EReal)).toReal : EReal) = g (ζ : EReal) := by
        simpa using (EReal.coe_toReal (x := g (ζ : EReal)) hζtop hζbot)
      have hneg_coe : ((- (g (ζ : EReal)).toReal : ℝ) : EReal) = - g (ζ : EReal) := by
        simp [hco]
      have hne : ((- (g (ζ : EReal)).toReal : ℝ) : EReal) ≠ (⊥ : EReal) := by
        simp
      exact hne (by simpa [hneg_coe] using hbot')
    have hcutoff :
        (rα = 0 ∧ rβ = 0) ∨ (0 < rα ∧ 0 < rβ) := by
      simpa [Aα, Aβ, rα, rβ, gPlus] using
        (cutoff_pos_or_all_zero_of_monotoneConjugateERealNonneg (g := g) hg_top h0_ne_bot
          (αr := αr) (βr := βr) (by simpa [gPlus, hαcoe] using hα0')
          (by simpa [gPlus, hβcoe] using hβ0')
          hAα_bdd hAβ_bdd)
    rcases hcutoff with ⟨hαz, hβz⟩ | ⟨hαpos, hβpos⟩
    · refine ⟨1, by norm_num, ?_⟩
      have hsubα' :
          {xStar | fenchelConjugate n f xStar ≤ α} =
            {xStar | kStar xStar ≤ (0 : EReal)} := by
        have hsubα'' :
            {xStar | gPlus (kStar xStar) ≤ α} =
              {xStar | kStar xStar ≤ (0 : EReal)} := by
          simpa [hαcoe, hαz] using hsubα
        simpa [hformula, gPlus, kStar] using hsubα''
      have hsubβ' :
          {xStar | fenchelConjugate n f xStar ≤ β} =
            {xStar | kStar xStar ≤ (0 : EReal)} := by
        have hsubβ'' :
            {xStar | gPlus (kStar xStar) ≤ β} =
              {xStar | kStar xStar ≤ (0 : EReal)} := by
          simpa [hβcoe, hβz] using hsubβ
        simpa [hformula, gPlus, kStar] using hsubβ''
      calc
        {xStar | fenchelConjugate n f xStar ≤ α} =
            {xStar | kStar xStar ≤ (0 : EReal)} := hsubα'
        _ = (1 : ℝ) • {xStar | kStar xStar ≤ (0 : EReal)} := by
          simp
        _ = (1 : ℝ) • {xStar | fenchelConjugate n f xStar ≤ β} := by
          simp [hsubβ']
    · refine ⟨rα / rβ, by exact div_pos hαpos hβpos, ?_⟩
      have hsubα' :
          {xStar | fenchelConjugate n f xStar ≤ α} =
            {xStar | kStar xStar ≤ (rα : EReal)} := by
        have hsubα'' :
            {xStar | gPlus (kStar xStar) ≤ α} =
              {xStar | kStar xStar ≤ (rα : EReal)} := by
          simpa [hαcoe] using hsubα
        simpa [hformula, gPlus, kStar] using hsubα''
      have hsubβ' :
          {xStar | fenchelConjugate n f xStar ≤ β} =
            {xStar | kStar xStar ≤ (rβ : EReal)} := by
        have hsubβ'' :
            {xStar | gPlus (kStar xStar) ≤ β} =
              {xStar | kStar xStar ≤ (rβ : EReal)} := by
          simpa [hβcoe] using hsubβ
        simpa [hformula, gPlus, kStar] using hsubβ''
      have hαsmul :
          {xStar | kStar xStar ≤ (rα : EReal)} =
            rα • {xStar | kStar xStar ≤ (1 : EReal)} :=
        sublevel_eq_smul_sublevel_one_of_isGauge hkStar hαpos
      have hβsmul :
          {xStar | kStar xStar ≤ (rβ : EReal)} =
            rβ • {xStar | kStar xStar ≤ (1 : EReal)} :=
        sublevel_eq_smul_sublevel_one_of_isGauge hkStar hβpos
      have hmul : (rα / rβ) * rβ = rα := by
        field_simp [ne_of_gt hβpos]
      calc
        {xStar | fenchelConjugate n f xStar ≤ α}
            = rα • {xStar | kStar xStar ≤ (1 : EReal)} := by simpa [hsubα'] using hαsmul
        _ = (rα / rβ) • (rβ • {xStar | kStar xStar ≤ (1 : EReal)}) := by
          simp [smul_smul, hmul]
        _ = (rα / rβ) • {xStar | fenchelConjugate n f xStar ≤ β} := by
          simp [hsubβ', hβsmul, smul_smul]
  exact ⟨hgl, hformula⟩

/-- Text 15.0.21: Let `p > 0`. A function `f : ℝⁿ → (-∞, +∞]` is positively homogeneous of degree
`p` if `f (λ x) = λ^p f x` for all `x` and all `λ > 0`.

In this development, `ℝⁿ` is `Fin n → ℝ`, `(-∞, +∞]` is `EReal`, and `λ^p` is `Real.rpow λ p`. -/
def PositivelyHomogeneousOfDegree {n : ℕ} (p : ℝ) (f : (Fin n → ℝ) → EReal) : Prop :=
  ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 < t → f (t • x) = ((Real.rpow t p : ℝ) : EReal) * f x

/-- Sublevel sets scale under positive homogeneity. -/
lemma sublevel_eq_smul_sublevel_of_posHomogeneous {n : ℕ} {p : ℝ} {f : (Fin n → ℝ) → EReal}
    (hp : 0 < p) (hf_hom : PositivelyHomogeneousOfDegree (n := n) p f) {αr βr : ℝ}
    (hα : 0 < αr) (hβ : 0 < βr) :
    let t : ℝ := Real.rpow (αr / βr) (1 / p)
    {x | f x ≤ (αr : EReal)} = t • {x | f x ≤ (βr : EReal)} := by
  classical
  set t : ℝ := Real.rpow (αr / βr) (1 / p)
  have htpos : 0 < t := Real.rpow_pos_of_pos (div_pos hα hβ) (1 / p)
  have htpos' : 0 ≤ t := le_of_lt htpos
  have hpne : p ≠ 0 := ne_of_gt hp
  have htpow : Real.rpow t p = αr / βr := by
    have hnonneg : 0 ≤ αr / βr := le_of_lt (div_pos hα hβ)
    simpa [t, one_div] using (Real.rpow_inv_rpow (x := αr / βr) (y := p) hnonneg hpne)
  have htinv_pow : Real.rpow t⁻¹ p = βr / αr := by
    calc
      Real.rpow t⁻¹ p = (Real.rpow t p)⁻¹ := by
        simpa using (Real.inv_rpow (x := t) htpos' p)
      _ = (αr / βr)⁻¹ := by rw [htpow]
      _ = βr / αr := by
        field_simp [ne_of_gt hα, ne_of_gt hβ]
  ext x
  constructor
  · intro hx
    refine ⟨(t⁻¹) • x, ?_, ?_⟩
    · have hhom :
        f (t⁻¹ • x) = ((Real.rpow t⁻¹ p : ℝ) : EReal) * f x :=
        hf_hom x t⁻¹ (inv_pos.mpr htpos)
      have hx' : f x ≤ (αr : EReal) := by simpa using hx
      have hmul :
          ((Real.rpow t⁻¹ p : ℝ) : EReal) * f x ≤
            ((Real.rpow t⁻¹ p : ℝ) : EReal) * (αr : EReal) := by
        refine mul_le_mul_of_nonneg_left hx' ?_
        exact_mod_cast (le_of_lt (Real.rpow_pos_of_pos (inv_pos.mpr htpos) p))
      have hmul' : ((Real.rpow t⁻¹ p : ℝ) : EReal) * (αr : EReal) = (βr : EReal) := by
        have hrat : (Real.rpow t⁻¹ p) * αr = βr := by
          calc
            Real.rpow t⁻¹ p * αr = (βr / αr) * αr := by rw [htinv_pow]
            _ = βr := by field_simp [ne_of_gt hα]
        simpa [EReal.coe_mul] using congrArg (fun r : ℝ => (r : EReal)) hrat
      have : f (t⁻¹ • x) ≤ (βr : EReal) := by
        calc
          f (t⁻¹ • x) = ((Real.rpow t⁻¹ p : ℝ) : EReal) * f x := hhom
          _ ≤ ((Real.rpow t⁻¹ p : ℝ) : EReal) * (αr : EReal) := hmul
          _ = (βr : EReal) := hmul'
      exact this
    · have htne : t ≠ 0 := ne_of_gt htpos
      calc
        t • (t⁻¹ • x) = (t * t⁻¹) • x := by simp [smul_smul]
        _ = (1 : ℝ) • x := by simp [htne]
        _ = x := by simp
  · rintro ⟨y, hy, rfl⟩
    have hhom : f (t • y) = ((Real.rpow t p : ℝ) : EReal) * f y :=
      hf_hom y t htpos
    have hy' : f y ≤ (βr : EReal) := by simpa using hy
    have hmul :
        ((Real.rpow t p : ℝ) : EReal) * f y ≤
          ((Real.rpow t p : ℝ) : EReal) * (βr : EReal) := by
      refine mul_le_mul_of_nonneg_left hy' ?_
      exact_mod_cast (le_of_lt (Real.rpow_pos_of_pos htpos p))
    have hmul' : ((Real.rpow t p : ℝ) : EReal) * (βr : EReal) = (αr : EReal) := by
      have hrat : (Real.rpow t p) * βr = αr := by
        calc
          Real.rpow t p * βr = (αr / βr) * βr := by rw [htpow]
          _ = αr := by field_simp [ne_of_gt hβ]
      simpa [EReal.coe_mul] using congrArg (fun r : ℝ => (r : EReal)) hrat
    calc
      f (t • y) = ((Real.rpow t p : ℝ) : EReal) * f y := hhom
      _ ≤ ((Real.rpow t p : ℝ) : EReal) * (βr : EReal) := hmul
      _ = (αr : EReal) := hmul'

/-- Power profile used in the `rpow` representation. -/
noncomputable def phiPow (r : ℝ) : EReal → EReal := fun z =>
  if z = ⊥ then (0 : EReal) else if z = ⊤ then (⊤ : EReal) else (Real.rpow (max z.toReal 0) r : EReal)

/-- Multiplying `⊤` by a positive real yields `⊤` in `EReal`. -/
lemma ereal_coe_mul_top_of_pos {t : ℝ} (ht : 0 < t) :
    ((t : ℝ) : EReal) * (⊤ : EReal) = (⊤ : EReal) := by
  change EReal.mul (t : EReal) (⊤ : EReal) = ⊤
  have htcoe : (t : EReal) = (some (some t) : EReal) := rfl
  simp [EReal.mul, ht, htcoe]

/-- The power profile scales on nonnegative inputs. -/
lemma phiPow_mul_of_nonneg {r : ℝ} {z : EReal} {t : ℝ} (hz : 0 ≤ z) (ht : 0 < t) :
    phiPow r (((t : ℝ) : EReal) * z) =
      ((Real.rpow t r : ℝ) : EReal) * phiPow r z := by
  classical
  by_cases hz_top : z = ⊤
  ·
    have hmul_top : ((t : ℝ) : EReal) * (⊤ : EReal) = (⊤ : EReal) :=
      ereal_coe_mul_top_of_pos ht
    have hmul_top' : ((Real.rpow t r : ℝ) : EReal) * (⊤ : EReal) = (⊤ : EReal) :=
      ereal_coe_mul_top_of_pos (Real.rpow_pos_of_pos ht r)
    have hphi_left : phiPow r (((t : ℝ) : EReal) * (⊤ : EReal)) = (⊤ : EReal) := by
      simp [phiPow, hmul_top]
    have hphi_right : ((Real.rpow t r : ℝ) : EReal) * phiPow r (⊤ : EReal) = (⊤ : EReal) := by
      simpa [phiPow] using hmul_top'
    calc
      phiPow r (((t : ℝ) : EReal) * z) = (⊤ : EReal) := by
        simpa [hz_top] using hphi_left
      _ = ((Real.rpow t r : ℝ) : EReal) * phiPow r z := by
        simpa [hz_top] using hphi_right.symm
  ·
    have hz_ne_bot : z ≠ (⊥ : EReal) := by
      intro hbot
      have hz' := hz
      simp [hbot] at hz'
    have hz_coe : (z.toReal : EReal) = z :=
      EReal.coe_toReal (x := z) hz_top hz_ne_bot
    have hz_nonneg : 0 ≤ z.toReal := by
      have : (0 : EReal) ≤ (z.toReal : EReal) := by simpa [hz_coe] using hz
      exact (EReal.coe_le_coe_iff).1 this
    have hmul_coe : ((t : ℝ) : EReal) * z = ((t * z.toReal : ℝ) : EReal) := by
      calc
        ((t : ℝ) : EReal) * z = ((t : ℝ) : EReal) * (z.toReal : EReal) := by
          simp [hz_coe]
        _ = ((t * z.toReal : ℝ) : EReal) := by
          simp [EReal.coe_mul]
    have hmul_top : ((t * z.toReal : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
    have hmul_bot : ((t * z.toReal : ℝ) : EReal) ≠ ⊥ := EReal.coe_ne_bot _
    have hmul_nonneg : 0 ≤ t * z.toReal := mul_nonneg (le_of_lt ht) hz_nonneg
    have hphi_z : phiPow r z = ((Real.rpow z.toReal r : ℝ) : EReal) := by
      simp [phiPow, hz_top, hz_ne_bot, max_eq_left hz_nonneg]
    have hphi_mul :
        phiPow r (((t : ℝ) : EReal) * z) = ((Real.rpow (t * z.toReal) r : ℝ) : EReal) := by
      have hmul_coe' : ((t : ℝ) : EReal) * z = ((t * z.toReal : ℝ) : EReal) := hmul_coe
      simp [phiPow, hmul_coe', hmul_top, hmul_bot, max_eq_left hmul_nonneg, EReal.toReal_coe,
        -EReal.coe_mul]
    have hmul_rpow :
        Real.rpow (t * z.toReal) r = Real.rpow t r * Real.rpow z.toReal r := by
      simpa using
        (Real.mul_rpow (x := t) (y := z.toReal) (z := r) (hx := le_of_lt ht) (hy := hz_nonneg))
    have hmul_rpow_coe :
        ((Real.rpow (t * z.toReal) r : ℝ) : EReal) =
          ((Real.rpow t r * Real.rpow z.toReal r : ℝ) : EReal) := by
      exact_mod_cast hmul_rpow
    calc
      phiPow r (((t : ℝ) : EReal) * z) = ((Real.rpow (t * z.toReal) r : ℝ) : EReal) := hphi_mul
      _ = ((Real.rpow t r : ℝ) : EReal) * ((Real.rpow z.toReal r : ℝ) : EReal) := by
        calc
          ((Real.rpow (t * z.toReal) r : ℝ) : EReal) =
              ((Real.rpow t r * Real.rpow z.toReal r : ℝ) : EReal) := hmul_rpow_coe
          _ = ((Real.rpow t r : ℝ) : EReal) * ((Real.rpow z.toReal r : ℝ) : EReal) := by
            simp [EReal.coe_mul]
      _ = ((Real.rpow t r : ℝ) : EReal) * phiPow r z := by
        simp [hphi_z]

/-- The power profile is monotone for nonnegative exponents. -/
lemma phiPow_mono {r : ℝ} (hr : 0 ≤ r) : Monotone (phiPow r) := by
  intro a b hab
  by_cases hb_top : b = ⊤
  · simp [phiPow, hb_top]
  by_cases ha_bot : a = ⊥
  ·
    have hnonneg : (0 : EReal) ≤ phiPow r b := by
      by_cases hb_bot : b = ⊥
      · simp [phiPow, hb_bot]
      ·
        have hb_ne_top : b ≠ ⊤ := hb_top
        have hb_ne_bot : b ≠ ⊥ := hb_bot
        have hpow_nonneg : 0 ≤ Real.rpow (max b.toReal 0) r := by
          simpa using (Real.rpow_nonneg (le_max_right _ _) r)
        have hpow_nonneg' :
            (0 : EReal) ≤ ((Real.rpow (max b.toReal 0) r : ℝ) : EReal) := by
          exact_mod_cast hpow_nonneg
        have hphi :
            phiPow r b = ((Real.rpow (max b.toReal 0) r : ℝ) : EReal) := by
          simp [phiPow, hb_ne_top, hb_ne_bot]
        simpa [hphi] using hpow_nonneg'
    simpa [phiPow, ha_bot] using hnonneg
  by_cases ha_top : a = ⊤
  ·
    have : b = ⊤ := by
      have : (⊤ : EReal) ≤ b := by simpa [ha_top] using hab
      exact (top_le_iff.mp this)
    exact (hb_top this).elim
  have hb_bot : b ≠ ⊥ := by
    intro hbot
    have : a = ⊥ := by
      have : a ≤ (⊥ : EReal) := by simpa [hbot] using hab
      exact le_bot_iff.mp this
    exact (ha_bot this).elim
  have ha_ne_top : a ≠ ⊤ := ha_top
  have hb_ne_top : b ≠ ⊤ := hb_top
  have ha_ne_bot : a ≠ ⊥ := ha_bot
  have ha_coe : (a.toReal : EReal) = a :=
    EReal.coe_toReal (x := a) ha_ne_top ha_ne_bot
  have hb_coe : (b.toReal : EReal) = b :=
    EReal.coe_toReal (x := b) hb_ne_top hb_bot
  have hab_real : a.toReal ≤ b.toReal := by
    have : (a.toReal : EReal) ≤ (b.toReal : EReal) := by simpa [ha_coe, hb_coe] using hab
    exact (EReal.coe_le_coe_iff).1 this
  have hmax : max a.toReal 0 ≤ max b.toReal 0 := by
    exact max_le_max hab_real (le_rfl)
  have hpow :
      Real.rpow (max a.toReal 0) r ≤ Real.rpow (max b.toReal 0) r := by
    exact Real.rpow_le_rpow (le_max_right _ _) hmax hr
  have hpow' :
      ((Real.rpow (max a.toReal 0) r : ℝ) : EReal) ≤
        ((Real.rpow (max b.toReal 0) r : ℝ) : EReal) := by
    exact_mod_cast hpow
  have hphi_a :
      phiPow r a = ((Real.rpow (max a.toReal 0) r : ℝ) : EReal) := by
    simp [phiPow, ha_ne_top, ha_ne_bot]
  have hphi_b :
      phiPow r b = ((Real.rpow (max b.toReal 0) r : ℝ) : EReal) := by
    simp [phiPow, hb_ne_top, hb_bot]
  simpa [hphi_a, hphi_b] using hpow'

/-- Basic properties of `gPow z = (1/p) * phiPow p z`. -/
lemma gPow_basic {p : ℝ} (hp : 1 < p) :
    Monotone (fun z : EReal => ((1 / p : ℝ) : EReal) * phiPow p z) ∧
      (fun z : EReal => ((1 / p : ℝ) : EReal) * phiPow p z) ⊤ = ⊤ ∧
        ∃ ζ : ℝ, 0 < ζ ∧
          (fun z : EReal => ((1 / p : ℝ) : EReal) * phiPow p z) (ζ : EReal) ≠ ⊤ ∧
          (fun z : EReal => ((1 / p : ℝ) : EReal) * phiPow p z) (ζ : EReal) ≠ ⊥ := by
  classical
  set gPow : EReal → EReal := fun z => ((1 / p : ℝ) : EReal) * phiPow p z
  have hp0 : 0 < (1 / p : ℝ) := by
    have : 0 < p := by linarith
    exact one_div_pos.mpr this
  have hg_mono : Monotone gPow := by
    have hphi_mono : Monotone (phiPow p) := phiPow_mono (r := p) (by linarith)
    intro a b hab
    have hphi : phiPow p a ≤ phiPow p b := hphi_mono hab
    have hnonneg : (0 : EReal) ≤ ((1 / p : ℝ) : EReal) := by
      exact_mod_cast (le_of_lt hp0)
    simpa [gPow] using (mul_le_mul_of_nonneg_left hphi hnonneg)
  have hg_top : gPow ⊤ = ⊤ := by
    have hmul_top : ((p⁻¹ : ℝ) : EReal) * (⊤ : EReal) = (⊤ : EReal) := by
      simpa [one_div] using (ereal_coe_mul_top_of_pos hp0)
    simp [gPow, phiPow, one_div, hmul_top]
  have hζ :
      ∃ ζ : ℝ, 0 < ζ ∧ gPow (ζ : EReal) ≠ ⊤ ∧ gPow (ζ : EReal) ≠ ⊥ := by
    refine ⟨1, by norm_num, ?_, ?_⟩
    ·
      have h1_ne_top : (1 : EReal) ≠ ⊤ := EReal.coe_ne_top 1
      have h1_ne_bot : (1 : EReal) ≠ ⊥ := EReal.coe_ne_bot 1
      have hval : gPow (1 : EReal) = ((1 / p : ℝ) : EReal) := by
        simp [gPow, phiPow, h1_ne_top, h1_ne_bot]
      intro htop
      have htop' := htop
      simp [hval] at htop'
    ·
      have h1_ne_top : (1 : EReal) ≠ ⊤ := EReal.coe_ne_top 1
      have h1_ne_bot : (1 : EReal) ≠ ⊥ := EReal.coe_ne_bot 1
      have hval : gPow (1 : EReal) = ((1 / p : ℝ) : EReal) := by
        simp [gPow, phiPow, h1_ne_top, h1_ne_bot]
      intro hbot
      have hbot' := hbot
      simp [hval] at hbot'
  refine ⟨hg_mono, ?_, hζ⟩
  simpa [gPow] using hg_top

/-- The monotone conjugate of the power profile `(1/p) * phiPow p` on nonnegative inputs. -/
lemma monotoneConjugateERealNonneg_gPow_eq_one_div_q_phiPow {p q : ℝ} (hp : 1 < p)
    (hpq : (1 / p) + (1 / q) = 1) {s : EReal} (hs : 0 ≤ s) :
    monotoneConjugateERealNonneg (fun z : EReal => ((1 / p : ℝ) : EReal) * phiPow p z) s =
      ((1 / q : ℝ) : EReal) * phiPow q s := by
  classical
  set gPow : EReal → EReal := fun z => ((1 / p : ℝ) : EReal) * phiPow p z
  have hpq' : p.HolderConjugate q := by
    refine (Real.holderConjugate_iff).2 ?_
    refine ⟨hp, ?_⟩
    simpa [one_div] using hpq
  have hq_pos : 0 < q := hpq'.symm.pos
  have hq_pos' : 0 < (1 / q : ℝ) := one_div_pos.mpr hq_pos
  by_cases hst : s = ⊤
  ·
    have hζ :
        ∃ ζ : ℝ, 0 < ζ ∧ gPow (ζ : EReal) ≠ ⊤ ∧ gPow (ζ : EReal) ≠ ⊥ := by
      simpa [gPow] using (gPow_basic (p := p) hp).2.2
    have htop : monotoneConjugateERealNonneg gPow ⊤ = ⊤ :=
      monotoneConjugateERealNonneg_top_of_exists_finite (g := gPow) hζ
    have hmul_top : ((q⁻¹ : ℝ) : EReal) * (⊤ : EReal) = (⊤ : EReal) := by
      simpa [one_div] using (ereal_coe_mul_top_of_pos hq_pos')
    simp [hst, htop, phiPow, hmul_top, one_div]
  ·
    have hs_bot : s ≠ (⊥ : EReal) := by
      intro hbot
      have hs' := hs
      simp [hbot] at hs'
    set sr : ℝ := s.toReal
    have hs_coe : (sr : EReal) = s := by
      simpa [sr] using (EReal.coe_toReal (x := s) hst hs_bot)
    have hs_nonneg : 0 ≤ sr := by
      have : (0 : EReal) ≤ (sr : EReal) := by simpa [hs_coe] using hs
      exact (EReal.coe_le_coe_iff).1 this
    have hphi_s : phiPow q s = ((Real.rpow sr q : ℝ) : EReal) := by
      simp [phiPow, hst, hs_bot, max_eq_left hs_nonneg, sr]
    have hle :
        monotoneConjugateERealNonneg gPow s ≤ ((1 / q : ℝ) : EReal) * phiPow q s := by
      unfold monotoneConjugateERealNonneg
      refine sSup_le ?_
      rintro _ ⟨t, ht, rfl⟩
      by_cases ht_top : t = ⊤
      ·
        have hgtop : gPow t = ⊤ := by
          simpa [gPow, ht_top] using (gPow_basic (p := p) hp).2.1
        have hbot : t * s - gPow t = (⊥ : EReal) := by
          simp [hgtop, sub_eq_add_neg, EReal.neg_top, EReal.add_bot]
        simp [hbot]
      ·
        have ht_bot : t ≠ (⊥ : EReal) := by
          intro hbot
          have ht' := ht
          simp [hbot] at ht'
        set tr : ℝ := t.toReal
        have ht_coe : (tr : EReal) = t := by
          simpa [tr] using (EReal.coe_toReal (x := t) ht_top ht_bot)
        have ht_nonneg : 0 ≤ tr := by
          have : (0 : EReal) ≤ (tr : EReal) := by simpa [ht_coe] using ht
          exact (EReal.coe_le_coe_iff).1 this
        have hphi_t : phiPow p t = ((Real.rpow tr p : ℝ) : EReal) := by
          simp [phiPow, ht_top, ht_bot, max_eq_left ht_nonneg, tr]
        have hterm_le_real :
            tr * sr - (1 / p) * Real.rpow tr p ≤ (1 / q) * Real.rpow sr q := by
          have hyoung :
              tr * sr ≤ (1 / p) * Real.rpow tr p + (1 / q) * Real.rpow sr q := by
            simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
              (Real.young_inequality_of_nonneg (a := tr) (b := sr) ht_nonneg hs_nonneg hpq')
          linarith
        have hterm_le :
            ((tr * sr - (1 / p) * Real.rpow tr p : ℝ) : EReal) ≤
              ((1 / q) * Real.rpow sr q : ℝ) := by
          exact_mod_cast hterm_le_real
        have hterm :
            t * s - gPow t =
              ((tr * sr - (1 / p) * Real.rpow tr p : ℝ) : EReal) := by
          calc
            t * s - gPow t =
                ((tr : ℝ) : EReal) * ((sr : ℝ) : EReal) - ((1 / p : ℝ) : EReal) * phiPow p t := by
              simp [gPow, ht_coe.symm, hs_coe.symm]
            _ = ((tr : ℝ) : EReal) * ((sr : ℝ) : EReal) -
                ((1 / p : ℝ) : EReal) * ((Real.rpow tr p : ℝ) : EReal) := by
              simp [hphi_t]
            _ = ((tr * sr - (1 / p) * Real.rpow tr p : ℝ) : EReal) := by
              simp [EReal.coe_mul, EReal.coe_sub]
        have hterm' :
            t * s - gPow t ≤ ((1 / q : ℝ) : EReal) * phiPow q s := by
          calc
            t * s - gPow t =
                ((tr * sr - (1 / p) * Real.rpow tr p : ℝ) : EReal) := hterm
            _ ≤ ((1 / q) * Real.rpow sr q : ℝ) := hterm_le
            _ = ((1 / q : ℝ) : EReal) * phiPow q s := by
              simp [hphi_s, EReal.coe_mul]
        exact hterm'
    have hge :
        ((1 / q : ℝ) : EReal) * phiPow q s ≤ monotoneConjugateERealNonneg gPow s := by
      set t0 : ℝ := Real.rpow sr (q - 1)
      have ht0_nonneg : 0 ≤ t0 := Real.rpow_nonneg hs_nonneg _
      have ht0_nonneg' : (0 : EReal) ≤ (t0 : EReal) := by exact_mod_cast ht0_nonneg
      have hterm_le :
          (t0 : EReal) * s - gPow (t0 : EReal) ≤ monotoneConjugateERealNonneg gPow s :=
        term_le_monotoneConjugateERealNonneg (g := gPow) (s := s) (t := (t0 : EReal))
          ht0_nonneg'
      have hterm_eq_real :
          t0 * sr - (1 / p) * Real.rpow t0 p = (1 / q) * Real.rpow sr q := by
        by_cases hsr0 : sr = 0
        ·
          have hp_pos : 0 < p := by linarith
          have hpne : p ≠ 0 := ne_of_gt hp_pos
          have hqne : q ≠ 0 := ne_of_gt hq_pos
          have hq1ne : q - 1 ≠ 0 := by
            have : 0 < q - 1 := by linarith [hpq'.symm.lt]
            exact ne_of_gt this
          have ht0 : t0 = 0 := by
            simp [t0, hsr0, Real.zero_rpow hq1ne]
          simp [hsr0, ht0, hpne, hqne, Real.zero_rpow]
        ·
          have hsr_pos : 0 < sr := lt_of_le_of_ne hs_nonneg (Ne.symm hsr0)
          have hmul : t0 * sr = Real.rpow sr q := by
            calc
              t0 * sr = Real.rpow sr (q - 1) * sr := by simp [t0]
              _ = Real.rpow sr (q - 1) * Real.rpow sr 1 := by simp [Real.rpow_one]
              _ = Real.rpow sr ((q - 1) + 1) := by
                simpa using (Real.rpow_add hsr_pos (q - 1) 1).symm
              _ = Real.rpow sr q := by ring_nf
          have hpow : Real.rpow t0 p = Real.rpow sr q := by
            have hconj : (q - 1) * p = q := by
              simpa using hpq'.symm.sub_one_mul_conj
            calc
              Real.rpow t0 p = Real.rpow sr ((q - 1) * p) := by
                simpa [t0] using
                  (Real.rpow_mul (x := sr) (hx := hs_nonneg) (y := q - 1) (z := p)).symm
              _ = Real.rpow sr q := by simp [hconj]
          have hqeq : 1 - 1 / p = 1 / q := by linarith [hpq]
          calc
            t0 * sr - (1 / p) * Real.rpow t0 p =
                Real.rpow sr q - (1 / p) * Real.rpow sr q := by
                  rw [hmul, hpow]
            _ = (1 - 1 / p) * Real.rpow sr q := by ring_nf
            _ = (1 / q) * Real.rpow sr q := by rw [hqeq]
      have hterm_eq :
          (t0 : EReal) * s - gPow (t0 : EReal) = ((1 / q : ℝ) : EReal) * phiPow q s := by
        have hphi_t0 : phiPow p (t0 : EReal) = ((Real.rpow t0 p : ℝ) : EReal) := by
          have ht0_ne_top : (t0 : EReal) ≠ ⊤ := EReal.coe_ne_top _
          have ht0_ne_bot : (t0 : EReal) ≠ ⊥ := EReal.coe_ne_bot _
          simp [phiPow, ht0_ne_top, ht0_ne_bot, max_eq_left ht0_nonneg, EReal.toReal_coe]
        have hterm_eq' :
            ((t0 * sr - (1 / p) * Real.rpow t0 p : ℝ) : EReal) =
              ((1 / q) * Real.rpow sr q : ℝ) := by
          exact_mod_cast hterm_eq_real
        calc
          (t0 : EReal) * s - gPow (t0 : EReal) =
              ((t0 * sr - (1 / p) * Real.rpow t0 p : ℝ) : EReal) := by
            simp [gPow, hs_coe.symm, hphi_t0, EReal.coe_mul, EReal.coe_sub]
          _ = ((1 / q) * Real.rpow sr q : ℝ) := hterm_eq'
          _ = ((1 / q : ℝ) : EReal) * phiPow q s := by
            simp [hphi_s, EReal.coe_mul]
      simpa [hterm_eq] using hterm_le
    exact le_antisymm hle hge

/-- Sublevel sets of a closed gauge match sublevels of a positive-homogeneous function. -/
lemma sublevel_closedGauge_eq_sublevel_f_pow {n : ℕ} {p : ℝ} {f : (Fin n → ℝ) → EReal}
    {k : (Fin n → ℝ) → EReal} (hp : 0 < p)
    (hf_hom : PositivelyHomogeneousOfDegree (n := n) p f) (hk : IsGauge k)
    (hunit : {x | k x ≤ (1 : EReal)} = {x | f x ≤ ((1 / p : ℝ) : EReal)}) :
    ∀ {r : ℝ}, 0 < r →
      {x | k x ≤ (r : EReal)} =
        {x | f x ≤ (((1 / p : ℝ) * Real.rpow r p) : ℝ)} := by
  classical
  intro r hr
  have hk_smul :
      {x | k x ≤ (r : EReal)} = r • {x | k x ≤ (1 : EReal)} :=
    sublevel_eq_smul_sublevel_one_of_isGauge hk hr
  set αr : ℝ := (1 / p) * Real.rpow r p
  set βr : ℝ := 1 / p
  have hβpos : 0 < βr := one_div_pos.mpr hp
  have hαpos : 0 < αr := by
    have hrpow_pos : 0 < Real.rpow r p := Real.rpow_pos_of_pos hr p
    nlinarith [hβpos, hrpow_pos]
  have hsub_f :
      {x | f x ≤ (αr : EReal)} =
        (Real.rpow (αr / βr) (1 / p)) • {x | f x ≤ (βr : EReal)} := by
    simpa [αr, βr] using
      (sublevel_eq_smul_sublevel_of_posHomogeneous (f := f) (p := p) (hp := hp) hf_hom hαpos hβpos)
  have hsub_f' :
      (Real.rpow (αr / βr) (1 / p)) • {x | f x ≤ (βr : EReal)} =
        {x | f x ≤ (αr : EReal)} := by
    simpa using hsub_f.symm
  have hratio : αr / βr = Real.rpow r p := by
    have hβne : βr ≠ 0 := by
      have : (0 : ℝ) < p := hp
      exact one_div_ne_zero (ne_of_gt this)
    calc
      αr / βr = ((1 / p) * Real.rpow r p) / (1 / p) := by simp [αr, βr]
      _ = Real.rpow r p := by field_simp [hβne]
  have ht : Real.rpow (αr / βr) (1 / p) = r := by
    have hr_nonneg : 0 ≤ r := le_of_lt hr
    have hpne : p ≠ 0 := ne_of_gt hp
    have : Real.rpow (Real.rpow r p) (1 / p) = r := by
      simpa [one_div] using (Real.rpow_rpow_inv hr_nonneg hpne)
    simpa [hratio] using this
  calc
    {x | k x ≤ (r : EReal)} = r • {x | k x ≤ (1 : EReal)} := hk_smul
    _ = r • {x | f x ≤ (βr : EReal)} := by
      simpa [βr] using congrArg (fun s => r • s) hunit
    _ = (Real.rpow (αr / βr) (1 / p)) • {x | f x ≤ (βr : EReal)} := by
      rw [ht.symm]
    _ = {x | f x ≤ (αr : EReal)} := hsub_f'
    _ = {x | f x ≤ (((1 / p : ℝ) * Real.rpow r p) : ℝ)} := by
      simp [αr]

/-- A closed proper convex positively homogeneous function is finite at the origin. -/
lemma f0_ne_top_of_closedProperConvex_posHomogeneous {n : ℕ} {p : ℝ}
    {f : (Fin n → ℝ) → EReal} (hp : 1 < p)
    (hf_closed : ClosedConvexFunction f)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hf_hom : PositivelyHomogeneousOfDegree (n := n) p f) :
    f 0 ≠ ⊤ := by
  classical
  rcases hf_proper with ⟨_hconv, hne_epi, hne_bot⟩
  rcases hne_epi with ⟨⟨x0, μ⟩, hx0⟩
  have hx0_le : f x0 ≤ (μ : EReal) := (mem_epigraph_univ_iff (f := f)).1 hx0
  have hx0_ne_top : f x0 ≠ ⊤ := by
    intro htop
    have hx0_le' := hx0_le
    simp [htop] at hx0_le'
  have hx0_ne_bot : f x0 ≠ ⊥ := hne_bot x0 (by simp)
  set r0 : ℝ := (f x0).toReal
  have hr0 : (r0 : EReal) = f x0 := by
    simpa [r0] using (EReal.coe_toReal (x := f x0) hx0_ne_top hx0_ne_bot)
  -- pick a positive scaling so that the value is below 1
  by_cases hr0_nonpos : r0 ≤ 0
  ·
    have h0le1 : f 0 ≤ (1 : EReal) := by
      have hsub_closed : IsClosed {x | f x ≤ (1 : EReal)} :=
        (sublevel_closed_convex_of_closedConvex (f := f) (α := (1 : ℝ)) hf_closed).1
      let seq : ℕ → Fin n → ℝ := fun m => ((1 / (m + 1 : ℕ) : ℝ)) • x0
      have hseq_tendsto : Tendsto seq Filter.atTop (𝓝 (0 : Fin n → ℝ)) := by
        have hscalar :
            Tendsto (fun m : ℕ => (1 / (m + 1 : ℕ) : ℝ)) Filter.atTop (𝓝 (0 : ℝ)) := by
          simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using
            (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
        simpa [seq] using
          (Filter.Tendsto.smul_const (f := fun m : ℕ => (1 / (m + 1 : ℕ) : ℝ)) (a := x0)
            hscalar)
      have hseq_mem : ∀ m, f (seq m) ≤ (1 : EReal) := by
        intro m
        have htpos : 0 < (1 / (m + 1 : ℕ) : ℝ) := by
          exact one_div_pos.mpr (by exact_mod_cast (Nat.succ_pos m))
        have hhom :
            f (seq m) =
              ((Real.rpow (1 / (m + 1 : ℕ) : ℝ) p : ℝ) : EReal) * f x0 := by
          simpa [seq] using hf_hom x0 (1 / (m + 1 : ℕ) : ℝ) htpos
        have hr0_le : (r0 : EReal) ≤ (0 : EReal) := by exact_mod_cast hr0_nonpos
        have hmul_le :
            ((Real.rpow (1 / (m + 1 : ℕ) : ℝ) p : ℝ) : EReal) * (r0 : EReal) ≤
              ((Real.rpow (1 / (m + 1 : ℕ) : ℝ) p : ℝ) : EReal) * (0 : EReal) := by
          refine mul_le_mul_of_nonneg_left hr0_le ?_
          exact_mod_cast (le_of_lt (Real.rpow_pos_of_pos htpos p))
        have hmul_zero :
            ((Real.rpow (1 / (m + 1 : ℕ) : ℝ) p : ℝ) : EReal) * (0 : EReal) = (0 : EReal) := by
          simp
        have hle0 :
            ((Real.rpow (1 / (m + 1 : ℕ) : ℝ) p : ℝ) : EReal) * (r0 : EReal) ≤ (0 : EReal) := by
          simpa [hmul_zero] using hmul_le
        have hle1 :
            ((Real.rpow (1 / (m + 1 : ℕ) : ℝ) p : ℝ) : EReal) * (r0 : EReal) ≤ (1 : EReal) :=
          hle0.trans (by simp)
        simpa [hhom, hr0] using hle1
      have hmem_closure :
          (0 : Fin n → ℝ) ∈ closure {x | f x ≤ (1 : EReal)} := by
        refine mem_closure_of_tendsto hseq_tendsto ?_
        exact eventually_of_forall hseq_mem
      have hmem :
          (0 : Fin n → ℝ) ∈ {x | f x ≤ (1 : EReal)} := by
        simpa [hsub_closed.closure_eq] using hmem_closure
      simpa using hmem
    intro htop
    have : (⊤ : EReal) ≤ (1 : EReal) := by simpa [htop] using h0le1
    exact (not_top_le_coe 1) this
  ·
    have hr0_pos : 0 < r0 := lt_of_not_ge hr0_nonpos
    have hsub_closed : IsClosed {x | f x ≤ (1 : EReal)} :=
      (sublevel_closed_convex_of_closedConvex (f := f) (α := (1 : ℝ)) hf_closed).1
    let t0 : ℝ := 1 / (r0 + 1)
    have ht0_pos : 0 < t0 := by
      have : 0 < r0 + 1 := by linarith
      exact one_div_pos.mpr this
    have ht0_le_one : t0 ≤ 1 := by
      have hpos : (0 : ℝ) < 1 := by norm_num
      have hle : (1 : ℝ) ≤ r0 + 1 := by linarith
      simpa [t0] using (one_div_le_one_div_of_le hpos hle)
    set y0 : Fin n → ℝ := t0 • x0
    have hy0_le1 : f y0 ≤ (1 : EReal) := by
      have hhom :
          f y0 = ((Real.rpow t0 p : ℝ) : EReal) * f x0 := by
        simpa [y0] using hf_hom x0 t0 ht0_pos
      have hpow_le : Real.rpow t0 p ≤ t0 := by
        have hp' : (1 : ℝ) ≤ p := le_of_lt hp
        have := Real.rpow_le_rpow_of_exponent_ge (x := t0) (y := p) (z := 1) ht0_pos ht0_le_one hp'
        simpa using this
      have hmul_le_real :
          Real.rpow t0 p * r0 ≤ t0 * r0 := by
        exact mul_le_mul_of_nonneg_right hpow_le (le_of_lt hr0_pos)
      have hmul_le :
          ((Real.rpow t0 p : ℝ) : EReal) * (r0 : EReal) ≤ ((t0 * r0 : ℝ) : EReal) := by
        exact_mod_cast hmul_le_real
      have ht0_le1' : t0 * r0 ≤ 1 := by
        have : r0 / (r0 + 1) ≤ 1 := by
          have hpos : 0 < r0 + 1 := by linarith
          have hle : r0 ≤ r0 + 1 := by linarith
          simpa [div_eq_mul_inv, mul_comm] using
            (div_le_one hpos).2 hle
        have htr : t0 * r0 = r0 / (r0 + 1) := by
          simp [t0, div_eq_mul_inv, mul_comm]
        simpa [htr] using this
      have hle1 :
          ((t0 * r0 : ℝ) : EReal) ≤ (1 : EReal) := by exact_mod_cast ht0_le1'
      have hle1' :
          ((Real.rpow t0 p : ℝ) : EReal) * (r0 : EReal) ≤ (1 : EReal) := hmul_le.trans hle1
      simpa [hhom, hr0] using hle1'
    let seq : ℕ → Fin n → ℝ := fun m => ((1 / (m + 1 : ℕ) : ℝ)) • y0
    have hseq_tendsto : Tendsto seq Filter.atTop (𝓝 (0 : Fin n → ℝ)) := by
      have hscalar :
          Tendsto (fun m : ℕ => (1 / (m + 1 : ℕ) : ℝ)) Filter.atTop (𝓝 (0 : ℝ)) := by
        simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa [seq] using
        (Filter.Tendsto.smul_const (f := fun m : ℕ => (1 / (m + 1 : ℕ) : ℝ)) (a := y0)
          hscalar)
    have hseq_mem : ∀ m, f (seq m) ≤ (1 : EReal) := by
      intro m
      have htpos : 0 < (1 / (m + 1 : ℕ) : ℝ) := by
        exact one_div_pos.mpr (by exact_mod_cast (Nat.succ_pos m))
      have hhom :
          f (seq m) =
            ((Real.rpow (1 / (m + 1 : ℕ) : ℝ) p : ℝ) : EReal) * f y0 := by
        simpa [seq] using hf_hom y0 (1 / (m + 1 : ℕ) : ℝ) htpos
      have hpow_le_one :
          ((Real.rpow (1 / (m + 1 : ℕ) : ℝ) p : ℝ) : EReal) ≤ (1 : EReal) := by
        have ht0 : 0 ≤ (1 / (m + 1 : ℕ) : ℝ) := by
          exact le_of_lt (one_div_pos.mpr (by exact_mod_cast (Nat.succ_pos m)))
        have ht1 : (1 / (m + 1 : ℕ) : ℝ) ≤ 1 := by
          simpa [one_div] using (Nat.cast_inv_le_one (m + 1))
        have hp' : 0 ≤ p := by linarith
        exact_mod_cast (Real.rpow_le_one ht0 ht1 hp')
      by_cases hy0_nonpos : f y0 ≤ (0 : EReal)
      ·
        have hmul_le :
            ((Real.rpow (1 / (m + 1 : ℕ) : ℝ) p : ℝ) : EReal) * f y0 ≤
              ((Real.rpow (1 / (m + 1 : ℕ) : ℝ) p : ℝ) : EReal) * (0 : EReal) := by
          refine mul_le_mul_of_nonneg_left hy0_nonpos ?_
          exact_mod_cast (le_of_lt (Real.rpow_pos_of_pos htpos p))
        have hmul_zero :
            ((Real.rpow (1 / (m + 1 : ℕ) : ℝ) p : ℝ) : EReal) * (0 : EReal) = (0 : EReal) := by
          simp
        have hle0 :
            ((Real.rpow (1 / (m + 1 : ℕ) : ℝ) p : ℝ) : EReal) * f y0 ≤ (0 : EReal) := by
          simpa [hmul_zero] using hmul_le
        have hle1 :
            ((Real.rpow (1 / (m + 1 : ℕ) : ℝ) p : ℝ) : EReal) * f y0 ≤ (1 : EReal) :=
          hle0.trans (by simp)
        simpa [hhom] using hle1
      ·
        have hy0_pos : (0 : EReal) < f y0 := lt_of_not_ge hy0_nonpos
        have hmul_le :
            ((Real.rpow (1 / (m + 1 : ℕ) : ℝ) p : ℝ) : EReal) * f y0 ≤
              (1 : EReal) * f y0 := by
          exact mul_le_mul_of_nonneg_right hpow_le_one (le_of_lt hy0_pos)
        have hmul_le' :
            ((Real.rpow (1 / (m + 1 : ℕ) : ℝ) p : ℝ) : EReal) * f y0 ≤ f y0 := by
          simpa using (by simpa using hmul_le)
        have hle1 :
            ((Real.rpow (1 / (m + 1 : ℕ) : ℝ) p : ℝ) : EReal) * f y0 ≤ (1 : EReal) :=
          hmul_le'.trans hy0_le1
        simpa [hhom] using hle1
    have hmem_closure :
        (0 : Fin n → ℝ) ∈ closure {x | f x ≤ (1 : EReal)} := by
      refine mem_closure_of_tendsto hseq_tendsto ?_
      exact eventually_of_forall hseq_mem
    have hmem :
        (0 : Fin n → ℝ) ∈ {x | f x ≤ (1 : EReal)} := by
      simpa [hsub_closed.closure_eq] using hmem_closure
    have h0le1 : f 0 ≤ (1 : EReal) := by simpa using hmem
    intro htop
    have : (⊤ : EReal) ≤ (1 : EReal) := by simpa [htop] using h0le1
    exact (not_top_le_coe 1) this

/-- A closed proper convex positively homogeneous function is gauge-like. -/
lemma isGaugeLike_of_closedProperConvex_posHomogeneous {n : ℕ} {p : ℝ}
    {f : (Fin n → ℝ) → EReal} (hp : 1 < p)
    (hf_closed : ClosedConvexFunction f)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hf_hom : PositivelyHomogeneousOfDegree (n := n) p f) :
    IsGaugeLike f := by
  classical
  have hconv : ConvexFunctionOn (S := (Set.univ : Set (Fin n → ℝ))) f := hf_proper.1
  have h0_ne_top : f 0 ≠ ⊤ :=
    f0_ne_top_of_closedProperConvex_posHomogeneous hp hf_closed hf_proper hf_hom
  have h0_ne_bot : f 0 ≠ ⊥ := by
    rcases hf_proper with ⟨_hconv, _hne_epi, hne_bot⟩
    exact hne_bot 0 (by simp)
  set r0 : ℝ := (f 0).toReal
  have hr0 : (r0 : EReal) = f 0 := by
    simpa [r0] using (EReal.coe_toReal (x := f 0) h0_ne_top h0_ne_bot)
  have hhom0 :
      f 0 = ((Real.rpow 2 p : ℝ) : EReal) * f 0 := by
    simpa using hf_hom (0 : Fin n → ℝ) 2 (by norm_num)
  have hhom0' : (r0 : EReal) = ((Real.rpow 2 p * r0 : ℝ) : EReal) := by
    simpa [hr0, EReal.coe_mul] using hhom0
  have hhom0_real : r0 = Real.rpow 2 p * r0 := by
    exact (EReal.coe_eq_coe_iff).1 hhom0'
  have hpow_gt : 1 < Real.rpow 2 p := by
    have h2 : (1 : ℝ) < 2 := by norm_num
    have hp0 : 0 < p := by linarith
    exact Real.one_lt_rpow h2 hp0
  have hr0_eq : r0 = 0 := by
    have hmul : (Real.rpow 2 p - 1) * r0 = 0 := by
      nlinarith [hhom0_real]
    have hpow_ne : Real.rpow 2 p - 1 ≠ 0 := by linarith [hpow_gt]
    have hzero := mul_eq_zero.mp hmul
    rcases hzero with hzero | hzero
    · exact (hpow_ne hzero).elim
    · exact hzero
  have h0_eq : f 0 = 0 := by
    have : (r0 : EReal) = (0 : EReal) := by simp [hr0_eq]
    simpa [hr0] using this
  have hnotbot : ∀ x ∈ (Set.univ : Set (Fin n → ℝ)), f x ≠ ⊥ := by
    intro x hx
    exact hf_proper.2.2 x (by simp)
  have hineq :=
    (convexFunctionOn_iff_segment_inequality (C := (Set.univ : Set (Fin n → ℝ))) (f := f)
          (hC := by simpa using (convex_univ : Convex ℝ (Set.univ : Set (Fin n → ℝ))))
          (hnotbot := hnotbot)).1 hconv
  have hnonneg : ∀ x : Fin n → ℝ, (0 : EReal) ≤ f x := by
    intro x
    by_cases hx_top : f x = ⊤
    · simp [hx_top]
    · have hx_bot : f x ≠ ⊥ := hf_proper.2.2 x (by simp)
      set t : ℝ := (1 / 2 : ℝ)
      have ht0 : 0 < t := by norm_num
      have ht1 : t < 1 := by norm_num
      have hconv_t :
          f (t • x) ≤ ((1 - t : ℝ) : EReal) * f 0 + ((t : ℝ) : EReal) * f x := by
        simpa [t, add_comm, add_left_comm, add_assoc] using
          hineq 0 (by simp) x (by simp) t ht0 ht1
      have hconv_t' :
          f (t • x) ≤ ((t : ℝ) : EReal) * f x := by
        simpa [h0_eq, t, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hconv_t
      have hhom_t :
          f (t • x) = ((Real.rpow t p : ℝ) : EReal) * f x := by
        simpa [t] using hf_hom x t ht0
      have hineq_t :
          ((Real.rpow t p : ℝ) : EReal) * f x ≤ ((t : ℝ) : EReal) * f x := by
        simpa [hhom_t] using hconv_t'
      set rx : ℝ := (f x).toReal
      have hrx : (rx : EReal) = f x := by
        simpa [rx] using (EReal.coe_toReal (x := f x) hx_top hx_bot)
      have hineq_real : Real.rpow t p * rx ≤ t * rx := by
        have hineq' : (rx : EReal) = f x := hrx
        have hineq'' :
            ((Real.rpow t p * rx : ℝ) : EReal) ≤ ((t * rx : ℝ) : EReal) := by
          simpa [hineq', EReal.coe_mul] using hineq_t
        exact (EReal.coe_le_coe_iff).1 hineq''
      have hpow_lt : Real.rpow t p < t := by
        exact Real.rpow_lt_self_of_lt_one ht0 ht1 hp
      have hmul_nonneg : 0 ≤ (t - Real.rpow t p) * rx := by
        nlinarith [hineq_real]
      have hpos : 0 < t - Real.rpow t p := by linarith [hpow_lt]
      have hrx_nonneg : 0 ≤ rx := by
        have hcases := (mul_nonneg_iff).1 hmul_nonneg
        rcases hcases with ⟨_, hrx_nonneg⟩ | ⟨hneg, _hrx_nonpos⟩
        · exact hrx_nonneg
        · exact (False.elim (not_lt_of_ge hneg hpos))
      have : (0 : EReal) ≤ (rx : EReal) := by exact_mod_cast hrx_nonneg
      simpa [hrx] using this
  have hmin : f 0 = sInf (Set.range f) := by
    apply le_antisymm
    · refine le_sInf ?_
      intro y hy
      rcases hy with ⟨x, rfl⟩
      simpa [h0_eq] using hnonneg x
    · exact sInf_le ⟨0, rfl⟩
  refine ⟨hconv, hmin, ?_⟩
  intro α β hα0 hαtop hβ0 hβtop
  set αr : ℝ := α.toReal
  set βr : ℝ := β.toReal
  have hαtop' : α ≠ ⊤ := ne_of_lt hαtop
  have hβtop' : β ≠ ⊤ := ne_of_lt hβtop
  have h0ltα : (0 : EReal) < α := by simpa [h0_eq] using hα0
  have h0ltβ : (0 : EReal) < β := by simpa [h0_eq] using hβ0
  have hαbot' : α ≠ ⊥ := by
    intro hbot
    have h0ltα' := h0ltα
    simp [hbot] at h0ltα'
  have hβbot' : β ≠ ⊥ := by
    intro hbot
    have h0ltβ' := h0ltβ
    simp [hbot] at h0ltβ'
  have hαcoe : (αr : EReal) = α := by
    simpa [αr] using (EReal.coe_toReal (x := α) hαtop' hαbot')
  have hβcoe : (βr : EReal) = β := by
    simpa [βr] using (EReal.coe_toReal (x := β) hβtop' hβbot')
  have hαrpos : 0 < αr := by
    have : (0 : EReal) < (αr : EReal) := by simpa [hαcoe] using h0ltα
    exact (EReal.coe_lt_coe_iff).1 this
  have hβrpos : 0 < βr := by
    have : (0 : EReal) < (βr : EReal) := by simpa [hβcoe] using h0ltβ
    exact (EReal.coe_lt_coe_iff).1 this
  set t : ℝ := Real.rpow (αr / βr) (1 / p)
  have htpos : 0 < t := Real.rpow_pos_of_pos (div_pos hαrpos hβrpos) (1 / p)
  have hsub :
      {x | f x ≤ (αr : EReal)} = t • {x | f x ≤ (βr : EReal)} := by
    simpa [t] using
      (sublevel_eq_smul_sublevel_of_posHomogeneous (f := f) (p := p) (hp := by linarith)
        hf_hom hαrpos hβrpos)
  refine ⟨t, htpos, ?_⟩
  simpa [hαcoe, hβcoe] using hsub

end Section15
end Chap03
