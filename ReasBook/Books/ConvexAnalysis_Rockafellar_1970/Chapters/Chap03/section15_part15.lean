/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yijie Wang, Yunxi Duan, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part14

section Chap03
section Section15

open scoped BigOperators
open scoped Pointwise

/-- The ℓᵖ gauge as an `EReal`-valued function. -/
noncomputable def lpNormEReal {n : ℕ} (p : ℝ) (x : Fin n → ℝ) : EReal :=
  ((Real.rpow (∑ i : Fin n, Real.rpow (|x i|) p) (1 / p) : ℝ) : EReal)

/-- `lpNormEReal` is the `phiPow` of the `ℓ^p` sum. -/
lemma lpNormEReal_eq_phiPow_sum_abs_rpow {n : ℕ} (p : ℝ) (x : Fin n → ℝ) :
    lpNormEReal (n := n) p x =
      phiPow (1 / p) ((∑ i : Fin n, Real.rpow (|x i|) p : ℝ) : EReal) := by
  have hsum_nonneg : 0 ≤ ∑ i : Fin n, Real.rpow (|x i|) p := by
    refine Finset.sum_nonneg ?_
    intro i hi
    exact Real.rpow_nonneg (abs_nonneg (x i)) p
  have hmax :
      max (∑ i : Fin n, Real.rpow (|x i|) p) 0 =
        ∑ i : Fin n, Real.rpow (|x i|) p := by
    exact max_eq_left hsum_nonneg
  calc
    lpNormEReal (n := n) p x =
        ((Real.rpow (∑ i : Fin n, Real.rpow (|x i|) p) (1 / p) : ℝ) : EReal) := by
      simp [lpNormEReal]
    _ =
        ((Real.rpow (max (∑ i : Fin n, Real.rpow (|x i|) p) 0) (1 / p) : ℝ) : EReal) := by
      simpa using
        (congrArg (fun t => ((Real.rpow t (1 / p) : ℝ) : EReal)) hmax).symm
    _ = phiPow (1 / p) ((∑ i : Fin n, Real.rpow (|x i|) p : ℝ) : EReal) := by
      simp [phiPow, EReal.toReal_coe]

/-- `lpNormEReal` is even. -/
lemma lpNormEReal_symm {n : ℕ} (p : ℝ) (x : Fin n → ℝ) :
    lpNormEReal (n := n) p (-x) = lpNormEReal (n := n) p x := by
  simp [lpNormEReal]

/-- `lpNormEReal` is strictly positive away from the origin. -/
lemma lpNormEReal_pos_of_ne_zero {n : ℕ} {p : ℝ} (x : Fin n → ℝ) (hx : x ≠ 0) :
    (0 : EReal) < lpNormEReal (n := n) p x := by
  classical
  have hx' : ∃ i : Fin n, x i ≠ 0 := by
    by_contra h
    apply hx
    funext i
    by_contra hxi
    exact h ⟨i, hxi⟩
  rcases hx' with ⟨i, hxi⟩
  have hterm_pos : 0 < Real.rpow (|x i|) p := by
    have habs_pos : 0 < |x i| := abs_pos.mpr hxi
    exact Real.rpow_pos_of_pos habs_pos p
  have hterm_le :
      Real.rpow (|x i|) p ≤ ∑ j : Fin n, Real.rpow (|x j|) p := by
    classical
    have hterm_le' :=
      Finset.single_le_sum (s := (Finset.univ : Finset (Fin n))) (a := i)
        (f := fun j => Real.rpow (|x j|) p)
        (by
          intro j hj
          exact Real.rpow_nonneg (abs_nonneg (x j)) p)
        (by simp)
    simpa using hterm_le'
  have hsum_pos : 0 < ∑ j : Fin n, Real.rpow (|x j|) p := by
    exact lt_of_lt_of_le hterm_pos hterm_le
  have hpow_pos :
      0 < Real.rpow (∑ j : Fin n, Real.rpow (|x j|) p) (1 / p) := by
    exact Real.rpow_pos_of_pos hsum_pos (1 / p)
  have hpow_pos' :
      (0 : EReal) <
        ((Real.rpow (∑ j : Fin n, Real.rpow (|x j|) p) (1 / p) : ℝ) : EReal) := by
    exact_mod_cast hpow_pos
  simpa [lpNormEReal] using hpow_pos'

/-- Closed gauge and polar gauge for power profiles of closed proper convex functions. -/
lemma closedGauge_rpow_mul_and_polar_eq_of_closedProperConvex_posHomogeneous {n : ℕ} {p q : ℝ}
    (hp : 1 < p) (hpq : (1 / p) + (1 / q) = 1) {f : (Fin n → ℝ) → EReal}
    (hf_closed : ClosedConvexFunction f)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hf_hom : PositivelyHomogeneousOfDegree (n := n) p f) :
    let k : (Fin n → ℝ) → EReal := fun x => phiPow (1 / p) (((p : ℝ) : EReal) * f x)
    let kStar : (Fin n → ℝ) → EReal :=
      fun xStar => phiPow (1 / q) (((q : ℝ) : EReal) * fenchelConjugate n f xStar)
    IsClosedGauge k ∧ polarGauge k = kStar := by
  classical
  rcases
      exists_closedGauge_rpow_representation_of_posHomogeneous (n := n) (p := p) hp hf_closed
        hf_proper hf_hom with
    ⟨k0, hk0, hfk0⟩
  have hfenchel :
      ∀ xStar : Fin n → ℝ,
        fenchelConjugate n f xStar =
          ((1 / q : ℝ) : EReal) * phiPow q (polarGauge k0 xStar) := by
    exact
      (fenchelConjugate_rpow_closedGauge_formula_and_posHomogeneous (n := n) (p := p) (q := q) hp
        hpq (f := f) (k := k0) hk0 hfk0).2
  have hk_eq :=
    k_eq_closedGauge_from_cor1531 (n := n) (p := p) (q := q) hp hpq (f := f) (k0 := k0) hk0
      hfk0 hfenchel
  have hk_eq' :
      (fun x => phiPow p⁻¹ (((p : ℝ) : EReal) * f x)) = k0 := by
    simpa [one_div] using hk_eq.1
  have hkStar_eq' :
      (fun xStar =>
          phiPow q⁻¹ (((q : ℝ) : EReal) * fenchelConjugate n f xStar)) = polarGauge k0 := by
    simpa [one_div] using hk_eq.2
  refine ⟨?_, ?_⟩
  · simpa [hk_eq'] using hk0
  · simp [hk_eq', hkStar_eq']

/-- The ℓᵖ gauge is closed and its polar gauge is the ℓᵠ gauge. -/
lemma lpNormEReal_isClosedGauge_and_polarGauge_eq {n : ℕ} {p q : ℝ} (hp : 1 < p)
    (hpq : (1 / p) + (1 / q) = 1) :
    IsClosedGauge (lpNormEReal (n := n) p) ∧
      polarGauge (lpNormEReal (n := n) p) = lpNormEReal (n := n) q := by
  set f : (Fin n → ℝ) → EReal :=
    fun x => (((1 / p : ℝ) * ∑ i : Fin n, Real.rpow (|x i|) p) : EReal) with hf
  have hf_props :
      ClosedConvexFunction f ∧
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f ∧
          PositivelyHomogeneousOfDegree (n := n) p f := by
    simpa [hf] using (sum_abs_rpow_div_closedProperConvex_posHomogeneous (n := n) (p := p) hp)
  have hcor :=
    closedGauge_rpow_mul_and_polar_eq_of_closedProperConvex_posHomogeneous (n := n) (p := p)
      (q := q) hp hpq (f := f) hf_props.1 hf_props.2.1 hf_props.2.2
  have hcor' :
      let k : (Fin n → ℝ) → EReal := fun x => phiPow (1 / p) (((p : ℝ) : EReal) * f x)
      let kStar : (Fin n → ℝ) → EReal :=
        fun xStar => phiPow (1 / q) (((q : ℝ) : EReal) * fenchelConjugate n f xStar)
      IsClosedGauge k ∧ polarGauge k = kStar := by
    simpa using hcor
  rcases hcor' with ⟨hk, hpol⟩
  have hp_pos : 0 < p := by linarith
  have h_one_div_lt : (1 / p : ℝ) < 1 := by
    have h :=
      one_div_lt_one_div_of_lt (a := (1 : ℝ)) (b := p) (ha := by norm_num) (h := hp)
    simpa using h
  have hq_inv_pos : 0 < (1 / q : ℝ) := by
    have hq_inv : (1 / q : ℝ) = 1 - 1 / p := by linarith [hpq]
    have hpos : 0 < (1 - 1 / p : ℝ) := by linarith [h_one_div_lt]
    simpa [hq_inv] using hpos
  have hq_pos : 0 < q := one_div_pos.mp hq_inv_pos
  have hp_ne : p ≠ 0 := ne_of_gt hp_pos
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hk_eq :
      (fun x => phiPow (1 / p) (((p : ℝ) : EReal) * f x)) = lpNormEReal (n := n) p := by
    funext x
    set s : ℝ := ∑ i : Fin n, Real.rpow (|x i|) p
    have hmul_real : p * (p⁻¹ * s) = s := by
      field_simp [hp_ne]
    have hmul :
        ((p : ℝ) : EReal) * (((p⁻¹ : ℝ) : EReal) * ((s : ℝ) : EReal)) = ((s : ℝ) : EReal) := by
      calc
        ((p : ℝ) : EReal) * (((p⁻¹ : ℝ) : EReal) * ((s : ℝ) : EReal)) =
            ((p * (p⁻¹ * s) : ℝ) : EReal) := by
          simp [EReal.coe_mul]
        _ = ((s : ℝ) : EReal) := by
          exact_mod_cast hmul_real
    calc
      phiPow (1 / p) (((p : ℝ) : EReal) * f x) =
          phiPow (1 / p) (((p : ℝ) : EReal) * (((1 / p : ℝ) * s : ℝ) : EReal)) := by
        simp [hf, s, one_div]
      _ = phiPow (1 / p) (((p : ℝ) : EReal) * (((p⁻¹ : ℝ) : EReal) * ((s : ℝ) : EReal))) := by
        simp [EReal.coe_mul, one_div]
      _ = phiPow (1 / p) ((s : ℝ) : EReal) := by
        simp [hmul]
      _ = lpNormEReal (n := n) p x := by
        simpa [s] using (lpNormEReal_eq_phiPow_sum_abs_rpow (n := n) p x).symm
  have hk_eq' :
      (fun x => phiPow p⁻¹ (((p : ℝ) : EReal) * f x)) = lpNormEReal (n := n) p := by
    simpa [one_div] using hk_eq
  have hfenchel :
      fenchelConjugate n f =
        fun xStar => (((1 / q : ℝ) * ∑ i : Fin n, Real.rpow (|xStar i|) q) : EReal) := by
    simpa [hf] using
      (fenchelConjugate_sum_abs_rpow_div_eq_sum_abs_rpow_div (n := n) (p := p) (q := q) hp hpq)
  have hkStar_eq :
      (fun xStar =>
          phiPow (1 / q) (((q : ℝ) : EReal) * fenchelConjugate n f xStar)) =
        lpNormEReal (n := n) q := by
    funext xStar
    set s : ℝ := ∑ i : Fin n, Real.rpow (|xStar i|) q
    have hmul_real : q * (q⁻¹ * s) = s := by
      field_simp [hq_ne]
    have hmul :
        ((q : ℝ) : EReal) * (((q⁻¹ : ℝ) : EReal) * ((s : ℝ) : EReal)) = ((s : ℝ) : EReal) := by
      calc
        ((q : ℝ) : EReal) * (((q⁻¹ : ℝ) : EReal) * ((s : ℝ) : EReal)) =
            ((q * (q⁻¹ * s) : ℝ) : EReal) := by
          simp [EReal.coe_mul]
        _ = ((s : ℝ) : EReal) := by
          exact_mod_cast hmul_real
    calc
      phiPow (1 / q) (((q : ℝ) : EReal) * fenchelConjugate n f xStar) =
          phiPow (1 / q) (((q : ℝ) : EReal) * (((1 / q : ℝ) * s : ℝ) : EReal)) := by
        simp [hfenchel, s, one_div]
      _ = phiPow (1 / q) (((q : ℝ) : EReal) * (((q⁻¹ : ℝ) : EReal) * ((s : ℝ) : EReal))) := by
        simp [EReal.coe_mul, one_div]
      _ = phiPow (1 / q) ((s : ℝ) : EReal) := by
        simp [hmul]
      _ = lpNormEReal (n := n) q xStar := by
        simpa [s] using (lpNormEReal_eq_phiPow_sum_abs_rpow (n := n) q xStar).symm
  have hkStar_eq' :
      (fun xStar =>
          phiPow q⁻¹ (((q : ℝ) : EReal) * fenchelConjugate n f xStar)) =
        lpNormEReal (n := n) q := by
    simpa [one_div] using hkStar_eq
  refine ⟨?_, ?_⟩
  · simpa [hk_eq'] using hk
  · simpa [hk_eq', hkStar_eq'] using hpol

/-- A gauge instance for `lpNormEReal` upgrades to a norm gauge. -/
lemma lpNormEReal_isNormGauge_of_isGauge {n : ℕ} {p : ℝ}
    (hg : IsGauge (lpNormEReal (n := n) p)) : IsNormGauge (lpNormEReal (n := n) p) := by
  refine ⟨hg, ?_, ?_, ?_⟩
  · intro x
    simp [lpNormEReal]
  · intro x
    simpa using (lpNormEReal_symm (n := n) p x)
  · intro x hx
    exact lpNormEReal_pos_of_ne_zero (n := n) (p := p) x hx

/-- A closed gauge is fixed by the polar gauge involution. -/
lemma lpNormEReal_polarGauge_eq_self_of_closedGauge {n : ℕ} {k kPolar : (Fin n → ℝ) → EReal}
    (hk : IsClosedGauge k) (hpol : polarGauge k = kPolar) : polarGauge kPolar = k := by
  have hpol' :
      polarGauge (polarGauge k) = k :=
    polarGauge_involutive_of_isGauge_isClosed_epigraph hk.1 hk.2
  simpa [hpol] using hpol'
end Section15
end Chap03
