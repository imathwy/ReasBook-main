/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yijie Wang, Yunxi Duan, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part1

section Chap03
section Section15

open scoped BigOperators
open scoped Pointwise
open scoped RealInnerProductSpace

/-- Outside the polar cone, the polar gauge of an indicator is `⊤`. -/
lemma polarGauge_erealIndicator_eq_top_of_not_mem_Kpolar {n : ℕ}
    (K : ConvexCone ℝ (Fin n → ℝ)) {xStar : Fin n → ℝ}
    (hxStar : ¬ ∀ x ∈ (K : Set (Fin n → ℝ)), (x ⬝ᵥ xStar : ℝ) ≤ 0) :
    polarGauge (erealIndicator (K : Set (Fin n → ℝ))) xStar = ⊤ := by
  classical
  push_neg at hxStar
  rcases hxStar with ⟨x0, hx0K, hx0pos⟩
  let M : Set EReal :=
    {μ : EReal |
      0 ≤ μ ∧
        ∀ x : Fin n → ℝ,
          ((x ⬝ᵥ xStar : ℝ) : EReal) ≤
            μ * erealIndicator (K : Set (Fin n → ℝ)) x}
  have hMempty : M = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro μ hμ
    have hineq : ((x0 ⬝ᵥ xStar : ℝ) : EReal) ≤ (0 : EReal) := by
      simpa [erealIndicator, hx0K] using hμ.2 x0
    have hposE : (0 : EReal) < ((x0 ⬝ᵥ xStar : ℝ) : EReal) := by
      simpa using (EReal.coe_lt_coe_iff.2 hx0pos)
    exact (not_lt_of_ge hineq) hposE
  simp [polarGauge, M, hMempty]

/-- On the polar cone, the polar gauge of an indicator is `0`. -/
lemma polarGauge_erealIndicator_eq_zero_of_mem_Kpolar {n : ℕ}
    (K : ConvexCone ℝ (Fin n → ℝ)) {xStar : Fin n → ℝ}
    (hxStar : ∀ x ∈ (K : Set (Fin n → ℝ)), (x ⬝ᵥ xStar : ℝ) ≤ 0) :
    polarGauge (erealIndicator (K : Set (Fin n → ℝ))) xStar = 0 := by
  classical
  let M : Set EReal :=
    {μ : EReal |
      0 ≤ μ ∧
        ∀ x : Fin n → ℝ,
          ((x ⬝ᵥ xStar : ℝ) : EReal) ≤
            μ * erealIndicator (K : Set (Fin n → ℝ)) x}
  have h0le : (0 : EReal) ≤ sInf M := by
    refine le_sInf ?_
    intro μ hμ
    exact hμ.1
  have hle0 : sInf M ≤ (0 : EReal) := by
    refine (EReal.le_of_forall_lt_iff_le (x := (0 : EReal)) (y := sInf M)).1 ?_
    intro z hz
    have hzpos : (0 : ℝ) < z := by
      simpa using hz
    have hzmem : (z : EReal) ∈ M := by
      refine ⟨?_, ?_⟩
      · exact_mod_cast (le_of_lt hzpos)
      · intro x
        by_cases hx : x ∈ (K : Set (Fin n → ℝ))
        · have hinner : (x ⬝ᵥ xStar : ℝ) ≤ 0 := hxStar x hx
          have hinner' : ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ (0 : EReal) := by
            exact_mod_cast hinner
          simpa [erealIndicator, hx] using hinner'
        · have htop :
              ((z : ℝ) : EReal) * (⊤ : EReal) = (⊤ : EReal) := by
            simpa using (EReal.coe_mul_top_of_pos (x := z) hzpos)
          simp [erealIndicator, hx, htop]
    exact sInf_le hzmem
  have hEq : sInf M = (0 : EReal) := le_antisymm hle0 h0le
  simp [polarGauge, M, hEq]

/-- On the polar cone, the conjugate of the indicator is `0`. -/
lemma kStar_eq_zero_of_mem_Kpolar {n : ℕ} (K : ConvexCone ℝ (Fin n → ℝ)) {xStar : Fin n → ℝ}
    (h0K : (0 : Fin n → ℝ) ∈ (K : Set (Fin n → ℝ)))
    (hxStar : ∀ x ∈ (K : Set (Fin n → ℝ)), (x ⬝ᵥ xStar : ℝ) ≤ 0) :
    sSup
        (Set.range fun x : Fin n → ℝ =>
          ((x ⬝ᵥ xStar : ℝ) : EReal) - erealIndicator (K : Set (Fin n → ℝ)) x) = 0 := by
  classical
  apply le_antisymm
  · refine sSup_le ?_
    rintro _ ⟨x, rfl⟩
    by_cases hx : x ∈ (K : Set (Fin n → ℝ))
    · have hinner : (x ⬝ᵥ xStar : ℝ) ≤ 0 := hxStar x hx
      have hinner' : ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ (0 : EReal) := by
        exact_mod_cast hinner
      simpa [erealIndicator, hx] using hinner'
    · simp [erealIndicator, hx]
  · refine le_sSup ?_
    refine ⟨0, ?_⟩
    simp [erealIndicator, h0K]

/-- Outside the polar cone, the conjugate of the indicator is `⊤`. -/
lemma kStar_eq_top_of_not_mem_Kpolar {n : ℕ} (K : ConvexCone ℝ (Fin n → ℝ)) {xStar : Fin n → ℝ}
    (hxStar : ¬ ∀ x ∈ (K : Set (Fin n → ℝ)), (x ⬝ᵥ xStar : ℝ) ≤ 0) :
    sSup
        (Set.range fun x : Fin n → ℝ =>
          ((x ⬝ᵥ xStar : ℝ) : EReal) - erealIndicator (K : Set (Fin n → ℝ)) x) = ⊤ := by
  classical
  push_neg at hxStar
  rcases hxStar with ⟨x0, hx0K, hx0pos⟩
  refine (sSup_eq_top).2 ?_
  intro b hb
  induction b using EReal.rec with
  | bot =>
      refine
        ⟨((x0 ⬝ᵥ xStar : ℝ) : EReal) -
            erealIndicator (K : Set (Fin n → ℝ)) x0, ?_, ?_⟩
      · exact ⟨x0, rfl⟩
      · simp [erealIndicator, hx0K]
  | coe r =>
      obtain ⟨m : ℕ, hm⟩ : ∃ m : ℕ, r / (x0 ⬝ᵥ xStar) < m := exists_nat_gt (r / (x0 ⬝ᵥ xStar))
      have hlt : r / (x0 ⬝ᵥ xStar) < (m + 1 : ℝ) := by
        have : (m : ℝ) < (m + 1 : ℝ) := by
          exact_mod_cast (Nat.lt_succ_self m)
        exact lt_trans hm this
      have hr : r < (m + 1 : ℝ) * (x0 ⬝ᵥ xStar) := by
        exact (div_lt_iff₀ hx0pos).1 hlt
      have hnpos : (0 : ℝ) < (m + 1 : ℝ) := by
        exact_mod_cast (Nat.succ_pos m)
      have hxmem : ((m + 1 : ℝ) • x0) ∈ (K : Set (Fin n → ℝ)) :=
        K.smul_mem hnpos hx0K
      refine
        ⟨(((((m + 1 : ℝ) • x0) ⬝ᵥ xStar : ℝ) : EReal) -
            erealIndicator (K : Set (Fin n → ℝ)) ((m + 1 : ℝ) • x0)), ?_, ?_⟩
      · exact ⟨(m + 1 : ℝ) • x0, rfl⟩
      · have : (r : EReal) < ((m + 1 : ℝ) * (x0 ⬝ᵥ xStar) : EReal) := by
          exact (EReal.coe_lt_coe_iff).2 hr
        simpa [erealIndicator, hxmem, dotProduct_comm, dotProduct_smul, smul_eq_mul, mul_assoc,
          mul_left_comm, mul_comm] using this
  | top =>
      cases (lt_irrefl (⊤ : EReal) hb)

/-- Text 15.0.7: Let `K ⊆ ℝⁿ` be a convex cone and let `k = δ(· | K)` be its indicator function.
Then the polar `kᵒ` agrees with the conjugate `k*`, and it is the indicator of the polar cone
`Kᵒ := {x⋆ ∈ ℝⁿ | ⟪x, x⋆⟫ ≤ 0 for all x ∈ K}`.

In this development, `ℝⁿ` is `Fin n → ℝ`, the indicator `δ(· | K)` is `erealIndicator K`, the polar
`kᵒ` is `polarGauge k`, the conjugate `k*` is given by `x⋆ ↦ sup_x (⟪x, x⋆⟫ - k x)`, and
`⟪x, x⋆⟫` is `x ⬝ᵥ x⋆`. -/
theorem polarGauge_erealIndicator_eq_conjugate_eq_erealIndicator_polarCone {n : ℕ}
    (K : ConvexCone ℝ (Fin n → ℝ)) (h0K : (0 : Fin n → ℝ) ∈ (K : Set (Fin n → ℝ))) :
    let k : (Fin n → ℝ) → EReal := erealIndicator (K : Set (Fin n → ℝ))
    let Kpolar : Set (Fin n → ℝ) :=
      {xStar | ∀ x ∈ (K : Set (Fin n → ℝ)), (x ⬝ᵥ xStar : ℝ) ≤ 0}
    let kStar : (Fin n → ℝ) → EReal :=
      fun xStar => sSup (Set.range fun x : Fin n → ℝ => ((x ⬝ᵥ xStar : ℝ) : EReal) - k x)
    polarGauge k = kStar ∧ polarGauge k = erealIndicator Kpolar := by
  classical
  simp
  constructor
  · funext xStar
    by_cases hxStar : ∀ x ∈ (K : Set (Fin n → ℝ)), (x ⬝ᵥ xStar : ℝ) ≤ 0
    · have hpolar :
          polarGauge (erealIndicator (K : Set (Fin n → ℝ))) xStar = 0 :=
        polarGauge_erealIndicator_eq_zero_of_mem_Kpolar (K := K) hxStar
      have hkStar :
          sSup
              (Set.range fun x : Fin n → ℝ =>
                ((x ⬝ᵥ xStar : ℝ) : EReal) -
                  erealIndicator (K : Set (Fin n → ℝ)) x) = 0 :=
        kStar_eq_zero_of_mem_Kpolar (K := K) h0K hxStar
      simp [hpolar, hkStar]
    · have hpolar :
          polarGauge (erealIndicator (K : Set (Fin n → ℝ))) xStar = ⊤ :=
        polarGauge_erealIndicator_eq_top_of_not_mem_Kpolar (K := K) hxStar
      have hkStar :
          sSup
              (Set.range fun x : Fin n → ℝ =>
                ((x ⬝ᵥ xStar : ℝ) : EReal) -
                  erealIndicator (K : Set (Fin n → ℝ)) x) = ⊤ :=
        kStar_eq_top_of_not_mem_Kpolar (K := K) hxStar
      simp [hpolar, hkStar]
  · funext xStar
    by_cases hxStar : ∀ x ∈ (K : Set (Fin n → ℝ)), (x ⬝ᵥ xStar : ℝ) ≤ 0
    · have hpolar :
          polarGauge (erealIndicator (K : Set (Fin n → ℝ))) xStar = 0 :=
        polarGauge_erealIndicator_eq_zero_of_mem_Kpolar (K := K) hxStar
      have hind :
          erealIndicator
              {xStar | ∀ x ∈ (K : Set (Fin n → ℝ)), (x ⬝ᵥ xStar : ℝ) ≤ 0} xStar = 0 := by
        simpa [erealIndicator] using hxStar
      calc
        polarGauge (erealIndicator (K : Set (Fin n → ℝ))) xStar = 0 := hpolar
        _ = erealIndicator
              {xStar | ∀ x ∈ (K : Set (Fin n → ℝ)), (x ⬝ᵥ xStar : ℝ) ≤ 0} xStar := by
            simpa using hind.symm
    · have hpolar :
          polarGauge (erealIndicator (K : Set (Fin n → ℝ))) xStar = ⊤ :=
        polarGauge_erealIndicator_eq_top_of_not_mem_Kpolar (K := K) hxStar
      have hind :
          erealIndicator
              {xStar | ∀ x ∈ (K : Set (Fin n → ℝ)), (x ⬝ᵥ xStar : ℝ) ≤ 0} xStar = ⊤ := by
        simpa [erealIndicator] using hxStar
      calc
        polarGauge (erealIndicator (K : Set (Fin n → ℝ))) xStar = ⊤ := hpolar
        _ = erealIndicator
              {xStar | ∀ x ∈ (K : Set (Fin n → ℝ)), (x ⬝ᵥ xStar : ℝ) ≤ 0} xStar := by
            simpa using hind.symm

/-- Text 15.0.8: Define `k : ℝ² → [0, +∞)` by
`k(ξ₁, ξ₂) = sqrt (ξ₁^2 + ξ₂^2) + ξ₁`. Then `k` is a closed gauge function.

Its polar gauge `k^∘` is given by the piecewise formula
`k^∘(ξ₁⋆, ξ₂⋆) = (1/2) * ((ξ₂⋆)^2 / ξ₁⋆ + ξ₁⋆)` if `0 < ξ₁⋆`,
`k^∘(0, 0) = 0`, and `k^∘(ξ₁⋆, ξ₂⋆) = +∞` otherwise.

Neither `k` nor `k^∘` is a norm (e.g. neither is an even function). -/
noncomputable def gaugeSqrtSumSq_add_fst (x : Fin 2 → ℝ) : EReal :=
  ((Real.sqrt ((x 0) ^ 2 + (x 1) ^ 2) + x 0) : ℝ)

/-- Rewrite `gaugeSqrtSumSq_add_fst` using the Euclidean norm on `ℝ²`. -/
lemma gaugeSqrtSumSq_add_fst_eq_euclideanNorm_add_fst (x : Fin 2 → ℝ) :
    gaugeSqrtSumSq_add_fst x =
      ((‖(EuclideanSpace.equiv (Fin 2) ℝ).symm x‖ + x 0 : ℝ) : EReal) := by
  classical
  set e : (Fin 2 → ℝ) → EuclideanSpace ℝ (Fin 2) :=
    ((EuclideanSpace.equiv (Fin 2) ℝ).symm : (Fin 2 → ℝ) → EuclideanSpace ℝ (Fin 2))
  have hnorm :
      Real.sqrt ((x 0) ^ 2 + (x 1) ^ 2) = ‖e x‖ := by
    symm
    calc
      ‖e x‖ = Real.sqrt (∑ i : Fin 2, ‖(e x) i‖ ^ 2) := by
        simpa using (EuclideanSpace.norm_eq (x := e x))
      _ = Real.sqrt ((x 0) ^ 2 + (x 1) ^ 2) := by
        simp [e, PiLp.coe_symm_continuousLinearEquiv, PiLp.toLp_apply,
          Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  simp [gaugeSqrtSumSq_add_fst, hnorm, e]

/-- Convexity of `gaugeSqrtSumSq_add_fst` on `Set.univ`. -/
lemma gaugeSqrtSumSq_add_fst_convexFunctionOn :
    ConvexFunctionOn (S := (Set.univ : Set (Fin 2 → ℝ))) gaugeSqrtSumSq_add_fst := by
  classical
  have hconv_univ : Convex ℝ (Set.univ : Set (Fin 2 → ℝ)) := by
    simpa using (convex_univ : Convex ℝ (Set.univ : Set (Fin 2 → ℝ)))
  have hnotbot :
      ∀ x ∈ (Set.univ : Set (Fin 2 → ℝ)), gaugeSqrtSumSq_add_fst x ≠ (⊥ : EReal) := by
    intro x hx
    simp [gaugeSqrtSumSq_add_fst]
  refine (convexFunctionOn_iff_segment_inequality
      (C := (Set.univ : Set (Fin 2 → ℝ))) (f := gaugeSqrtSumSq_add_fst)
      hconv_univ hnotbot).2 ?_
  intro x hx y hy t ht0 ht1
  set e : (Fin 2 → ℝ) → EuclideanSpace ℝ (Fin 2) :=
    ((EuclideanSpace.equiv (Fin 2) ℝ).symm : (Fin 2 → ℝ) → EuclideanSpace ℝ (Fin 2))
  have hlin :
      e ((1 - t) • x + t • y) = (1 - t) • e x + t • e y := by
    ext i
    simp [e, smul_eq_mul, add_comm]
  have hcoord :
      ((1 - t) • x + t • y) 0 = (1 - t) * x 0 + t * y 0 := by
    simp [smul_eq_mul, add_comm]
  have ht0' : 0 ≤ t := le_of_lt ht0
  have h1t : 0 ≤ 1 - t := by linarith
  have hnorm :
      ‖e ((1 - t) • x + t • y)‖ ≤ (1 - t) * ‖e x‖ + t * ‖e y‖ := by
    calc
      ‖e ((1 - t) • x + t • y)‖ = ‖(1 - t) • e x + t • e y‖ := by
        simp [hlin]
      _ ≤ ‖(1 - t) • e x‖ + ‖t • e y‖ := by
        simpa using norm_add_le ((1 - t) • e x) (t • e y)
      _ = |1 - t| * ‖e x‖ + |t| * ‖e y‖ := by
        simp [norm_smul]
      _ = (1 - t) * ‖e x‖ + t * ‖e y‖ := by
        simp [abs_of_nonneg ht0', abs_of_nonneg h1t]
  have hsum :
      ‖e ((1 - t) • x + t • y)‖ + ((1 - t) • x + t • y) 0 ≤
        (1 - t) * (‖e x‖ + x 0) + t * (‖e y‖ + y 0) := by
    have hsum' :
        ‖e ((1 - t) • x + t • y)‖ + ((1 - t) * x 0 + t * y 0) ≤
          (1 - t) * ‖e x‖ + t * ‖e y‖ + ((1 - t) * x 0 + t * y 0) := by
      exact add_le_add hnorm le_rfl
    have hdistrib :
        (1 - t) * ‖e x‖ + t * ‖e y‖ + ((1 - t) * x 0 + t * y 0) =
          (1 - t) * (‖e x‖ + x 0) + t * (‖e y‖ + y 0) := by
      ring_nf
    simpa [hcoord, hdistrib] using hsum'
  have hsumE :
      ((‖e ((1 - t) • x + t • y)‖ + ((1 - t) • x + t • y) 0 : ℝ) : EReal) ≤
        (((1 - t) * (‖e x‖ + x 0) + t * (‖e y‖ + y 0) : ℝ) : EReal) := by
    exact (EReal.coe_le_coe_iff).2 hsum
  simpa [gaugeSqrtSumSq_add_fst_eq_euclideanNorm_add_fst, EReal.coe_add, EReal.coe_mul, e]
    using hsumE

/-- Nonnegativity of `gaugeSqrtSumSq_add_fst`. -/
lemma gaugeSqrtSumSq_add_fst_nonneg (x : Fin 2 → ℝ) :
    (0 : EReal) ≤ gaugeSqrtSumSq_add_fst x := by
  have hsq : (x 0) ^ 2 ≤ (x 0) ^ 2 + (x 1) ^ 2 := by
    nlinarith
  have habs : |x 0| ≤ Real.sqrt ((x 0) ^ 2 + (x 1) ^ 2) := by
    have h := Real.sqrt_le_sqrt hsq
    simpa [Real.sqrt_sq_eq_abs] using h
  have hneg : -x 0 ≤ Real.sqrt ((x 0) ^ 2 + (x 1) ^ 2) :=
    le_trans (neg_le_abs (x 0)) habs
  have h0 : 0 ≤ Real.sqrt ((x 0) ^ 2 + (x 1) ^ 2) + x 0 := by
    linarith
  have h0E :
      (0 : EReal) ≤ ((Real.sqrt ((x 0) ^ 2 + (x 1) ^ 2) + x 0 : ℝ) : EReal) := by
    exact_mod_cast h0
  simpa [gaugeSqrtSumSq_add_fst] using h0E

/-- Positive homogeneity of `gaugeSqrtSumSq_add_fst`. -/
lemma gaugeSqrtSumSq_add_fst_smul (x : Fin 2 → ℝ) (r : ℝ) (hr : 0 ≤ r) :
    gaugeSqrtSumSq_add_fst (r • x) = (r : EReal) * gaugeSqrtSumSq_add_fst x := by
  classical
  set e : (Fin 2 → ℝ) → EuclideanSpace ℝ (Fin 2) :=
    ((EuclideanSpace.equiv (Fin 2) ℝ).symm : (Fin 2 → ℝ) → EuclideanSpace ℝ (Fin 2))
  have hcoord : (r • x) 0 = r * x 0 := by
    simp [smul_eq_mul]
  have hlin : e (r • x) = r • e x := by
    ext i
    simp [e, smul_eq_mul]
  have habs : |r| = r := abs_of_nonneg hr
  calc
    gaugeSqrtSumSq_add_fst (r • x) =
        ((‖e (r • x)‖ + (r • x) 0 : ℝ) : EReal) := by
          simpa using (gaugeSqrtSumSq_add_fst_eq_euclideanNorm_add_fst (x := r • x))
    _ = ((‖r • e x‖ + r * x 0 : ℝ) : EReal) := by
          simp [hlin, hcoord]
    _ = ((|r| * ‖e x‖ + r * x 0 : ℝ) : EReal) := by
          simp [norm_smul]
    _ = ((r * ‖e x‖ + r * x 0 : ℝ) : EReal) := by
          simp [habs]
    _ = ((r * (‖e x‖ + x 0) : ℝ) : EReal) := by
          ring_nf
    _ = (r : EReal) * ((‖e x‖ + x 0 : ℝ) : EReal) := by
          simp [EReal.coe_mul]
    _ = (r : EReal) * gaugeSqrtSumSq_add_fst x := by
          simp [gaugeSqrtSumSq_add_fst_eq_euclideanNorm_add_fst, e]

/-- The epigraph of `gaugeSqrtSumSq_add_fst` is closed. -/
lemma isClosed_epigraph_gaugeSqrtSumSq_add_fst :
    IsClosed (epigraph (S := (Set.univ : Set (Fin 2 → ℝ))) gaugeSqrtSumSq_add_fst) := by
  have hcont_left :
      Continuous (fun p : (Fin 2 → ℝ) × ℝ =>
        Real.sqrt ((p.1 0) ^ 2 + (p.1 1) ^ 2) + p.1 0) := by
    have hcont0 : Continuous (fun p : (Fin 2 → ℝ) × ℝ => p.1 0) :=
      (continuous_apply 0).comp continuous_fst
    have hcont1 : Continuous (fun p : (Fin 2 → ℝ) × ℝ => p.1 1) :=
      (continuous_apply 1).comp continuous_fst
    have hsq0 : Continuous (fun p : (Fin 2 → ℝ) × ℝ => (p.1 0) ^ 2) :=
      hcont0.pow 2
    have hsq1 : Continuous (fun p : (Fin 2 → ℝ) × ℝ => (p.1 1) ^ 2) :=
      hcont1.pow 2
    have hsum : Continuous (fun p : (Fin 2 → ℝ) × ℝ => (p.1 0) ^ 2 + (p.1 1) ^ 2) :=
      hsq0.add hsq1
    have hsqrt :
        Continuous (fun p : (Fin 2 → ℝ) × ℝ =>
          Real.sqrt ((p.1 0) ^ 2 + (p.1 1) ^ 2)) := by
      simpa using (Real.continuous_sqrt.comp hsum)
    exact hsqrt.add hcont0
  have hclosed :
      IsClosed {p : (Fin 2 → ℝ) × ℝ |
        Real.sqrt ((p.1 0) ^ 2 + (p.1 1) ^ 2) + p.1 0 ≤ p.2} :=
    isClosed_le hcont_left continuous_snd
  have hrewrite :
      epigraph (S := (Set.univ : Set (Fin 2 → ℝ))) gaugeSqrtSumSq_add_fst =
        {p : (Fin 2 → ℝ) × ℝ |
          Real.sqrt ((p.1 0) ^ 2 + (p.1 1) ^ 2) + p.1 0 ≤ p.2} := by
    ext p
    constructor
    · intro hp
      have hle :
          gaugeSqrtSumSq_add_fst p.1 ≤ (p.2 : EReal) :=
        (mem_epigraph_univ_iff (f := gaugeSqrtSumSq_add_fst) (x := p.1) (μ := p.2)).1 hp
      have hle' :
          (Real.sqrt ((p.1 0) ^ 2 + (p.1 1) ^ 2) + p.1 0 : ℝ) ≤ p.2 := by
        exact (EReal.coe_le_coe_iff).1 (by simpa [gaugeSqrtSumSq_add_fst] using hle)
      simpa using hle'
    · intro hp
      have hleE :
          gaugeSqrtSumSq_add_fst p.1 ≤ (p.2 : EReal) := by
        have hleE' :
            ((Real.sqrt ((p.1 0) ^ 2 + (p.1 1) ^ 2) + p.1 0 : ℝ) : EReal) ≤
              (p.2 : EReal) := by
          exact (EReal.coe_le_coe_iff).2 hp
        simpa [gaugeSqrtSumSq_add_fst] using hleE'
      exact
        (mem_epigraph_univ_iff (f := gaugeSqrtSumSq_add_fst) (x := p.1) (μ := p.2)).2 hleE
  simpa [hrewrite] using hclosed

/-- Text 15.0.8 (closed gauge): the function `gaugeSqrtSumSq_add_fst` is a gauge and its epigraph is
closed. -/
theorem gaugeSqrtSumSq_add_fst_isGauge_isClosed :
    IsGauge gaugeSqrtSumSq_add_fst ∧
      IsClosed (epigraph (S := (Set.univ : Set (Fin 2 → ℝ))) gaugeSqrtSumSq_add_fst) := by
  refine ⟨?_, ?_⟩
  · refine ⟨gaugeSqrtSumSq_add_fst_convexFunctionOn, gaugeSqrtSumSq_add_fst_nonneg,
      gaugeSqrtSumSq_add_fst_smul, ?_⟩
    simp [gaugeSqrtSumSq_add_fst]
  · exact isClosed_epigraph_gaugeSqrtSumSq_add_fst

/-- Text 15.0.8 (polar formula): explicit piecewise formula for the polar gauge of
`gaugeSqrtSumSq_add_fst`. -/
noncomputable def polarGaugeSqrtSumSq_add_fst (xStar : Fin 2 → ℝ) : EReal :=
  if 0 < xStar 0 then
    ((1 / 2 : ℝ) * (((xStar 1) ^ 2) / (xStar 0) + xStar 0) : ℝ)
  else if xStar 0 = 0 ∧ xStar 1 = 0 then
    (0 : EReal)
  else
    ⊤

/-- Bound `sqrt(t^2 + b^2) - t` by `b^2 / (2t)` for `t > 0`. -/
lemma sqrt_sq_add_sub_le (t b : ℝ) (ht : 0 < t) :
    Real.sqrt (t ^ 2 + b ^ 2) - t ≤ b ^ 2 / (2 * t) := by
  have ht0 : 0 ≤ t := le_of_lt ht
  have hdenom_pos : 0 < Real.sqrt (t ^ 2 + b ^ 2) + t := by
    have hsqrt_nonneg : 0 ≤ Real.sqrt (t ^ 2 + b ^ 2) := Real.sqrt_nonneg _
    linarith
  have hdenom_ne : Real.sqrt (t ^ 2 + b ^ 2) + t ≠ 0 := by linarith
  have hmul :
      (Real.sqrt (t ^ 2 + b ^ 2) - t) * (Real.sqrt (t ^ 2 + b ^ 2) + t) = b ^ 2 := by
    have hs : (Real.sqrt (t ^ 2 + b ^ 2)) ^ 2 = t ^ 2 + b ^ 2 := by
      have hnonneg : 0 ≤ t ^ 2 + b ^ 2 := by nlinarith
      simpa using (Real.sq_sqrt hnonneg)
    calc
      (Real.sqrt (t ^ 2 + b ^ 2) - t) * (Real.sqrt (t ^ 2 + b ^ 2) + t) =
          (Real.sqrt (t ^ 2 + b ^ 2)) ^ 2 - t ^ 2 := by
            ring
      _ = (t ^ 2 + b ^ 2) - t ^ 2 := by simp [hs]
      _ = b ^ 2 := by ring
  have hfrac :
      Real.sqrt (t ^ 2 + b ^ 2) - t =
        b ^ 2 / (Real.sqrt (t ^ 2 + b ^ 2) + t) := by
    calc
      Real.sqrt (t ^ 2 + b ^ 2) - t =
          ((Real.sqrt (t ^ 2 + b ^ 2) - t) * (Real.sqrt (t ^ 2 + b ^ 2) + t)) /
            (Real.sqrt (t ^ 2 + b ^ 2) + t) := by
          field_simp [hdenom_ne]
      _ = b ^ 2 / (Real.sqrt (t ^ 2 + b ^ 2) + t) := by
          simp [hmul]
  have hsqrt_ge : t ≤ Real.sqrt (t ^ 2 + b ^ 2) := by
    have htsq : t ^ 2 ≤ t ^ 2 + b ^ 2 := by nlinarith
    have h := Real.sqrt_le_sqrt htsq
    simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg ht0] using h
  have hdenom_ge : 2 * t ≤ Real.sqrt (t ^ 2 + b ^ 2) + t := by linarith
  have hb2_nonneg : 0 ≤ b ^ 2 := by nlinarith
  have hfrac_le :
      b ^ 2 / (Real.sqrt (t ^ 2 + b ^ 2) + t) ≤ b ^ 2 / (2 * t) :=
    div_le_div_of_nonneg_left hb2_nonneg (by nlinarith [ht]) hdenom_ge
  simpa [hfrac] using hfrac_le

/-- Cauchy–Schwarz inequality for `Fin 2 → ℝ` in dot-product form. -/
lemma dotProduct_le_mul_sqrt_dotProduct_self_fin2 (x y : Fin 2 → ℝ) :
    (x ⬝ᵥ y : ℝ) ≤
      Real.sqrt ((x 0) ^ 2 + (x 1) ^ 2) * Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2) := by
  have hsq :
      (x ⬝ᵥ y : ℝ) ^ 2 ≤
        ((x 0) ^ 2 + (x 1) ^ 2) * ((y 0) ^ 2 + (y 1) ^ 2) := by
    have hsq' :
        (∑ i : Fin 2, x i * y i) ^ 2 ≤
          (∑ i : Fin 2, x i ^ 2) * ∑ i : Fin 2, y i ^ 2 := by
      simpa using
        (Finset.sum_mul_sq_le_sq_mul_sq (s := (Finset.univ : Finset (Fin 2))) (f := x) (g := y))
    simpa [dotProduct, Fin.sum_univ_two] using hsq'
  have hnonneg :
      0 ≤
        Real.sqrt ((x 0) ^ 2 + (x 1) ^ 2) * Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsq' :
      (x ⬝ᵥ y : ℝ) ^ 2 ≤
        (Real.sqrt ((x 0) ^ 2 + (x 1) ^ 2) * Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ 2 := by
    have hx_nonneg : 0 ≤ (x 0) ^ 2 + (x 1) ^ 2 := by nlinarith
    have hy_nonneg : 0 ≤ (y 0) ^ 2 + (y 1) ^ 2 := by nlinarith
    have hsq_rhs :
        (Real.sqrt ((x 0) ^ 2 + (x 1) ^ 2) * Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ 2 =
          ((x 0) ^ 2 + (x 1) ^ 2) * ((y 0) ^ 2 + (y 1) ^ 2) := by
      calc
        (Real.sqrt ((x 0) ^ 2 + (x 1) ^ 2) * Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ 2 =
            (Real.sqrt ((x 0) ^ 2 + (x 1) ^ 2)) ^ 2 *
              (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ 2 := by
              ring
        _ = ((x 0) ^ 2 + (x 1) ^ 2) * ((y 0) ^ 2 + (y 1) ^ 2) := by
              simp [Real.sq_sqrt, hx_nonneg, hy_nonneg]
    simpa [hsq_rhs] using hsq
  exact le_of_sq_le_sq hsq' hnonneg

/-- If `xStar 0 < 0`, the polar gauge of `gaugeSqrtSumSq_add_fst` is `⊤`. -/
lemma polarGauge_gaugeSqrtSumSq_add_fst_eq_top_of_fst_lt_zero (xStar : Fin 2 → ℝ)
    (hx : xStar 0 < 0) : polarGauge gaugeSqrtSumSq_add_fst xStar = ⊤ := by
  classical
  let M : Set EReal :=
    {μ : EReal | 0 ≤ μ ∧ ∀ x : Fin 2 → ℝ,
      ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ μ * gaugeSqrtSumSq_add_fst x}
  have hMempty : M = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro μ hμ
    have hineq := hμ.2 (![(-1), 0])
    have hdot : (![(-1), 0] ⬝ᵥ xStar : ℝ) = -xStar 0 := by
      simp [dotProduct, Fin.sum_univ_two]
    have hk : gaugeSqrtSumSq_add_fst (![(-1), 0]) = (0 : EReal) := by
      norm_num [gaugeSqrtSumSq_add_fst, pow_two]
    have hpos : (0 : ℝ) < -xStar 0 := by linarith
    have hposE : (0 : EReal) < ((-xStar 0 : ℝ) : EReal) := by
      exact_mod_cast hpos
    have hineq' : ((-xStar 0 : ℝ) : EReal) ≤ (0 : EReal) := by
      simpa [hdot, hk] using hineq
    exact (not_lt_of_ge hineq') hposE
  have hEq : sInf M = (⊤ : EReal) := by
    simp [hMempty]
  unfold polarGauge
  simpa [M] using hEq

/-- If `xStar 0 = 0` and `xStar 1 ≠ 0`, the polar gauge is `⊤`. -/
lemma polarGauge_gaugeSqrtSumSq_add_fst_eq_top_of_fst_eq_zero_snd_ne_zero
    (xStar : Fin 2 → ℝ) (hx0 : xStar 0 = 0) (hx1 : xStar 1 ≠ 0) :
    polarGauge gaugeSqrtSumSq_add_fst xStar = ⊤ := by
  classical
  let M : Set EReal :=
    {μ : EReal | 0 ≤ μ ∧ ∀ x : Fin 2 → ℝ,
      ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ μ * gaugeSqrtSumSq_add_fst x}
  have hMsubset : M ⊆ {⊤} := by
    intro μ hμ
    by_cases hμtop : μ = ⊤
    · simp [hμtop]
    · exfalso
      have hμbot : μ ≠ (⊥ : EReal) := by
        intro hbot
        have h0le : (0 : EReal) ≤ μ := hμ.1
        simp [hbot] at h0le
      set a : ℝ := μ.toReal
      have hμ_eq : μ = (a : EReal) := by
        simpa [a] using (EReal.coe_toReal (x := μ) hμtop hμbot).symm
      have ha_nonneg : 0 ≤ a := EReal.toReal_nonneg hμ.1
      set t : ℝ := a + 1
      have ht_pos : 0 < t := by linarith
      let x : Fin 2 → ℝ := ![-t, xStar 1]
      have hdot : (x ⬝ᵥ xStar : ℝ) = (xStar 1) ^ 2 := by
        simp [x, dotProduct, Fin.sum_univ_two, hx0, pow_two]
      have hkx :
          gaugeSqrtSumSq_add_fst x =
            ((Real.sqrt (t ^ 2 + (xStar 1) ^ 2) + (-t) : ℝ) : EReal) := by
        simp [gaugeSqrtSumSq_add_fst, x, pow_two]
      have hineq := hμ.2 x
      have hineq' :
          ((xStar 1) ^ 2 : EReal) ≤
            ((a * (Real.sqrt (t ^ 2 + (xStar 1) ^ 2) + (-t)) : ℝ) : EReal) := by
        simpa [hdot, hμ_eq, hkx, EReal.coe_mul] using hineq
      have hineq_real :
          (xStar 1) ^ 2 ≤ a * (Real.sqrt (t ^ 2 + (xStar 1) ^ 2) - t) := by
        have hineq_real' := (EReal.coe_le_coe_iff).1 hineq'
        simpa [pow_two, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hineq_real'
      have hsqrt_le :
          Real.sqrt (t ^ 2 + (xStar 1) ^ 2) - t ≤ (xStar 1) ^ 2 / (2 * t) :=
        sqrt_sq_add_sub_le t (xStar 1) ht_pos
      have hle_mul :
          a * (Real.sqrt (t ^ 2 + (xStar 1) ^ 2) - t) ≤
            a * ((xStar 1) ^ 2 / (2 * t)) :=
        mul_le_mul_of_nonneg_left hsqrt_le ha_nonneg
      have hb2_pos : 0 < (xStar 1) ^ 2 := by
        exact sq_pos_of_ne_zero hx1
      have hratio_lt : a / (2 * t) < 1 := by
        have ht_pos' : 0 < 2 * t := by nlinarith [ht_pos]
        have hnum : a < 2 * t := by
          simp [t] at *
          linarith
        exact (div_lt_iff₀ ht_pos').2 (by simpa using hnum)
      have hmul_lt : a * ((xStar 1) ^ 2 / (2 * t)) < (xStar 1) ^ 2 := by
        have hmul_lt' :
            (a / (2 * t)) * (xStar 1) ^ 2 < 1 * (xStar 1) ^ 2 :=
          mul_lt_mul_of_pos_right hratio_lt hb2_pos
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul_lt'
      have hlt : a * (Real.sqrt (t ^ 2 + (xStar 1) ^ 2) - t) < (xStar 1) ^ 2 :=
        lt_of_le_of_lt hle_mul hmul_lt
      exact (not_le_of_gt hlt) hineq_real
  have htop_le : (⊤ : EReal) ≤ sInf M := by
    have hle := sInf_le_sInf hMsubset
    simpa using hle
  have hEq : sInf M = ⊤ := (top_le_iff).1 htop_le
  unfold polarGauge
  simpa [M] using hEq

/-- Feasible multiplier for the polar gauge when `xStar 0 > 0`. -/
lemma polarGauge_gaugeSqrtSumSq_add_fst_mu0_feasible_of_fst_pos (xStar : Fin 2 → ℝ)
    (hpos : 0 < xStar 0) :
    let μ0 : ℝ := (1 / 2) * ((xStar 1) ^ 2 / (xStar 0) + xStar 0)
    (0 : EReal) ≤ (μ0 : EReal) ∧
      ∀ x : Fin 2 → ℝ,
        ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ (μ0 : EReal) * gaugeSqrtSumSq_add_fst x := by
  classical
  intro μ0
  set a : ℝ := xStar 0 with ha
  set b : ℝ := xStar 1 with hb
  have ha_pos : 0 < a := by simpa [ha] using hpos
  have ha_nonneg : 0 ≤ a := le_of_lt ha_pos
  have hμ0_nonneg : 0 ≤ μ0 := by
    have hb2_nonneg : 0 ≤ b ^ 2 := by nlinarith
    have hdiv_nonneg : 0 ≤ b ^ 2 / a := by
      exact div_nonneg hb2_nonneg ha_nonneg
    have hsum_nonneg : 0 ≤ b ^ 2 / a + a := by nlinarith
    have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) := by norm_num
    exact mul_nonneg hhalf_nonneg hsum_nonneg
  refine ⟨?_, ?_⟩
  · exact_mod_cast hμ0_nonneg
  · intro x
    let y0 : ℝ := (a ^ 2 - b ^ 2) / (2 * a)
    let y : Fin 2 → ℝ := ![y0, b]
    have hsum : μ0 + y0 = a := by
      have ha_ne : a ≠ 0 := by linarith
      simp [μ0, y0, ha.symm, hb.symm]
      field_simp [ha_ne]
      ring_nf
    have hμ0_sq : μ0 ^ 2 = y0 ^ 2 + b ^ 2 := by
      have ha_ne : a ≠ 0 := by linarith
      simp [μ0, y0, ha.symm, hb.symm]
      field_simp [ha_ne]
      ring_nf
    have hμ0_sqrt : Real.sqrt (y0 ^ 2 + b ^ 2) = μ0 := by
      have hy_nonneg : 0 ≤ y0 ^ 2 + b ^ 2 := by nlinarith
      have hμ0_sq' : y0 ^ 2 + b ^ 2 = μ0 ^ 2 := by
        nlinarith [hμ0_sq]
      exact (Real.sqrt_eq_iff_eq_sq hy_nonneg hμ0_nonneg).2 hμ0_sq'
    have hcs :
        (x ⬝ᵥ y : ℝ) ≤ Real.sqrt ((x 0) ^ 2 + (x 1) ^ 2) * μ0 := by
      simpa [y, hμ0_sqrt] using
        (dotProduct_le_mul_sqrt_dotProduct_self_fin2 x y)
    have hdot_decomp :
        (x ⬝ᵥ xStar : ℝ) = μ0 * x 0 + (x ⬝ᵥ y : ℝ) := by
      calc
        (x ⬝ᵥ xStar : ℝ) = x 0 * a + x 1 * b := by
          simp [dotProduct, Fin.sum_univ_two, ha.symm, hb.symm]
        _ = a * x 0 + b * x 1 := by ring
        _ = (μ0 + y0) * x 0 + b * x 1 := by
          simp [hsum]
        _ = μ0 * x 0 + (y0 * x 0 + b * x 1) := by ring
        _ = μ0 * x 0 + (x 0 * y0 + x 1 * b) := by ring
        _ = μ0 * x 0 + (x ⬝ᵥ y : ℝ) := by
          simp [dotProduct, Fin.sum_univ_two, y]
    have hineq_real :
        (x ⬝ᵥ xStar : ℝ) ≤
          μ0 * x 0 + μ0 * Real.sqrt ((x 0) ^ 2 + (x 1) ^ 2) := by
      have h := add_le_add_left hcs (μ0 * x 0)
      simpa [hdot_decomp, mul_comm, mul_left_comm, mul_assoc] using h
    have hineq_real' :
        (x ⬝ᵥ xStar : ℝ) ≤
          μ0 * (Real.sqrt ((x 0) ^ 2 + (x 1) ^ 2) + x 0) := by
      calc
        (x ⬝ᵥ xStar : ℝ) ≤ μ0 * x 0 + μ0 * Real.sqrt ((x 0) ^ 2 + (x 1) ^ 2) :=
          hineq_real
        _ = μ0 * (Real.sqrt ((x 0) ^ 2 + (x 1) ^ 2) + x 0) := by ring
    have hineqE :
        ((x ⬝ᵥ xStar : ℝ) : EReal) ≤
          ((μ0 * (Real.sqrt ((x 0) ^ 2 + (x 1) ^ 2) + x 0) : ℝ) : EReal) := by
      exact_mod_cast hineq_real'
    simpa [gaugeSqrtSumSq_add_fst, EReal.coe_mul] using hineqE

/-- A point that attains the polar inequality when `xStar 0 > 0`. -/
lemma polarGauge_gaugeSqrtSumSq_add_fst_witness_of_fst_pos (xStar : Fin 2 → ℝ)
    (hpos : 0 < xStar 0) :
    let t : ℝ := xStar 1 / xStar 0
    let x : Fin 2 → ℝ := ![(1 - t ^ 2) / 2, t]
    gaugeSqrtSumSq_add_fst x = (1 : EReal) ∧
      (x ⬝ᵥ xStar : ℝ) = (1 / 2) * ((xStar 1) ^ 2 / (xStar 0) + xStar 0) := by
  classical
  intro t x
  set a : ℝ := xStar 0 with ha
  set b : ℝ := xStar 1 with hb
  have ha_ne : a ≠ 0 := by linarith
  have hxsq :
      (x 0) ^ 2 + (x 1) ^ 2 = ((1 + t ^ 2) ^ 2) / 4 := by
    simp [x, pow_two]
    ring
  have hsqrt :
      Real.sqrt ((x 0) ^ 2 + (x 1) ^ 2) = (1 + t ^ 2) / 2 := by
    have hnonneg : 0 ≤ (1 + t ^ 2) / 2 := by nlinarith
    have hxsq' : (x 0) ^ 2 + (x 1) ^ 2 = ((1 + t ^ 2) / 2) ^ 2 := by
      calc
        (x 0) ^ 2 + (x 1) ^ 2 = ((1 + t ^ 2) ^ 2) / 4 := hxsq
        _ = ((1 + t ^ 2) / 2) ^ 2 := by ring
    exact (Real.sqrt_eq_iff_eq_sq (by nlinarith) hnonneg).2 hxsq'
  have hgauge : gaugeSqrtSumSq_add_fst x = (1 : EReal) := by
    have hsum : (1 + t ^ 2) / 2 + (1 - t ^ 2) / 2 = (1 : ℝ) := by ring
    have hx0 : x 0 = (1 - t ^ 2) / 2 := by simp [x]
    calc
      gaugeSqrtSumSq_add_fst x =
          ((Real.sqrt ((x 0) ^ 2 + (x 1) ^ 2) + x 0 : ℝ) : EReal) := by
            simp [gaugeSqrtSumSq_add_fst]
      _ = (((1 + t ^ 2) / 2 + x 0 : ℝ) : EReal) := by
            simp [hsqrt]
      _ = (((1 + t ^ 2) / 2 + (1 - t ^ 2) / 2 : ℝ) : EReal) := by
            simp [hx0]
      _ = (1 : EReal) := by
            simp [hsum]
  have hdot :
      (x ⬝ᵥ xStar : ℝ) = (1 / 2) * (b ^ 2 / a + a) := by
    calc
      (x ⬝ᵥ xStar : ℝ) = ((1 - t ^ 2) / 2) * a + t * b := by
        simp [x, dotProduct, Fin.sum_univ_two, ha.symm, hb.symm]
      _ = (1 / 2) * (b ^ 2 / a + a) := by
        simp [t, ha.symm, hb.symm]
        field_simp [ha_ne]
        ring_nf
  refine ⟨hgauge, ?_⟩
  simpa [ha.symm, hb.symm] using hdot

/-- Compute the polar gauge value for `xStar 0 > 0`. -/
lemma polarGauge_gaugeSqrtSumSq_add_fst_eq_mu0_of_fst_pos (xStar : Fin 2 → ℝ)
    (hpos : 0 < xStar 0) :
    polarGauge gaugeSqrtSumSq_add_fst xStar =
      ((1 / 2) * ((xStar 1) ^ 2 / (xStar 0) + xStar 0) : ℝ) := by
  classical
  set μ0 : ℝ := (1 / 2) * ((xStar 1) ^ 2 / (xStar 0) + xStar 0)
  have hμ0_feasible :
      (0 : EReal) ≤ (μ0 : EReal) ∧
        ∀ x : Fin 2 → ℝ,
          ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ (μ0 : EReal) * gaugeSqrtSumSq_add_fst x := by
    simpa [μ0] using
      (polarGauge_gaugeSqrtSumSq_add_fst_mu0_feasible_of_fst_pos (xStar := xStar) hpos)
  have hμ0_mem :
      (μ0 : EReal) ∈
        {μ : EReal | 0 ≤ μ ∧ ∀ x : Fin 2 → ℝ,
          ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ μ * gaugeSqrtSumSq_add_fst x} := by
    exact hμ0_feasible
  have hle : polarGauge gaugeSqrtSumSq_add_fst xStar ≤ (μ0 : EReal) := by
    unfold polarGauge
    exact sInf_le hμ0_mem
  have hge : (μ0 : EReal) ≤ polarGauge gaugeSqrtSumSq_add_fst xStar := by
    unfold polarGauge
    refine le_sInf ?_
    intro μ hμ
    set t : ℝ := xStar 1 / xStar 0
    set x : Fin 2 → ℝ := ![(1 - t ^ 2) / 2, t]
    have hwit :
        gaugeSqrtSumSq_add_fst x = (1 : EReal) ∧
          (x ⬝ᵥ xStar : ℝ) = μ0 := by
      simpa [μ0, t, x] using
        (polarGauge_gaugeSqrtSumSq_add_fst_witness_of_fst_pos (xStar := xStar) hpos)
    have hineq := hμ.2 x
    have hineq' : ((μ0 : ℝ) : EReal) ≤ μ := by
      simpa [hwit.1, hwit.2, EReal.coe_mul] using hineq
    simpa using hineq'
  have hEq : polarGauge gaugeSqrtSumSq_add_fst xStar = (μ0 : EReal) :=
    le_antisymm hle hge
  simpa [μ0] using hEq

/-- Text 15.0.8 (polar gauge): the polar gauge of `gaugeSqrtSumSq_add_fst` agrees with the explicit
formula `polarGaugeSqrtSumSq_add_fst`. -/
theorem polarGauge_gaugeSqrtSumSq_add_fst :
    polarGauge gaugeSqrtSumSq_add_fst = polarGaugeSqrtSumSq_add_fst := by
  funext xStar
  by_cases hpos : 0 < xStar 0
  · have hmu := polarGauge_gaugeSqrtSumSq_add_fst_eq_mu0_of_fst_pos (xStar := xStar) hpos
    simp [polarGaugeSqrtSumSq_add_fst, hpos, hmu]
  · by_cases hzero : xStar 0 = 0 ∧ xStar 1 = 0
    · have hzero' : xStar = 0 := by
        funext i
        fin_cases i
        · simp [hzero.1]
        · simp [hzero.2]
      have hpol : polarGauge gaugeSqrtSumSq_add_fst xStar = 0 := by
        simpa [hzero'] using (polarGauge_zero gaugeSqrtSumSq_add_fst)
      simp [polarGaugeSqrtSumSq_add_fst, hzero, hpol]
    · by_cases hneg : xStar 0 < 0
      · have htop := polarGauge_gaugeSqrtSumSq_add_fst_eq_top_of_fst_lt_zero xStar hneg
        simp [polarGaugeSqrtSumSq_add_fst, hpos, hzero, htop]
      · have hx0_le : xStar 0 ≤ 0 := le_of_not_gt hpos
        have hx0_ge : 0 ≤ xStar 0 := le_of_not_gt hneg
        have hx0 : xStar 0 = 0 := by linarith
        have hx1 : xStar 1 ≠ 0 := by
          intro hx1
          exact hzero ⟨hx0, hx1⟩
        have htop :=
          polarGauge_gaugeSqrtSumSq_add_fst_eq_top_of_fst_eq_zero_snd_ne_zero xStar hx0 hx1
        simp [polarGaugeSqrtSumSq_add_fst, hx0, hx1, htop]

/-- Evaluate `gaugeSqrtSumSq_add_fst` on `![1,0]` and its negation. -/
lemma gaugeSqrtSumSq_add_fst_eval_vec10 :
    gaugeSqrtSumSq_add_fst (![1, 0]) = (2 : EReal) ∧
      gaugeSqrtSumSq_add_fst (-![1, 0]) = (0 : EReal) := by
  constructor
  ·
    norm_num [gaugeSqrtSumSq_add_fst, pow_two]
    norm_cast
  ·
    norm_num [gaugeSqrtSumSq_add_fst, pow_two]

/-- The witness `![1,0]` shows `gaugeSqrtSumSq_add_fst` is not even. -/
lemma gaugeSqrtSumSq_add_fst_not_even_via_vec10 :
    ¬ (∀ x : Fin 2 → ℝ, gaugeSqrtSumSq_add_fst (-x) = gaugeSqrtSumSq_add_fst x) := by
  intro h
  have hspec := h (![1, 0])
  rcases gaugeSqrtSumSq_add_fst_eval_vec10 with ⟨hpos, hneg⟩
  have hneg' : gaugeSqrtSumSq_add_fst (![(-1), 0]) = (0 : EReal) := by
    simpa using hneg
  have hspec' : gaugeSqrtSumSq_add_fst (![(-1), 0]) = gaugeSqrtSumSq_add_fst (![1, 0]) := by
    simpa using hspec
  have hcontr : (0 : EReal) = (2 : EReal) := by
    calc
      (0 : EReal) = gaugeSqrtSumSq_add_fst (![(-1), 0]) := by
        exact hneg'.symm
      _ = gaugeSqrtSumSq_add_fst (![1, 0]) := hspec'
      _ = (2 : EReal) := by
        exact hpos
  have hne : (0 : EReal) ≠ (2 : EReal) := by
    norm_cast
  exact hne hcontr

/-- Text 15.0.8 (not a norm): `gaugeSqrtSumSq_add_fst` is not even. -/
theorem gaugeSqrtSumSq_add_fst_not_even :
    ¬ (∀ x : Fin 2 → ℝ, gaugeSqrtSumSq_add_fst (-x) = gaugeSqrtSumSq_add_fst x) := by
  exact gaugeSqrtSumSq_add_fst_not_even_via_vec10

/-- Evaluate `polarGaugeSqrtSumSq_add_fst` on `![1,0]` and its negation. -/
lemma polarGaugeSqrtSumSq_add_fst_eval_vec10 :
    polarGaugeSqrtSumSq_add_fst (![1, 0]) = ((1 / 2 : ℝ) : EReal) ∧
      polarGaugeSqrtSumSq_add_fst (-![1, 0]) = (⊤ : EReal) := by
  have hpos : (0 : ℝ) < (1 : ℝ) := by norm_num
  have hnotpos : ¬ (0 : ℝ) < (-1 : ℝ) := by linarith
  constructor
  · simp [polarGaugeSqrtSumSq_add_fst, hpos, pow_two]
  · simp [polarGaugeSqrtSumSq_add_fst, hnotpos]

/-- The witness `![1,0]` shows `polarGaugeSqrtSumSq_add_fst` is not even. -/
lemma polarGaugeSqrtSumSq_add_fst_not_even_via_vec10 :
    ¬ (∀ xStar : Fin 2 → ℝ,
        polarGaugeSqrtSumSq_add_fst (-xStar) = polarGaugeSqrtSumSq_add_fst xStar) := by
  intro h
  have hspec := h (![1, 0])
  rcases polarGaugeSqrtSumSq_add_fst_eval_vec10 with ⟨hposval, hnegval⟩
  have hnegval' : polarGaugeSqrtSumSq_add_fst (![(-1), 0]) = (⊤ : EReal) := by
    simpa using hnegval
  have hspec' :
      polarGaugeSqrtSumSq_add_fst (![(-1), 0]) =
        polarGaugeSqrtSumSq_add_fst (![1, 0]) := by
    simpa using hspec
  have hcontr : (⊤ : EReal) = ((1 / 2 : ℝ) : EReal) := by
    calc
      (⊤ : EReal) = polarGaugeSqrtSumSq_add_fst (![(-1), 0]) := by
        exact hnegval'.symm
      _ = polarGaugeSqrtSumSq_add_fst (![1, 0]) := hspec'
      _ = ((1 / 2 : ℝ) : EReal) := by
        exact hposval
  exact (EReal.top_ne_coe (1 / 2)) hcontr

/-- Text 15.0.8 (not a norm): the polar gauge `polarGaugeSqrtSumSq_add_fst` is not even. -/
theorem polarGaugeSqrtSumSq_add_fst_not_even :
    ¬ (∀ xStar : Fin 2 → ℝ,
        polarGaugeSqrtSumSq_add_fst (-xStar) = polarGaugeSqrtSumSq_add_fst xStar) := by
  exact polarGaugeSqrtSumSq_add_fst_not_even_via_vec10

/-- Approximate the polar gauge inequality in ℝ with an ε-margin. -/
lemma inner_le_mul_polarGauge_real_eps {n : ℕ} {k : (Fin n → ℝ) → EReal} (hk : IsGauge k)
    (x xStar : Fin n → ℝ) (hx : k x ≠ ⊤) (hxStar : polarGauge k xStar ≠ ⊤) :
    ∀ ε > 0, (x ⬝ᵥ xStar : ℝ) ≤ ((polarGauge k xStar).toReal + ε) * (k x).toReal := by
  classical
  intro ε hε
  have hbot : polarGauge k xStar ≠ (⊥ : EReal) := polarGauge_ne_bot (k := k) xStar
  set a : ℝ := (polarGauge k xStar).toReal
  have ha : polarGauge k xStar = (a : EReal) := by
    simpa [a] using (EReal.coe_toReal (x := polarGauge k xStar) hxStar hbot).symm
  have hlt : polarGauge k xStar < ((a + ε : ℝ) : EReal) := by
    have : (a : EReal) < ((a + ε : ℝ) : EReal) := (EReal.coe_lt_coe_iff).2 (by linarith)
    simpa [ha] using this
  obtain ⟨μ', hμ'mem, hμ'lt⟩ := (sInf_lt_iff).1 hlt
  have hineq : ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ μ' * k x := hμ'mem.2 x
  have hineq' :
      ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ ((a + ε : ℝ) : EReal) * k x := by
    have hμ'le : μ' ≤ ((a + ε : ℝ) : EReal) := le_of_lt hμ'lt
    have hkx_nonneg : (0 : EReal) ≤ k x := hk.2.1 x
    exact le_trans hineq (mul_le_mul_of_nonneg_right hμ'le hkx_nonneg)
  have hkx_bot : k x ≠ (⊥ : EReal) := IsGauge.ne_bot hk x
  have hkx_eq : k x = ((k x).toReal : EReal) := by
    simpa using (EReal.coe_toReal (x := k x) hx hkx_bot).symm
  have hineq'' :
      ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ ((a + ε) * (k x).toReal : ℝ) := by
    have hineq'' := hineq'
    rw [hkx_eq, ← EReal.coe_mul] at hineq''
    exact hineq''
  have hreal : (x ⬝ᵥ xStar : ℝ) ≤ (a + ε) * (k x).toReal :=
    (EReal.coe_le_coe_iff).1 hineq''
  simpa [a] using hreal

/-- Letting ε→0 in the real inequality gives the sharp product bound. -/
lemma inner_le_mul_polarGauge_real {n : ℕ} {k : (Fin n → ℝ) → EReal} (hk : IsGauge k)
    (x xStar : Fin n → ℝ) (hx : k x ≠ ⊤) (hxStar : polarGauge k xStar ≠ ⊤) :
    (x ⬝ᵥ xStar : ℝ) ≤ (k x).toReal * (polarGauge k xStar).toReal := by
  classical
  set a : ℝ := (polarGauge k xStar).toReal
  set r : ℝ := (k x).toReal
  have hEps : ∀ ε > 0, (x ⬝ᵥ xStar : ℝ) ≤ (a + ε) * r := by
    intro ε hε
    simpa [a, r] using
      (inner_le_mul_polarGauge_real_eps (hk := hk) (x := x) (xStar := xStar) hx hxStar ε hε)
  have hr0 : 0 ≤ r := by
    have hkx_bot : k x ≠ (⊥ : EReal) := IsGauge.ne_bot hk x
    have hkx_eq : k x = (r : EReal) := by
      simpa [r] using (EReal.coe_toReal (x := k x) hx hkx_bot).symm
    have h0le : (0 : EReal) ≤ k x := hk.2.1 x
    have h0le' : (0 : EReal) ≤ (r : EReal) := by simpa [hkx_eq] using h0le
    exact (EReal.coe_le_coe_iff).1 h0le'
  by_cases hr0' : r = 0
  · have h := hEps 1 (by linarith)
    have h' : (x ⬝ᵥ xStar : ℝ) ≤ 0 := by simpa [hr0'] using h
    have h'' : (x ⬝ᵥ xStar : ℝ) ≤ r * a := by simpa [hr0'] using h'
    simpa [a, r] using h''
  · have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr0')
    have hle : (x ⬝ᵥ xStar : ℝ) ≤ a * r := by
      refine le_of_forall_pos_le_add ?_
      intro δ hδ
      have hδpos : 0 < δ / r := div_pos hδ hrpos
      have h := hEps (δ / r) hδpos
      have hcalc : (a + δ / r) * r = a * r + δ := by
        have hr0'' : r ≠ 0 := ne_of_gt hrpos
        calc
          (a + δ / r) * r = a * r + (δ / r) * r := by ring
          _ = a * r + δ := by
                field_simp [hr0'']
      have h' : (x ⬝ᵥ xStar : ℝ) ≤ a * r + δ := by simpa [hcalc] using h
      exact h'
    have hle' : (x ⬝ᵥ xStar : ℝ) ≤ r * a := by
      simpa [mul_comm] using hle
    simpa [a, r] using hle'

/-- Cast the real inequality back to `EReal`. -/
lemma inner_le_mul_polarGauge_via_toReal {n : ℕ} {k : (Fin n → ℝ) → EReal} (hk : IsGauge k)
    (x xStar : Fin n → ℝ) (hx : k x ≠ ⊤) (hxStar : polarGauge k xStar ≠ ⊤) :
    ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ k x * polarGauge k xStar := by
  classical
  have hreal :
      (x ⬝ᵥ xStar : ℝ) ≤ (k x).toReal * (polarGauge k xStar).toReal :=
    inner_le_mul_polarGauge_real (hk := hk) (x := x) (xStar := xStar) hx hxStar
  have hkx_bot : k x ≠ (⊥ : EReal) := IsGauge.ne_bot hk x
  have hpol_bot : polarGauge k xStar ≠ (⊥ : EReal) := polarGauge_ne_bot (k := k) xStar
  have hkx_eq : k x = ((k x).toReal : EReal) := by
    simpa using (EReal.coe_toReal (x := k x) hx hkx_bot).symm
  have hpol_eq : polarGauge k xStar = ((polarGauge k xStar).toReal : EReal) := by
    simpa using (EReal.coe_toReal (x := polarGauge k xStar) hxStar hpol_bot).symm
  have hrealE :
      ((x ⬝ᵥ xStar : ℝ) : EReal) ≤
        ((k x).toReal * (polarGauge k xStar).toReal : ℝ) :=
    (EReal.coe_le_coe_iff).2 hreal
  have hrealE' := hrealE
  rw [EReal.coe_mul] at hrealE'
  rw [← hkx_eq, ← hpol_eq] at hrealE'
  exact hrealE'

/-- Text 15.0.9: Let `k` be a gauge and let `kᵒ` be its polar gauge. Then for every `x` in the
effective domain of `k` and every `x⋆` in the effective domain of `kᵒ`,
`⟪x, x⋆⟫ ≤ k x * kᵒ x⋆`.

In this development, we represent `kᵒ` by `polarGauge k`, the pairing `⟪x, x⋆⟫` by `x ⬝ᵥ x⋆`,
and we model domain assumptions as `k x ≠ ⊤` and `polarGauge k x⋆ ≠ ⊤`.

If `k` is a norm (i.e. `k (-x) = k x` and `k` is finite and positive away from `0`), then
`|⟪x, x⋆⟫| ≤ k x * kᵒ x⋆` for all `x, x⋆`. -/
theorem inner_le_mul_polarGauge {n : ℕ} {k : (Fin n → ℝ) → EReal} (hk : IsGauge k)
    (x xStar : Fin n → ℝ) (hx : k x ≠ ⊤) (hxStar : polarGauge k xStar ≠ ⊤) :
    ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ k x * polarGauge k xStar := by
  exact inner_le_mul_polarGauge_via_toReal (hk := hk) (x := x) (xStar := xStar) hx hxStar

/-- Absolute-value form of the polar gauge inequality under norm-like hypotheses. -/
lemma abs_inner_le_mul_polarGauge_of_norm_like_casework {n : ℕ} {k : (Fin n → ℝ) → EReal}
    (hk : IsGauge k) (hk_even : ∀ x, k (-x) = k x) (hk_finite : ∀ x, k x ≠ ⊤)
    (hk_pos : ∀ x, x ≠ 0 → (0 : EReal) < k x) (x xStar : Fin n → ℝ) :
    ((|x ⬝ᵥ xStar| : ℝ) : EReal) ≤ k x * polarGauge k xStar := by
  classical
  by_cases htop : polarGauge k xStar = ⊤
  · by_cases hx0 : x = 0
    · subst hx0
      simp [hk.2.2.2, htop]
    · have hpos : (0 : EReal) < k x := hk_pos x hx0
      have hmul : k x * polarGauge k xStar = ⊤ := by
        simpa [htop] using (EReal.mul_top_of_pos (x := k x) hpos)
      simp [hmul]
  · have hpos_real :
        (x ⬝ᵥ xStar : ℝ) ≤ (k x).toReal * (polarGauge k xStar).toReal :=
      inner_le_mul_polarGauge_real (hk := hk) (x := x) (xStar := xStar) (hk_finite x) htop
    have hneg_real :
        ((-x) ⬝ᵥ xStar : ℝ) ≤ (k (-x)).toReal * (polarGauge k xStar).toReal :=
      inner_le_mul_polarGauge_real (hk := hk) (x := -x) (xStar := xStar)
        (hk_finite (-x)) htop
    have hneg_real' :
        -(x ⬝ᵥ xStar : ℝ) ≤ (k x).toReal * (polarGauge k xStar).toReal := by
      simpa [hk_even] using hneg_real
    have hneg_bound :
        -((k x).toReal * (polarGauge k xStar).toReal) ≤ (x ⬝ᵥ xStar : ℝ) := by
      nlinarith [hneg_real']
    have habs :
        |x ⬝ᵥ xStar| ≤ (k x).toReal * (polarGauge k xStar).toReal :=
      (abs_le).2 ⟨hneg_bound, hpos_real⟩
    have hkx_bot : k x ≠ (⊥ : EReal) := IsGauge.ne_bot hk x
    have hpol_bot : polarGauge k xStar ≠ (⊥ : EReal) := polarGauge_ne_bot (k := k) xStar
    have hkx_eq : k x = ((k x).toReal : EReal) := by
      simpa using (EReal.coe_toReal (x := k x) (hk_finite x) hkx_bot).symm
    have hpol_eq : polarGauge k xStar = ((polarGauge k xStar).toReal : EReal) := by
      simpa using (EReal.coe_toReal (x := polarGauge k xStar) htop hpol_bot).symm
    have habsE :
        ((|x ⬝ᵥ xStar| : ℝ) : EReal) ≤
          ((k x).toReal * (polarGauge k xStar).toReal : ℝ) :=
      (EReal.coe_le_coe_iff).2 habs
    have habsE' := habsE
    rw [EReal.coe_mul] at habsE'
    rw [← hkx_eq, ← hpol_eq] at habsE'
    exact habsE'

theorem abs_inner_le_mul_polarGauge_of_norm_like {n : ℕ} {k : (Fin n → ℝ) → EReal} (hk : IsGauge k)
    (hk_even : ∀ x, k (-x) = k x) (hk_finite : ∀ x, k x ≠ ⊤)
    (hk_pos : ∀ x, x ≠ 0 → (0 : EReal) < k x) (x xStar : Fin n → ℝ) :
    ((|x ⬝ᵥ xStar| : ℝ) : EReal) ≤ k x * polarGauge k xStar := by
  exact
    abs_inner_le_mul_polarGauge_of_norm_like_casework (hk := hk) (hk_even := hk_even)
      (hk_finite := hk_finite) (hk_pos := hk_pos) (x := x) (xStar := xStar)

/-- Feasible multipliers for the inf-definition in Text 15.0.10. -/
def innerMulFeasible {n : ℕ} {J : Set (Fin n → ℝ)} (j : J → EReal) (x : Fin n → ℝ) :
    Set EReal :=
  {μ : EReal | 0 ≤ μ ∧ ∀ y : J, ((x ⬝ᵥ (y : Fin n → ℝ) : ℝ) : EReal) ≤ μ * j y}

/-- Candidate gauge defined by infimum of feasible multipliers. -/
noncomputable def innerMulGauge {n : ℕ} {J : Set (Fin n → ℝ)} (j : J → EReal)
    (x : Fin n → ℝ) : EReal :=
  sInf (innerMulFeasible (J := J) j x)

/-- The infimum definition yields a nonnegative value. -/
lemma innerMulGauge_nonneg {n : ℕ} {J : Set (Fin n → ℝ)} (j : J → EReal) (x : Fin n → ℝ) :
    (0 : EReal) ≤ innerMulGauge (J := J) j x := by
  unfold innerMulGauge innerMulFeasible
  refine le_sInf ?_
  intro μ hμ
  exact hμ.1

/-- The infimum definition yields zero at the origin. -/
lemma innerMulGauge_zero {n : ℕ} {J : Set (Fin n → ℝ)} (j : J → EReal) :
    innerMulGauge (J := J) j (0 : Fin n → ℝ) = 0 := by
  classical
  have h0mem : (0 : EReal) ∈ innerMulFeasible (J := J) j (0 : Fin n → ℝ) := by
    refine ⟨le_rfl, ?_⟩
    intro y
    simp
  have hle : innerMulGauge (J := J) j (0 : Fin n → ℝ) ≤ 0 := by
    unfold innerMulGauge
    exact sInf_le h0mem
  have hge : (0 : EReal) ≤ innerMulGauge (J := J) j (0 : Fin n → ℝ) :=
    innerMulGauge_nonneg (J := J) (j := j) (x := 0)
  exact le_antisymm hle hge

/-- If `r ≥ 0` and `a ≤ (μ + ε) * r` for all `ε > 0`, then `a ≤ μ * r`. -/
lemma le_mul_of_forall_pos_add_mul {a μ r : ℝ} (hr : 0 ≤ r)
    (h : ∀ ε > 0, a ≤ (μ + ε) * r) : a ≤ μ * r := by
  by_cases hr0 : r = 0
  · subst hr0
    have hε := h 1 (by linarith)
    simpa using hε
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    refine le_of_forall_pos_le_add ?_
    intro δ hδ
    have hε : 0 < δ / r := div_pos hδ hrpos
    have h' := h (δ / r) hε
    have hcalc : (μ + δ / r) * r = μ * r + δ := by
      have hr0' : r ≠ 0 := hr0
      calc
        (μ + δ / r) * r = μ * r + (δ / r) * r := by ring
        _ = μ * r + δ * r / r := by
              simp [div_mul_eq_mul_div]
        _ = μ * r + δ := by
              field_simp [hr0']
    have h'' : a ≤ μ * r + δ := by simpa [hcalc] using h'
    exact h''

/-- If `h` is nonnegative and provides a feasible multiplier on `H`, then `innerMulGauge ≤ h` on `H`
and hence `innerMulGauge` is finite on `H`. -/
lemma innerMulGauge_le_h_on_H {n : ℕ} {H J : Set (Fin n → ℝ)} (h : H → EReal) (j : J → EReal)
    (h_nonneg : ∀ x : H, (0 : EReal) ≤ h x)
    (h_ne_top : ∀ x : H, h x ≠ ⊤)
    (hineq : ∀ x : H, ∀ y : J,
      ((x.1 ⬝ᵥ (y : Fin n → ℝ) : ℝ) : EReal) ≤ h x * j y) :
    ∀ x : H,
      innerMulGauge (J := J) j x.1 ≤ h x ∧ innerMulGauge (J := J) j x.1 ≠ ⊤ := by
  intro x
  have hmem : h x ∈ innerMulFeasible (J := J) j x.1 := by
    refine ⟨h_nonneg x, ?_⟩
    intro y
    simpa using hineq x y
  have hle : innerMulGauge (J := J) j x.1 ≤ h x := by
    unfold innerMulGauge
    exact sInf_le hmem
  have hne : innerMulGauge (J := J) j x.1 ≠ ⊤ := by
    intro htop
    have htop' : (⊤ : EReal) ≤ h x := by simpa [htop] using hle
    have htop'' : h x = ⊤ := (top_le_iff).1 htop'
    exact (h_ne_top x) htop''
  exact ⟨hle, hne⟩

/-- On the effective domain, `innerMulGauge` satisfies the defining inequality. -/
lemma inner_le_innerMulGauge_mul_j_of_ne_top {n : ℕ} {J : Set (Fin n → ℝ)} (j : J → EReal)
    (j_nonneg : ∀ y : J, (0 : EReal) ≤ j y) (j_ne_top : ∀ y : J, j y ≠ ⊤) :
    ∀ x, innerMulGauge (J := J) j x ≠ ⊤ → ∀ y : J,
      ((x ⬝ᵥ (y : Fin n → ℝ) : ℝ) : EReal) ≤ innerMulGauge (J := J) j x * j y := by
  classical
  intro x hx y
  set a : ℝ := (innerMulGauge (J := J) j x).toReal
  set b : ℝ := (j y).toReal
  have hk_nonneg : (0 : EReal) ≤ innerMulGauge (J := J) j x :=
    innerMulGauge_nonneg (J := J) (j := j) (x := x)
  have hk_bot : innerMulGauge (J := J) j x ≠ (⊥ : EReal) := by
    intro hbot
    have h0le := hk_nonneg
    rw [hbot] at h0le
    have h0eq : (0 : EReal) = (⊥ : EReal) := (le_bot_iff).1 h0le
    have h0ne : (0 : EReal) ≠ (⊥ : EReal) := by simp
    exact h0ne h0eq
  have ha : innerMulGauge (J := J) j x = (a : EReal) := by
    simpa [a] using
      (EReal.coe_toReal (x := innerMulGauge (J := J) j x) hx hk_bot).symm
  have hj_bot : j y ≠ (⊥ : EReal) := by
    intro hbot
    have h0le : (0 : EReal) ≤ j y := j_nonneg y
    have h0le' := h0le
    rw [hbot] at h0le'
    have h0eq : (0 : EReal) = (⊥ : EReal) := (le_bot_iff).1 h0le'
    have h0ne : (0 : EReal) ≠ (⊥ : EReal) := by simp
    exact h0ne h0eq
  have hb : j y = (b : EReal) := by
    simpa [b] using (EReal.coe_toReal (x := j y) (j_ne_top y) hj_bot).symm
  have hb0 : 0 ≤ b := by
    have h0le : (0 : EReal) ≤ j y := j_nonneg y
    have h0le' : (0 : EReal) ≤ (b : EReal) := by simpa [hb] using h0le
    exact (EReal.coe_le_coe_iff).1 h0le'
  have hEps : ∀ ε > 0, (x ⬝ᵥ (y : Fin n → ℝ) : ℝ) ≤ (a + ε) * b := by
    intro ε hε
    have hlt : innerMulGauge (J := J) j x < ((a + ε : ℝ) : EReal) := by
      have : (a : EReal) < ((a + ε : ℝ) : EReal) :=
        (EReal.coe_lt_coe_iff).2 (by linarith)
      simpa [ha] using this
    obtain ⟨μ, hμmem, hμlt⟩ := (sInf_lt_iff).1 hlt
    have hineq : ((x ⬝ᵥ (y : Fin n → ℝ) : ℝ) : EReal) ≤ μ * j y := hμmem.2 y
    have hμle : μ ≤ ((a + ε : ℝ) : EReal) := le_of_lt hμlt
    have hineq' :
        ((x ⬝ᵥ (y : Fin n → ℝ) : ℝ) : EReal) ≤ ((a + ε : ℝ) : EReal) * j y := by
      exact le_trans hineq (mul_le_mul_of_nonneg_right hμle (j_nonneg y))
    have hineq'' :
        ((x ⬝ᵥ (y : Fin n → ℝ) : ℝ) : EReal) ≤ (((a + ε) * b : ℝ) : EReal) := by
      simpa [hb, EReal.coe_mul, mul_comm, mul_left_comm, mul_assoc] using hineq'
    have hreal : (x ⬝ᵥ (y : Fin n → ℝ) : ℝ) ≤ (a + ε) * b :=
      (EReal.coe_le_coe_iff).1 hineq''
    simpa using hreal
  have hdot : (x ⬝ᵥ (y : Fin n → ℝ) : ℝ) ≤ a * b :=
    le_mul_of_forall_pos_add_mul hb0 hEps
  have hdotE : ((x ⬝ᵥ (y : Fin n → ℝ) : ℝ) : EReal) ≤ ((a * b : ℝ) : EReal) := by
    exact_mod_cast hdot
  have hmulE : ((a * b : ℝ) : EReal) = innerMulGauge (J := J) j x * j y := by
    calc
      ((a * b : ℝ) : EReal) = (a : EReal) * (b : EReal) := by
        simp [EReal.coe_mul]
      _ = innerMulGauge (J := J) j x * j y := by
        simp [ha, hb, mul_comm]
  simpa [hmulE] using hdotE

/-- The inner-multiplier gauge never attains `⊥`. -/
lemma innerMulGauge_ne_bot {n : ℕ} {J : Set (Fin n → ℝ)} (j : J → EReal) (x : Fin n → ℝ) :
    innerMulGauge (J := J) j x ≠ (⊥ : EReal) := by
  intro hbot
  have h0le : (0 : EReal) ≤ innerMulGauge (J := J) j x :=
    innerMulGauge_nonneg (J := J) (j := j) (x := x)
  have h0le' := h0le
  rw [hbot] at h0le'
  have h0eq : (0 : EReal) = (⊥ : EReal) := (le_bot_iff).1 h0le'
  exact (by simp : (0 : EReal) ≠ (⊥ : EReal)) h0eq

/-- Scaling a feasible multiplier scales feasibility for the scaled vector. -/
lemma innerMulFeasible_smul {n : ℕ} {J : Set (Fin n → ℝ)} (j : J → EReal)
    {x : Fin n → ℝ} {μ : EReal} (hμ : μ ∈ innerMulFeasible (J := J) j x) {t : ℝ}
    (ht : 0 ≤ t) :
    ((t : ℝ) : EReal) * μ ∈ innerMulFeasible (J := J) j (t • x) := by
  refine ⟨?_, ?_⟩
  · exact EReal.mul_nonneg (by exact_mod_cast ht) hμ.1
  · intro y
    have hineq : ((x ⬝ᵥ (y : Fin n → ℝ) : ℝ) : EReal) ≤ μ * j y := hμ.2 y
    have hmul :
        ((t : ℝ) : EReal) * ((x ⬝ᵥ (y : Fin n → ℝ) : ℝ) : EReal) ≤
          ((t : ℝ) : EReal) * (μ * j y) :=
      mul_le_mul_of_nonneg_left hineq (by exact_mod_cast ht)
    have hdot :
        ((t • x ⬝ᵥ (y : Fin n → ℝ) : ℝ) : EReal) =
          ((t : ℝ) : EReal) * ((x ⬝ᵥ (y : Fin n → ℝ) : ℝ) : EReal) := by
      simp [smul_eq_mul, EReal.coe_mul]
    have hmul' :
        ((t • x ⬝ᵥ (y : Fin n → ℝ) : ℝ) : EReal) ≤
          ((t : ℝ) : EReal) * (μ * j y) := by
      simpa [hdot] using hmul
    simpa [mul_assoc] using hmul'

/-- The inner-multiplier gauge is subadditive. -/
lemma innerMulGauge_add_le {n : ℕ} {J : Set (Fin n → ℝ)} (j : J → EReal)
    (x z : Fin n → ℝ) :
    innerMulGauge (J := J) j (x + z) ≤
      innerMulGauge (J := J) j x + innerMulGauge (J := J) j z := by
  classical
  set k : (Fin n → ℝ) → EReal := innerMulGauge (J := J) j
  by_cases hx_top : k x = ⊤
  ·
    have hz_bot : k z ≠ (⊥ : EReal) :=
      innerMulGauge_ne_bot (J := J) (j := j) z
    calc
      k (x + z) ≤ (⊤ : EReal) := le_top
      _ = (⊤ : EReal) + k z := by
            simpa using (EReal.top_add_of_ne_bot hz_bot).symm
      _ = k x + k z := by simp [k, hx_top]
  by_cases hz_top : k z = ⊤
  ·
    have hx_bot : k x ≠ (⊥ : EReal) :=
      innerMulGauge_ne_bot (J := J) (j := j) x
    calc
      k (x + z) ≤ (⊤ : EReal) := le_top
      _ = k x + (⊤ : EReal) := by
            simpa using (EReal.add_top_of_ne_bot (x := k x) hx_bot).symm
      _ = k x + k z := by simp [k, hz_top]
  set a : ℝ := (k x).toReal
  set b : ℝ := (k z).toReal
  have hkx_bot : k x ≠ (⊥ : EReal) := innerMulGauge_ne_bot (J := J) (j := j) x
  have hkz_bot : k z ≠ (⊥ : EReal) := innerMulGauge_ne_bot (J := J) (j := j) z
  have ha : k x = (a : EReal) := by
    simpa [a] using (EReal.coe_toReal (x := k x) hx_top hkx_bot).symm
  have hb : k z = (b : EReal) := by
    simpa [b] using (EReal.coe_toReal (x := k z) hz_top hkz_bot).symm
  have hle_eps : ∀ ε > 0, k (x + z) ≤ ((a + b + ε : ℝ) : EReal) := by
    intro ε hε
    have hltx : k x < ((a + ε / 2 : ℝ) : EReal) := by
      have : (a : EReal) < ((a + ε / 2 : ℝ) : EReal) :=
        (EReal.coe_lt_coe_iff).2 (by linarith)
      simpa [ha] using this
    obtain ⟨μx, hμx_mem, hμx_lt⟩ := (sInf_lt_iff).1 hltx
    have hltz : k z < ((b + ε / 2 : ℝ) : EReal) := by
      have : (b : EReal) < ((b + ε / 2 : ℝ) : EReal) :=
        (EReal.coe_lt_coe_iff).2 (by linarith)
      simpa [hb] using this
    obtain ⟨μz, hμz_mem, hμz_lt⟩ := (sInf_lt_iff).1 hltz
    have hμsum_mem : μx + μz ∈ innerMulFeasible (J := J) j (x + z) := by
      refine ⟨add_nonneg hμx_mem.1 hμz_mem.1, ?_⟩
      intro y
      have hdotE :
          (((x + z) ⬝ᵥ (y : Fin n → ℝ) : ℝ) : EReal) =
            (((x ⬝ᵥ (y : Fin n → ℝ) : ℝ) : EReal)) +
              (((z ⬝ᵥ (y : Fin n → ℝ) : ℝ) : EReal)) := by
        simp [EReal.coe_add]
      have hle :
          (((x ⬝ᵥ (y : Fin n → ℝ) : ℝ) : EReal)) +
              (((z ⬝ᵥ (y : Fin n → ℝ) : ℝ) : EReal)) ≤
            μx * j y + μz * j y :=
        add_le_add (hμx_mem.2 y) (hμz_mem.2 y)
      have hle' :
          (((x + z) ⬝ᵥ (y : Fin n → ℝ) : ℝ) : EReal) ≤
            μx * j y + μz * j y := by
        simpa [hdotE] using hle
      have hsum :
          μx * j y + μz * j y = (μx + μz) * j y := by
        simpa using
          (EReal.right_distrib_of_nonneg (a := μx) (b := μz) (c := j y)
            hμx_mem.1 hμz_mem.1).symm
      simpa [hsum] using hle'
    have hk_le : k (x + z) ≤ μx + μz := by
      have : innerMulGauge (J := J) j (x + z) ≤ μx + μz := by
        unfold innerMulGauge
        exact sInf_le hμsum_mem
      simpa [k] using this
    have hsum_lt :
        μx + μz < ((a + b + ε : ℝ) : EReal) := by
      have hsum_lt' :
          μx + μz <
            ((a + ε / 2 : ℝ) : EReal) + ((b + ε / 2 : ℝ) : EReal) := by
        have hμz_bot : μz ≠ (⊥ : EReal) :=
          ne_bot_of_le_ne_bot (hb := by simp) (hab := hμz_mem.1)
        have htop : ((b + ε / 2 : ℝ) : EReal) ≠ ⊤ := by
          simpa using (EReal.coe_ne_top (b + ε / 2))
        exact
          EReal.add_lt_add_of_lt_of_le hμx_lt (le_of_lt hμz_lt) hμz_bot htop
      have hsumE :
          ((a : EReal) + ((ε / 2 : ℝ) : EReal)) +
              ((b : EReal) + ((ε / 2 : ℝ) : EReal)) =
            ((a + b + ε : ℝ) : EReal) := by
        have hsum : (a + ε / 2) + (b + ε / 2) = a + b + ε := by ring
        calc
          ((a : EReal) + ((ε / 2 : ℝ) : EReal)) +
              ((b : EReal) + ((ε / 2 : ℝ) : EReal)) =
              ((a + ε / 2 : ℝ) : EReal) + ((b + ε / 2 : ℝ) : EReal) := by
                simp [EReal.coe_add]
          _ = ((a + ε / 2 + (b + ε / 2) : ℝ) : EReal) := by
                simp [EReal.coe_add, add_assoc]
          _ = ((a + b + ε : ℝ) : EReal) := by
                exact_mod_cast hsum
      have hsum_lt'' :
          μx + μz <
            ((a : EReal) + ((ε / 2 : ℝ) : EReal)) +
              ((b : EReal) + ((ε / 2 : ℝ) : EReal)) := by
        simpa [EReal.coe_add, add_assoc, add_left_comm, add_comm] using hsum_lt'
      simpa [hsumE] using hsum_lt''
    exact le_trans hk_le (le_of_lt hsum_lt)
  have hkxz_top : k (x + z) ≠ ⊤ := by
    intro htop
    have hle := hle_eps 1 (by linarith)
    have hle' : (⊤ : EReal) ≤ ((a + b + 1 : ℝ) : EReal) := by
      simpa [k, htop] using hle
    exact (not_le_of_gt (EReal.coe_lt_top (a + b + 1))) hle'
  have hkxz_bot : k (x + z) ≠ (⊥ : EReal) :=
    innerMulGauge_ne_bot (J := J) (j := j) (x + z)
  set c : ℝ := (k (x + z)).toReal
  have hc : k (x + z) = (c : EReal) := by
    simpa [c] using (EReal.coe_toReal (x := k (x + z)) hkxz_top hkxz_bot).symm
  have hcle : c ≤ a + b := by
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    have hle := hle_eps ε hε
    have hle' : (c : EReal) ≤ ((a + b + ε : ℝ) : EReal) := by
      simpa [hc] using hle
    have hle'' : c ≤ a + b + ε := (EReal.coe_le_coe_iff).1 hle'
    simpa [add_assoc] using hle''
  have hleE : (c : EReal) ≤ ((a + b : ℝ) : EReal) :=
    (EReal.coe_le_coe_iff).2 hcle
  calc
    k (x + z) = (c : EReal) := hc
    _ ≤ ((a + b : ℝ) : EReal) := hleE
    _ = k x + k z := by
      calc
        ((a + b : ℝ) : EReal) = (a : EReal) + (b : EReal) := by
          simp [EReal.coe_add]
        _ = k x + k z := by simp [ha, hb]

/-- The inner-multiplier gauge is positively homogeneous. -/
lemma innerMulGauge_posHom {n : ℕ} {J : Set (Fin n → ℝ)} (j : J → EReal) :
    PositivelyHomogeneous (innerMulGauge (J := J) j) := by
  classical
  set k : (Fin n → ℝ) → EReal := innerMulGauge (J := J) j
  have hle_inv :
      ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 < t →
        ((t⁻¹ : ℝ) : EReal) * k (t • x) ≤ k x := by
    intro x t ht
    have ht0 : 0 ≤ t := le_of_lt ht
    have htinv0 : 0 ≤ (t⁻¹ : ℝ) := inv_nonneg.mpr ht0
    change
        ((t⁻¹ : ℝ) : EReal) * k (t • x) ≤
          sInf (innerMulFeasible (J := J) j x)
    refine le_sInf ?_
    intro μ hμ
    have hμ' : ((t : ℝ) : EReal) * μ ∈ innerMulFeasible (J := J) j (t • x) :=
      innerMulFeasible_smul (J := J) (j := j) (x := x) (μ := μ) hμ ht0
    have hk_le : k (t • x) ≤ ((t : ℝ) : EReal) * μ := by
      simpa [k, innerMulGauge] using (sInf_le hμ')
    have hmul :
        ((t⁻¹ : ℝ) : EReal) * k (t • x) ≤
          ((t⁻¹ : ℝ) : EReal) * (((t : ℝ) : EReal) * μ) :=
      mul_le_mul_of_nonneg_left hk_le (by exact_mod_cast htinv0)
    simpa [mul_assoc, section13_mul_inv_mul_cancel_pos_real (a := t) ht] using hmul
  intro x t ht
  have ht0 : 0 ≤ t := le_of_lt ht
  have hle_left : k (t • x) ≤ ((t : ℝ) : EReal) * k x := by
    have hmul :
        ((t : ℝ) : EReal) * (((t⁻¹ : ℝ) : EReal) * k (t • x)) ≤
          ((t : ℝ) : EReal) * k x :=
      mul_le_mul_of_nonneg_left (hle_inv x t ht) (by exact_mod_cast ht0)
    simpa [mul_assoc, section13_mul_mul_inv_cancel_pos_real (a := t) ht] using hmul
  have hle_right : ((t : ℝ) : EReal) * k x ≤ k (t • x) := by
    have htinv : 0 < (t⁻¹ : ℝ) := inv_pos.mpr ht
    have hle_inv' :
        (((t⁻¹)⁻¹ : ℝ) : EReal) * k ((t⁻¹) • (t • x)) ≤ k (t • x) :=
      hle_inv (t • x) (t⁻¹) htinv
    simpa [smul_smul, inv_mul_cancel, ht.ne', one_smul] using hle_inv'
  exact le_antisymm hle_left hle_right

/-- The inner-multiplier gauge is a gauge. -/
lemma innerMulGauge_isGauge {n : ℕ} {J : Set (Fin n → ℝ)} (j : J → EReal) :
    IsGauge (innerMulGauge (J := J) j) := by
  classical
  set k : (Fin n → ℝ) → EReal := innerMulGauge (J := J) j
  have hnotbot : ∀ x, k x ≠ (⊥ : EReal) := by
    intro x
    exact innerMulGauge_ne_bot (J := J) (j := j) x
  have hconv : ConvexFunction k :=
    convex_of_subadditive_posHom (hpos := innerMulGauge_posHom (J := J) (j := j))
      (hsub := by
        intro x y
        simpa [k] using innerMulGauge_add_le (J := J) (j := j) x y)
      (hnotbot := hnotbot)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [ConvexFunction] using hconv
  · intro x
    simpa [k] using innerMulGauge_nonneg (J := J) (j := j) (x := x)
  · intro x r hr
    by_cases hr0 : r = 0
    · simp [hr0, k, innerMulGauge_zero]
    · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
      simpa [k] using (innerMulGauge_posHom (J := J) (j := j) x r hrpos)
  · simpa [k] using innerMulGauge_zero (J := J) (j := j)

/-- Epigraph as an intersection of halfspaces for `innerMulGauge`. -/
lemma epigraph_innerMulGauge_eq_inter_iInter_halfspaces {n : ℕ} {J : Set (Fin n → ℝ)}
    (j : J → EReal) (j_nonneg : ∀ y : J, (0 : EReal) ≤ j y)
    (j_ne_top : ∀ y : J, j y ≠ ⊤) :
    epigraph (S := (Set.univ : Set (Fin n → ℝ))) (innerMulGauge (J := J) j) =
      {p : (Fin n → ℝ) × ℝ | 0 ≤ p.2} ∩
        ⋂ y : J, {p : (Fin n → ℝ) × ℝ | dotProduct p.1 (y : Fin n → ℝ) ≤
          p.2 * (j y).toReal} := by
  classical
  ext p
  rcases p with ⟨x, μ⟩
  constructor
  · intro hp
    have hx_le : innerMulGauge (J := J) j x ≤ (μ : EReal) :=
      (mem_epigraph_univ_iff (f := innerMulGauge (J := J) j) (x := x) (μ := μ)).1 hp
    have hμ0E : (0 : EReal) ≤ (μ : EReal) :=
      le_trans (innerMulGauge_nonneg (J := J) (j := j) (x := x)) hx_le
    have hμ0 : 0 ≤ μ := (EReal.coe_le_coe_iff).1 hμ0E
    have hx_ne_top : innerMulGauge (J := J) j x ≠ ⊤ := by
      intro htop
      have hx_le' := hx_le
      rw [htop] at hx_le'
      exact (not_le_of_gt (EReal.coe_lt_top μ)) hx_le'
    refine ⟨hμ0, ?_⟩
    refine Set.mem_iInter.2 ?_
    intro y
    have hineq :
        ((x ⬝ᵥ (y : Fin n → ℝ) : ℝ) : EReal) ≤
          innerMulGauge (J := J) j x * j y :=
      inner_le_innerMulGauge_mul_j_of_ne_top (J := J) (j := j) j_nonneg j_ne_top x hx_ne_top y
    have hineq' :
        ((x ⬝ᵥ (y : Fin n → ℝ) : ℝ) : EReal) ≤ (μ : EReal) * j y := by
      exact le_trans hineq (mul_le_mul_of_nonneg_right hx_le (j_nonneg y))
    have hj_bot : j y ≠ (⊥ : EReal) := by
      intro hbot
      have h0le : (0 : EReal) ≤ j y := j_nonneg y
      have h0le' := h0le
      rw [hbot] at h0le'
      have h0eq : (0 : EReal) = (⊥ : EReal) := (le_bot_iff).1 h0le'
      exact (by simp : (0 : EReal) ≠ (⊥ : EReal)) h0eq
    set b : ℝ := (j y).toReal
    have hb : j y = (b : EReal) := by
      simpa [b] using (EReal.coe_toReal (x := j y) (j_ne_top y) hj_bot).symm
    have hineq'' :
        ((x ⬝ᵥ (y : Fin n → ℝ) : ℝ) : EReal) ≤ ((μ * b : ℝ) : EReal) := by
      simpa [hb, EReal.coe_mul] using hineq'
    have hreal : dotProduct x (y : Fin n → ℝ) ≤ μ * b :=
      (EReal.coe_le_coe_iff).1 hineq''
    simpa [b] using hreal
  · intro hp
    rcases hp with ⟨hμ0, hp⟩
    have hμ0E : (0 : EReal) ≤ (μ : EReal) := by
      exact_mod_cast hμ0
    have hineq_real :
        ∀ y : J, dotProduct x (y : Fin n → ℝ) ≤ μ * (j y).toReal :=
      Set.mem_iInter.1 hp
    have hμmem : (μ : EReal) ∈ innerMulFeasible (J := J) j x := by
      refine ⟨hμ0E, ?_⟩
      intro y
      have hj_bot : j y ≠ (⊥ : EReal) := by
        intro hbot
        have h0le : (0 : EReal) ≤ j y := j_nonneg y
        have h0le' := h0le
        rw [hbot] at h0le'
        have h0eq : (0 : EReal) = (⊥ : EReal) := (le_bot_iff).1 h0le'
        exact (by simp : (0 : EReal) ≠ (⊥ : EReal)) h0eq
      set b : ℝ := (j y).toReal
      have hb : j y = (b : EReal) := by
        simpa [b] using (EReal.coe_toReal (x := j y) (j_ne_top y) hj_bot).symm
      have hreal : dotProduct x (y : Fin n → ℝ) ≤ μ * b := by
        simpa [b] using hineq_real y
      have hE : ((x ⬝ᵥ (y : Fin n → ℝ) : ℝ) : EReal) ≤ ((μ * b : ℝ) : EReal) := by
        exact_mod_cast hreal
      have hmulE :
          ((μ * b : ℝ) : EReal) = (μ : EReal) * j y := by
        simp [hb, EReal.coe_mul]
      simpa [hmulE] using hE
    have hle : innerMulGauge (J := J) j x ≤ (μ : EReal) := by
      unfold innerMulGauge
      exact sInf_le hμmem
    exact (mem_epigraph_univ_iff (f := innerMulGauge (J := J) j) (x := x) (μ := μ)).2 hle

/-- The epigraph of `innerMulGauge` is closed. -/
lemma isClosed_epigraph_innerMulGauge {n : ℕ} {J : Set (Fin n → ℝ)} (j : J → EReal)
    (j_nonneg : ∀ y : J, (0 : EReal) ≤ j y) (j_ne_top : ∀ y : J, j y ≠ ⊤) :
    IsClosed (epigraph (S := (Set.univ : Set (Fin n → ℝ))) (innerMulGauge (J := J) j)) := by
  classical
  have hclosed_nonneg : IsClosed {p : (Fin n → ℝ) × ℝ | 0 ≤ p.2} := by
    simpa using (isClosed_le continuous_const continuous_snd)
  have hclosed_half :
      ∀ y : J,
        IsClosed {p : (Fin n → ℝ) × ℝ |
          dotProduct p.1 (y : Fin n → ℝ) ≤ p.2 * (j y).toReal} := by
    intro y
    have hcont_left :
        Continuous (fun p : (Fin n → ℝ) × ℝ => dotProduct p.1 (y : Fin n → ℝ)) := by
      have hcont' : Continuous (fun x : Fin n → ℝ => (y : Fin n → ℝ) ⬝ᵥ x) :=
        continuous_dotProduct_const (x := (y : Fin n → ℝ))
      have hcont'' :
          Continuous (fun p : (Fin n → ℝ) × ℝ => (y : Fin n → ℝ) ⬝ᵥ p.1) :=
        hcont'.comp continuous_fst
      simpa [dotProduct_comm] using hcont''
    have hcont_right :
        Continuous (fun p : (Fin n → ℝ) × ℝ => p.2 * (j y).toReal) :=
      continuous_snd.mul continuous_const
    simpa using (isClosed_le hcont_left hcont_right)
  have hclosed_iInter :
      IsClosed (⋂ y : J,
        {p : (Fin n → ℝ) × ℝ |
          dotProduct p.1 (y : Fin n → ℝ) ≤ p.2 * (j y).toReal}) :=
    isClosed_iInter hclosed_half
  have hclosed_inter :
      IsClosed
        ({p : (Fin n → ℝ) × ℝ | 0 ≤ p.2} ∩
          ⋂ y : J,
            {p : (Fin n → ℝ) × ℝ |
              dotProduct p.1 (y : Fin n → ℝ) ≤ p.2 * (j y).toReal}) :=
    hclosed_nonneg.inter hclosed_iInter
  simpa
    [epigraph_innerMulGauge_eq_inter_iInter_halfspaces (J := J) (j := j) j_nonneg j_ne_top]
    using hclosed_inter

end Section15
end Chap03
