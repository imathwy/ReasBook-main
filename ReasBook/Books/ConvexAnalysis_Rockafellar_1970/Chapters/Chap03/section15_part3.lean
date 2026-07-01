/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yijie Wang, Yunxi Duan, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section13_part4

section Chap03
section Section15

open scoped BigOperators
open scoped Pointwise
open scoped RealInnerProductSpace

/-- The polar gauge of `innerMulGauge` is bounded by `j` on `J`. -/
lemma polarGauge_innerMulGauge_le_j_on_J {n : ℕ} {J : Set (Fin n → ℝ)} (j : J → EReal)
    (j_nonneg : ∀ y : J, (0 : EReal) ≤ j y) (j_ne_top : ∀ y : J, j y ≠ ⊤) :
    ∀ y : J, polarGauge (innerMulGauge (J := J) j) (y : Fin n → ℝ) ≤ j y ∧
      polarGauge (innerMulGauge (J := J) j) (y : Fin n → ℝ) ≠ ⊤ := by
  classical
  intro y
  set k : (Fin n → ℝ) → EReal := innerMulGauge (J := J) j
  by_cases hy0 : j y = 0
  · have hfeas : ∀ ε : ℝ, ε > 0 →
        (ε : EReal) ∈
          {μ : EReal |
            0 ≤ μ ∧
              ∀ x : Fin n → ℝ,
                ((x ⬝ᵥ (y : Fin n → ℝ) : ℝ) : EReal) ≤ μ * k x} := by
      intro ε hε
      refine ⟨?_, ?_⟩
      · exact_mod_cast (le_of_lt hε)
      · intro x
        by_cases hkx_top : k x = ⊤
        · have hmul : ((ε : ℝ) : EReal) * k x = ⊤ := by
            simpa [hkx_top] using (EReal.coe_mul_top_of_pos (x := ε) hε)
          simp [hmul]
        · have hineq :
            ((x ⬝ᵥ (y : Fin n → ℝ) : ℝ) : EReal) ≤ k x * j y :=
            inner_le_innerMulGauge_mul_j_of_ne_top (J := J) (j := j) j_nonneg j_ne_top x hkx_top y
          have hineq0 :
              ((x ⬝ᵥ (y : Fin n → ℝ) : ℝ) : EReal) ≤ (0 : EReal) := by
            simpa [k, hy0] using hineq
          have hnonneg :
              (0 : EReal) ≤ ((ε : ℝ) : EReal) * k x :=
            EReal.mul_nonneg (by exact_mod_cast (le_of_lt hε))
              (innerMulGauge_nonneg (J := J) (j := j) (x := x))
          exact le_trans hineq0 hnonneg
    have hle_eps :
        ∀ ε : ℝ, ε > 0 → polarGauge k (y : Fin n → ℝ) ≤ (ε : EReal) := by
      intro ε hε
      unfold polarGauge
      exact sInf_le (hfeas ε hε)
    have htop : polarGauge k (y : Fin n → ℝ) ≠ ⊤ := by
      intro htop
      have hle := hle_eps 1 (by linarith)
      have hle' : (⊤ : EReal) ≤ ((1 : ℝ) : EReal) := by
        simpa [htop] using hle
      exact (not_le_of_gt (EReal.coe_lt_top 1)) hle'
    have hbot : polarGauge k (y : Fin n → ℝ) ≠ (⊥ : EReal) :=
      polarGauge_ne_bot (k := k) (y : Fin n → ℝ)
    set a : ℝ := (polarGauge k (y : Fin n → ℝ)).toReal
    have ha : polarGauge k (y : Fin n → ℝ) = (a : EReal) := by
      simpa [a] using
        (EReal.coe_toReal (x := polarGauge k (y : Fin n → ℝ)) htop hbot).symm
    have hale : a ≤ 0 := by
      refine le_of_forall_pos_le_add ?_
      intro ε hε
      have hle := hle_eps ε hε
      have hle' : (a : EReal) ≤ (ε : EReal) := by
        simpa [ha] using hle
      have hle'' : a ≤ ε := (EReal.coe_le_coe_iff).1 hle'
      simpa using hle''
    have hle0 : polarGauge k (y : Fin n → ℝ) ≤ (0 : EReal) := by
      have hle' : (a : EReal) ≤ (0 : EReal) := (EReal.coe_le_coe_iff).2 hale
      simpa [ha] using hle'
    have hle : polarGauge k (y : Fin n → ℝ) ≤ j y := by
      simpa [hy0] using hle0
    exact ⟨hle, htop⟩
  · have hj_bot : j y ≠ (⊥ : EReal) := by
      intro hbot
      have h0le : (0 : EReal) ≤ j y := j_nonneg y
      have h0le' := h0le
      rw [hbot] at h0le'
      have h0eq : (0 : EReal) = (⊥ : EReal) := (le_bot_iff).1 h0le'
      exact (by simp : (0 : EReal) ≠ (⊥ : EReal)) h0eq
    set b : ℝ := (j y).toReal
    have hb : j y = (b : EReal) := by
      simpa [b] using (EReal.coe_toReal (x := j y) (j_ne_top y) hj_bot).symm
    have hb0 : 0 < b := by
      have hb0le : 0 ≤ b := by
        have h0le : (0 : EReal) ≤ j y := j_nonneg y
        have h0le' : (0 : EReal) ≤ (b : EReal) := by simpa [hb] using h0le
        exact (EReal.coe_le_coe_iff).1 h0le'
      have hb0ne : b ≠ 0 := by
        intro hb0
        have : j y = (0 : EReal) := by simp [hb0, hb]
        exact hy0 this
      exact lt_of_le_of_ne hb0le (Ne.symm hb0ne)
    have hposE : (0 : EReal) < j y := by
      simpa [hb] using (EReal.coe_lt_coe_iff.2 hb0)
    have hμmem :
        j y ∈ {μ : EReal |
          0 ≤ μ ∧
            ∀ x : Fin n → ℝ,
              ((x ⬝ᵥ (y : Fin n → ℝ) : ℝ) : EReal) ≤ μ * k x} := by
      refine ⟨j_nonneg y, ?_⟩
      intro x
      by_cases hkx_top : k x = ⊤
      · have hmul : j y * k x = ⊤ := by
          simpa [hkx_top] using (EReal.mul_top_of_pos (x := j y) hposE)
        simp [hmul]
      · have hineq :
          ((x ⬝ᵥ (y : Fin n → ℝ) : ℝ) : EReal) ≤ k x * j y :=
          inner_le_innerMulGauge_mul_j_of_ne_top (J := J) (j := j) j_nonneg j_ne_top x hkx_top y
        simpa [mul_comm] using hineq
    have hle : polarGauge k (y : Fin n → ℝ) ≤ j y := by
      unfold polarGauge
      exact sInf_le hμmem
    have htop : polarGauge k (y : Fin n → ℝ) ≠ ⊤ := by
      intro htop
      have hle' : (⊤ : EReal) ≤ j y := by simpa [htop] using hle
      have htop' : j y = ⊤ := (top_le_iff).1 hle'
      exact (j_ne_top y) htop'
    exact ⟨hle, htop⟩

/-- Text 15.0.10: Given subsets `H, J ⊆ ℝⁿ` and functions `h : H → [0, +∞]`, `j : J → [0, +∞]`
such that `⟪x, y⟫ ≤ h x * j y` for all `x ∈ H`, `y ∈ J`, define
`k(x) := inf { μ ≥ 0 | ⟪x, y⟫ ≤ μ * j y for all y ∈ J }`.

Then `k` is a closed gauge and satisfies `⟪x, y⟫ ≤ k x * j y` for all `x ∈ dom k`, `y ∈ J`, with
`dom k ⊇ H` and `k x ≤ h x` for all `x ∈ H`. Moreover, its polar gauge `k^∘` satisfies
`dom k^∘ ⊇ J` and `k^∘ y ≤ j y` for all `y ∈ J`, hence `⟪x, y⟫ ≤ k x * k^∘ y` for all
`x ∈ dom k`, `y ∈ dom k^∘`.

In this development, `ℝⁿ` is `Fin n → ℝ`, `[0, +∞]` is modeled by `EReal` with nonnegativity, and
effective-domain assumptions are modeled by `k x ≠ ⊤`. -/
theorem exists_closedGauge_of_inner_le_mul {n : ℕ} {H J : Set (Fin n → ℝ)} (h : H → EReal)
    (j : J → EReal)
    (h_nonneg : ∀ x : H, (0 : EReal) ≤ h x)
    (h_ne_top : ∀ x : H, h x ≠ ⊤)
    (j_nonneg : ∀ y : J, (0 : EReal) ≤ j y)
    (j_ne_top : ∀ y : J, j y ≠ ⊤)
    (hineq : ∀ x : H, ∀ y : J, ((x.1 ⬝ᵥ (y : Fin n → ℝ) : ℝ) : EReal) ≤ h x * j y) :
    let k : (Fin n → ℝ) → EReal := innerMulGauge (J := J) j
    (IsGauge k ∧ IsClosed (epigraph (S := (Set.univ : Set (Fin n → ℝ))) k)) ∧
      (∀ x : Fin n → ℝ,
          k x ≠ ⊤ → ∀ y : J, ((x ⬝ᵥ (y : Fin n → ℝ) : ℝ) : EReal) ≤ k x * j y) ∧
        (∀ x : H, k x.1 ≠ ⊤) ∧
          (∀ x : H, k x.1 ≤ h x) ∧
            (∀ y : J, polarGauge k (y : Fin n → ℝ) ≠ ⊤) ∧
              (∀ y : J, polarGauge k (y : Fin n → ℝ) ≤ j y) ∧
                (∀ x y : Fin n → ℝ,
                    k x ≠ ⊤ →
                      polarGauge k y ≠ ⊤ → ((x ⬝ᵥ y : ℝ) : EReal) ≤ k x * polarGauge k y) := by
  classical
  -- Inline the `let`-bound definition.
  dsimp
  set k : (Fin n → ℝ) → EReal := innerMulGauge (J := J) j
  have hk_le_h :
      ∀ x : H, k x.1 ≤ h x ∧ k x.1 ≠ ⊤ := by
    simpa [k] using
      (innerMulGauge_le_h_on_H (H := H) (J := J) (h := h) (j := j)
        h_nonneg h_ne_top hineq)
  have hk_ineq :
      ∀ x : Fin n → ℝ, k x ≠ ⊤ → ∀ y : J,
        ((x ⬝ᵥ (y : Fin n → ℝ) : ℝ) : EReal) ≤ k x * j y := by
    intro x hx y
    simpa [k] using
      (inner_le_innerMulGauge_mul_j_of_ne_top (J := J) (j := j) j_nonneg j_ne_top x hx y)
  have hk : IsGauge k := by
    simpa [k] using innerMulGauge_isGauge (J := J) (j := j)
  have hk_closed :
      IsClosed (epigraph (S := (Set.univ : Set (Fin n → ℝ))) k) := by
    simpa [k] using
      isClosed_epigraph_innerMulGauge (J := J) (j := j) j_nonneg j_ne_top
  have hpol :
      ∀ y : J, polarGauge k (y : Fin n → ℝ) ≤ j y ∧
        polarGauge k (y : Fin n → ℝ) ≠ ⊤ := by
    simpa [k] using
      polarGauge_innerMulGauge_le_j_on_J (J := J) (j := j) j_nonneg j_ne_top
  refine ?_
  -- Main conjuncts; remaining pieces require additional structural lemmas.
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨hk, hk_closed⟩
  · simpa [k] using hk_ineq
  · intro x
    simpa [k] using (hk_le_h x).2
  · intro x
    simpa [k] using (hk_le_h x).1
  · intro y
    exact (hpol y).2
  · intro y
    exact (hpol y).1
  · intro x y hx hy
    exact inner_le_mul_polarGauge (hk := hk) (x := x) (xStar := y) hx hy

/-- Text 15.0.11: Let `k(x) = ‖x‖₂` be the Euclidean norm on `ℝⁿ`. Then `k` is both the gauge
function and the support function of the Euclidean unit ball `B = {x | ‖x‖₂ ≤ 1}`. In particular,
the polar gauge satisfies `k^∘ = k`. Consequently, the inequality associated with the polar pair
`(k, k^∘)` is the Schwarz inequality

`⟪x, y⟫ ≤ ‖x‖₂ ‖y‖₂` for all `x, y ∈ ℝⁿ`.

In this development, we work with `Fin n → ℝ` for `ℝⁿ`, define `‖x‖₂` as `Real.sqrt (dotProduct x x)`,
take the unit ball to be `{x | Real.sqrt (dotProduct x x) ≤ 1}`, and use `gaugeFunction` and
`supportFunctionEReal` for the gauge and support functions. -/
noncomputable def euclideanNormEReal {n : ℕ} (x : Fin n → ℝ) : EReal :=
  ((Real.sqrt (dotProduct x x) : ℝ) : EReal)

def piEuclideanUnitBall (n : ℕ) : Set (Fin n → ℝ) :=
  {x | Real.sqrt (dotProduct x x) ≤ (1 : ℝ)}

/-- Every vector can be written as its Euclidean norm times a unit-ball vector. -/
lemma exists_unitBall_smul_eq {n : ℕ} (x : Fin n → ℝ) :
    ∃ y ∈ piEuclideanUnitBall n, x = Real.sqrt (dotProduct x x) • y := by
  by_cases hx : x = 0
  · refine ⟨0, ?_, ?_⟩
    · simp [piEuclideanUnitBall]
    · simp [hx]
  · set r : ℝ := Real.sqrt (dotProduct x x)
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    have hrne : r ≠ 0 := by
      intro hr0'
      have hzero : dotProduct x x = 0 := by
        have hsqrt : Real.sqrt (dotProduct x x) = 0 := by simpa [r] using hr0'
        have hnonneg : 0 ≤ dotProduct x x := dotProduct_self_nonneg (v := x)
        exact (Real.sqrt_eq_zero hnonneg).1 hsqrt
      exact hx ((dotProduct_self_eq_zero (v := x)).1 hzero)
    refine ⟨(r⁻¹) • x, ?_, ?_⟩
    · have hdot :
          dotProduct ((r⁻¹) • x) ((r⁻¹) • x) =
            (r⁻¹) * (r⁻¹) * dotProduct x x := by
        simp [dotProduct_smul, smul_eq_mul, mul_comm, mul_left_comm]
      have hrr : r * r = dotProduct x x := by
        have hrr := Real.mul_self_sqrt (dotProduct_self_nonneg (v := x))
        simpa [r] using hrr
      have hdot' : dotProduct ((r⁻¹) • x) ((r⁻¹) • x) ≤ (1 : ℝ) := by
        have : (r⁻¹) * (r⁻¹) * dotProduct x x = (1 : ℝ) := by
          calc
            (r⁻¹) * (r⁻¹) * dotProduct x x
                = (r⁻¹) * (r⁻¹) * (r * r) := by simp [hrr]
            _ = (1 : ℝ) := by
              field_simp [hrne]
        simp [hdot, this]
      have hsqrt :
          Real.sqrt (dotProduct ((r⁻¹) • x) ((r⁻¹) • x)) ≤ (1 : ℝ) := by
        refine (Real.sqrt_le_iff).2 ?_
        refine ⟨by norm_num, ?_⟩
        simpa using hdot'
      simpa [piEuclideanUnitBall] using hsqrt
    · simp [r, smul_smul, hrne]

/-- The Euclidean unit ball is absorbing. -/
lemma piEuclideanUnitBall_absorbing {n : ℕ} :
    ∀ x : Fin n → ℝ, ∃ r : ℝ, 0 ≤ r ∧ ∃ y ∈ piEuclideanUnitBall n, x = r • y := by
  intro x
  rcases exists_unitBall_smul_eq (n := n) x with ⟨y, hyB, hxy⟩
  refine ⟨Real.sqrt (dotProduct x x), Real.sqrt_nonneg _, y, hyB, hxy⟩

theorem euclideanNormEReal_eq_gaugeFunction_euclideanUnitBall {n : ℕ} :
    euclideanNormEReal (n := n) = fun x => (gaugeFunction (piEuclideanUnitBall n) x : EReal) := by
  funext x
  apply (EReal.coe_eq_coe_iff).2
  let B : Set (Fin n → ℝ) := piEuclideanUnitBall n
  let S : Set ℝ := {r : ℝ | 0 ≤ r ∧ ∃ y ∈ B, x = r • y}
  have hS_nonempty : S.Nonempty := by
    rcases exists_unitBall_smul_eq (n := n) x with ⟨y, hyB, hxy⟩
    refine ⟨Real.sqrt (dotProduct x x), ?_⟩
    refine ⟨Real.sqrt_nonneg _, y, by simpa [B] using hyB, hxy⟩
  have hBdd : BddBelow S := by
    refine ⟨0, ?_⟩
    intro r hr
    exact hr.1
  have hle : Real.sqrt (dotProduct x x) ≤ sInf S := by
    refine le_csInf hS_nonempty ?_
    intro r hr
    rcases hr with ⟨hr0, y, hyB, hxy⟩
    have hy_sqrt : Real.sqrt (dotProduct y y) ≤ (1 : ℝ) := by
      simpa [B, piEuclideanUnitBall] using hyB
    have hyy_le : dotProduct y y ≤ (1 : ℝ) := by
      have h := (Real.sqrt_le_iff).1 hy_sqrt
      simpa using h.2
    have hdot : dotProduct x x = r * r * dotProduct y y := by
      calc
        dotProduct x x = dotProduct (r • y) (r • y) := by simp [hxy]
        _ = r * r * dotProduct y y := by
              simp [dotProduct_smul, smul_eq_mul, mul_comm, mul_left_comm]
    have hdot_le : dotProduct x x ≤ r ^ 2 := by
      have hmul :
          r * r * dotProduct y y ≤ r * r * (1 : ℝ) :=
        mul_le_mul_of_nonneg_left hyy_le (mul_nonneg hr0 hr0)
      have hmul' : r * r * dotProduct y y ≤ r * r := by
        simpa [mul_assoc] using hmul
      simpa [hdot, pow_two] using hmul'
    exact (Real.sqrt_le_iff).2 ⟨hr0, hdot_le⟩
  have hge : sInf S ≤ Real.sqrt (dotProduct x x) := by
    have hmem : Real.sqrt (dotProduct x x) ∈ S := by
      rcases exists_unitBall_smul_eq (n := n) x with ⟨y, hyB, hxy⟩
      refine ⟨Real.sqrt_nonneg _, y, by simpa [B] using hyB, hxy⟩
    exact csInf_le hBdd hmem
  have hEq : Real.sqrt (dotProduct x x) = sInf S := le_antisymm hle hge
  simpa [gaugeFunction, S, B] using hEq

theorem euclideanNormEReal_eq_supportFunctionEReal_euclideanUnitBall {n : ℕ} :
    euclideanNormEReal (n := n) = supportFunctionEReal (piEuclideanUnitBall n) := by
  funext xStar
  apply le_antisymm
  · rcases section13_exists_dotProduct_eq_sqrt (n := n) (x := xStar) with ⟨y, hyB, hyEq⟩
    have hyEq' : dotProduct y xStar = Real.sqrt (dotProduct xStar xStar) := by
      simpa [dotProduct_comm] using hyEq
    have hmem :
        ((dotProduct y xStar : ℝ) : EReal) ∈
          {z : EReal |
            ∃ x ∈ piEuclideanUnitBall n, z = ((dotProduct x xStar : ℝ) : EReal)} := by
      exact ⟨y, by simpa [piEuclideanUnitBall] using hyB, rfl⟩
    have hle :
        ((dotProduct y xStar : ℝ) : EReal) ≤
          supportFunctionEReal (piEuclideanUnitBall n) xStar := by
      unfold supportFunctionEReal
      exact le_sSup hmem
    have hle' :
        (Real.sqrt (dotProduct xStar xStar) : EReal) ≤
          supportFunctionEReal (piEuclideanUnitBall n) xStar := by
      simpa [hyEq'] using hle
    simpa [euclideanNormEReal] using hle'
  · have hle :
        supportFunctionEReal (piEuclideanUnitBall n) xStar ≤
          (Real.sqrt (dotProduct xStar xStar) : EReal) := by
      refine
        (section13_supportFunctionEReal_le_coe_iff (C := piEuclideanUnitBall n) (y := xStar)
            (μ := Real.sqrt (dotProduct xStar xStar))).2 ?_
      intro y hyB
      have hy_sqrt : Real.sqrt (dotProduct y y) ≤ (1 : ℝ) := by
        simpa [piEuclideanUnitBall] using hyB
      have hcs :
          dotProduct y xStar ≤
            Real.sqrt (dotProduct y y) * Real.sqrt (dotProduct xStar xStar) :=
        section13_dotProduct_le_sqrt_mul_sqrt (n := n) (x := y) (y := xStar)
      have hxnonneg : 0 ≤ Real.sqrt (dotProduct xStar xStar) := Real.sqrt_nonneg _
      have hmul :
          Real.sqrt (dotProduct y y) * Real.sqrt (dotProduct xStar xStar) ≤
            Real.sqrt (dotProduct xStar xStar) := by
        have hmul' :=
          mul_le_mul_of_nonneg_right hy_sqrt hxnonneg
        simpa using hmul'
      exact le_trans hcs hmul
    simpa [euclideanNormEReal] using hle

theorem dotProduct_le_mul_sqrt_dotProduct_self {n : ℕ} (x y : Fin n → ℝ) :
    dotProduct x y ≤ Real.sqrt (dotProduct x x) * Real.sqrt (dotProduct y y) := by
  simpa using section13_dotProduct_le_sqrt_mul_sqrt (n := n) (x := x) (y := y)

/-- Text 15.0.12: A gauge `k : ℝⁿ → [0, +∞)` is called a norm if it is finite everywhere, symmetric
(`k (-x) = k x` for all `x`), and satisfies `k x > 0` for all `x ≠ 0`.

Equivalently, `k` is real-valued and satisfies:
(a) `k x > 0` for all `x ≠ 0`;
(b) `k (x₁ + x₂) ≤ k x₁ + k x₂` for all `x₁, x₂`;
(c) `k (λ • x) = λ * k x` for all `x` and all `λ > 0`;
(d) `k (-x) = k x` for all `x`.

In particular, (c) and (d) imply `k (λ • x) = |λ| * k x` for all `x` and all `λ ∈ ℝ`.

In this development, `ℝⁿ` is `Fin n → ℝ`, codomain is `EReal`, and "finite everywhere" is
`∀ x, k x ≠ ⊤`. -/
def IsNormGauge {n : ℕ} (k : (Fin n → ℝ) → EReal) : Prop :=
  IsGauge k ∧ (∀ x, k x ≠ ⊤) ∧ (∀ x, k (-x) = k x) ∧ (∀ x, x ≠ 0 → (0 : EReal) < k x)

lemma IsNormGauge.smul_eq_abs {n : ℕ} {k : (Fin n → ℝ) → EReal} (hk : IsNormGauge k)
    (x : Fin n → ℝ) (r : ℝ) :
    k (r • x) = ((|r| : ℝ) : EReal) * k x := by
  by_cases hr : 0 ≤ r
  · have hhom := hk.1.2.2.1 x r hr
    simpa [abs_of_nonneg hr] using hhom
  · have hneg : r < 0 := lt_of_not_ge hr
    have hr' : 0 ≤ -r := by linarith
    have hhom := hk.1.2.2.1 (-x) (-r) hr'
    have hsymm : k (-x) = k x := hk.2.2.1 x
    calc
      k (r • x) = k ((-r) • (-x)) := by simp
      _ = ((-r : ℝ) : EReal) * k (-x) := hhom
      _ = ((-r : ℝ) : EReal) * k x := by simp [hsymm]
      _ = ((|r| : ℝ) : EReal) * k x := by
            simp [abs_of_neg hneg]

/-- The epigraph of a gauge is a convex cone in `ℝⁿ × ℝ`. -/
def epigraph_isConvexCone_of_isGauge {n : ℕ} {k : (Fin n → ℝ) → EReal} (hk : IsGauge k) :
    ConvexCone ℝ ((Fin n → ℝ) × ℝ) := by
  classical
  refine
    { carrier := epigraph (S := (Set.univ : Set (Fin n → ℝ))) k
      smul_mem' := ?_
      add_mem' := ?_ }
  · intro c hc p hp
    have hc0 : 0 ≤ c := le_of_lt hc
    rcases p with ⟨x, μ⟩
    have hx : k x ≤ (μ : EReal) :=
      (mem_epigraph_univ_iff (f := k) (x := x) (μ := μ)).1 hp
    have hhom : k (c • x) = ((c : ℝ) : EReal) * k x := hk.2.2.1 x c hc0
    have hmul :
        ((c : ℝ) : EReal) * k x ≤ ((c : ℝ) : EReal) * (μ : EReal) :=
      mul_le_mul_of_nonneg_left hx (by exact_mod_cast hc0)
    have hle : k (c • x) ≤ ((c : ℝ) : EReal) * (μ : EReal) := by
      simpa [hhom] using hmul
    have hle' : k (c • x) ≤ ((c * μ : ℝ) : EReal) := by
      simpa [EReal.coe_mul, mul_comm, mul_left_comm, mul_assoc] using hle
    simpa [mem_epigraph_univ_iff] using hle'
  · intro p hp q hq
    rcases p with ⟨x, μ⟩
    rcases q with ⟨y, ν⟩
    have hx : k x ≤ (μ : EReal) :=
      (mem_epigraph_univ_iff (f := k) (x := x) (μ := μ)).1 hp
    have hy : k y ≤ (ν : EReal) :=
      (mem_epigraph_univ_iff (f := k) (x := y) (μ := ν)).1 hq
    have hle : k (x + y) ≤ (μ : EReal) + (ν : EReal) := by
      have hadd : k (x + y) ≤ k x + k y := IsGauge.add_le hk x y
      exact le_trans hadd (add_le_add hx hy)
    have hle' : k (x + y) ≤ ((μ + ν : ℝ) : EReal) := by
      simpa [EReal.coe_add, add_comm, add_left_comm, add_assoc] using hle
    simpa [mem_epigraph_univ_iff] using hle'

/-- The closure-slice infimum used in Theorem 15.1 matches `epigraphClosureInf`. -/
lemma kCl_eq_epigraphClosureInf {n : ℕ} (k : (Fin n → ℝ) → EReal) :
    (fun x =>
        sInf
          {μ : EReal |
            ∃ r : ℝ,
              μ = (r : EReal) ∧
                (x, r) ∈ closure (epigraph (S := (Set.univ : Set (Fin n → ℝ))) k)}) =
      epigraphClosureInf k := by
  funext x
  have hset :
      {μ : EReal |
          ∃ r : ℝ,
            μ = (r : EReal) ∧
              (x, r) ∈ closure (epigraph (S := (Set.univ : Set (Fin n → ℝ))) k)} =
        (fun r : ℝ => (r : EReal)) '' {r : ℝ |
          (x, r) ∈ closure (epigraph (S := (Set.univ : Set (Fin n → ℝ))) k)} := by
    ext μ
    constructor
    · intro hμ
      rcases hμ with ⟨r, rfl, hr⟩
      exact ⟨r, hr, rfl⟩
    · intro hμ
      rcases hμ with ⟨r, hr, rfl⟩
      exact ⟨r, rfl, hr⟩
  simp [epigraphClosureInf, hset]

/-- The support function is bounded above by the polar gauge of a gauge-function. -/
lemma supportFunctionEReal_le_polarGauge_of_gaugeFunction {n : ℕ} (C : Set (Fin n → ℝ))
    (xStar : Fin n → ℝ) :
    supportFunctionEReal C xStar ≤
      polarGauge (fun x => (gaugeFunction C x : EReal)) xStar := by
  classical
  let k : (Fin n → ℝ) → EReal := fun x => (gaugeFunction C x : EReal)
  have hk_le_one : ∀ y ∈ C, k y ≤ (1 : EReal) := by
    intro y hyC
    have hmem :
        (1 : ℝ) ∈ {r : ℝ | 0 ≤ r ∧ ∃ y' ∈ C, y = r • y'} := by
      refine ⟨by linarith, ?_⟩
      exact ⟨y, hyC, by simp⟩
    have hreal : gaugeFunction C y ≤ 1 := by
      have hbdd : BddBelow {r : ℝ | 0 ≤ r ∧ ∃ y' ∈ C, y = r • y'} := by
        refine ⟨0, ?_⟩
        intro r hr
        exact hr.1
      have : sInf {r : ℝ | 0 ≤ r ∧ ∃ y' ∈ C, y = r • y'} ≤ 1 :=
        csInf_le hbdd hmem
      simpa [gaugeFunction] using this
    simpa [k] using (show (gaugeFunction C y : EReal) ≤ (1 : EReal) from by exact_mod_cast hreal)
  unfold polarGauge supportFunctionEReal
  refine le_sInf ?_
  intro μ hμ
  rcases hμ with ⟨hμ0, hμ⟩
  refine sSup_le ?_
  intro z hz
  rcases hz with ⟨y, hyC, rfl⟩
  have hinner : ((y ⬝ᵥ xStar : ℝ) : EReal) ≤ μ * k y := hμ y
  have hmul : μ * k y ≤ μ * (1 : EReal) :=
    mul_le_mul_of_nonneg_left (hk_le_one y hyC) hμ0
  have hinner' : ((y ⬝ᵥ xStar : ℝ) : EReal) ≤ μ := by
    have h := le_trans hinner hmul
    simp at h
    exact h
  exact hinner'

/-- The support function of an absorbing set is nonnegative. -/
lemma supportFunctionEReal_nonneg_of_absorbing {n : ℕ} {C : Set (Fin n → ℝ)} (hCne : C.Nonempty)
    (hCabs : ∀ x : Fin n → ℝ, ∃ r : ℝ, 0 ≤ r ∧ ∃ y ∈ C, x = r • y) :
    ∀ xStar : Fin n → ℝ, 0 ≤ supportFunctionEReal C xStar := by
  intro xStar
  by_cases hx : xStar = 0
  · rcases hCne with ⟨y, hyC⟩
    have hmem :
        (0 : EReal) ∈
          {z : EReal | ∃ x ∈ C, z = ((dotProduct x xStar : ℝ) : EReal)} := by
      refine ⟨y, hyC, ?_⟩
      simp [hx]
    have hle : (0 : EReal) ≤ supportFunctionEReal C xStar := by
      unfold supportFunctionEReal
      exact le_sSup hmem
    exact hle
  · obtain ⟨r, hr0, y, hyC, hxy⟩ := hCabs xStar
    have hrne : r ≠ 0 := by
      intro hr
      have : xStar = 0 := by simp [hxy, hr]
      exact hx this
    have hy' : (r⁻¹ : ℝ) • xStar = y := by
      have h := congrArg (fun z => (r⁻¹ : ℝ) • z) hxy
      simp [smul_smul, hrne] at h
      exact h
    have hdot : dotProduct y xStar = (r⁻¹ : ℝ) * dotProduct xStar xStar := by
      calc
        dotProduct y xStar = dotProduct ((r⁻¹ : ℝ) • xStar) xStar := by simp [hy']
        _ = dotProduct xStar ((r⁻¹ : ℝ) • xStar) := by simp [dotProduct_comm]
        _ = (r⁻¹ : ℝ) * dotProduct xStar xStar := by
              simp [dotProduct_smul, smul_eq_mul, mul_comm]
    have hdot_nonneg : 0 ≤ dotProduct y xStar := by
      have hrinv_nonneg : 0 ≤ (r⁻¹ : ℝ) := inv_nonneg.mpr hr0
      have hself_nonneg : 0 ≤ dotProduct xStar xStar := dotProduct_self_nonneg (v := xStar)
      have : 0 ≤ (r⁻¹ : ℝ) * dotProduct xStar xStar := mul_nonneg hrinv_nonneg hself_nonneg
      have h' : 0 ≤ dotProduct y xStar := by
        simpa [hdot] using this
      exact h'
    have hmem :
        ((dotProduct y xStar : ℝ) : EReal) ∈
          {z : EReal | ∃ x ∈ C, z = ((dotProduct x xStar : ℝ) : EReal)} := by
      exact ⟨y, hyC, rfl⟩
    have hle : ((dotProduct y xStar : ℝ) : EReal) ≤ supportFunctionEReal C xStar := by
      unfold supportFunctionEReal
      exact le_sSup hmem
    have hnonneg : (0 : EReal) ≤ ((dotProduct y xStar : ℝ) : EReal) := by
      exact_mod_cast hdot_nonneg
    exact le_trans hnonneg hle

/-- The polar gauge of a gauge-function is bounded above by the support function under absorbing. -/
lemma polarGauge_of_gaugeFunction_le_supportFunctionEReal {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCne : C.Nonempty)
    (hCabs : ∀ x : Fin n → ℝ, ∃ r : ℝ, 0 ≤ r ∧ ∃ y ∈ C, x = r • y) :
    ∀ xStar : Fin n → ℝ,
      polarGauge (fun x => (gaugeFunction C x : EReal)) xStar ≤ supportFunctionEReal C xStar := by
  intro xStar
  by_cases htop : supportFunctionEReal C xStar = ⊤
  · simp [htop]
  have hnonneg :
      (0 : EReal) ≤ supportFunctionEReal C xStar :=
    supportFunctionEReal_nonneg_of_absorbing (C := C) hCne hCabs xStar
  have hbot : supportFunctionEReal C xStar ≠ ⊥ := by
    intro hbot
    have hle : (0 : EReal) ≤ (⊥ : EReal) := by
      calc
        (0 : EReal) ≤ supportFunctionEReal C xStar := hnonneg
        _ = (⊥ : EReal) := hbot
    have hlt : (⊥ : EReal) < (0 : EReal) := by
      simp
    exact (not_le_of_gt hlt) hle
  set μ : ℝ := (supportFunctionEReal C xStar).toReal
  have hμE : supportFunctionEReal C xStar = (μ : EReal) := by
    simpa [μ] using
      (EReal.coe_toReal (x := supportFunctionEReal C xStar) htop hbot).symm
  have hμ_nonneg : 0 ≤ μ := by
    have hnonneg' := hnonneg
    rw [hμE] at hnonneg'
    exact (EReal.coe_le_coe_iff).1 hnonneg'
  have hμmem :
      0 ≤ (μ : EReal) ∧
        ∀ x : Fin n → ℝ,
          ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ (μ : EReal) * (gaugeFunction C x : EReal) := by
    refine ⟨?_, ?_⟩
    · exact_mod_cast hμ_nonneg
    · intro x
      have hreal : dotProduct x xStar ≤ μ * gaugeFunction C x := by
        refine le_of_forall_pos_le_add ?_
        intro ε hε
        have hμ1_pos : 0 < μ + 1 := by linarith
        set δ : ℝ := ε / (μ + 1)
        have hδpos : 0 < δ := by
          dsimp [δ]
          exact div_pos hε hμ1_pos
        have hlt : gaugeFunction C x < gaugeFunction C x + δ := by linarith
        have hlt' :
            sInf {r : ℝ | 0 ≤ r ∧ ∃ y ∈ C, x = r • y} < gaugeFunction C x + δ := by
          simpa [gaugeFunction] using hlt
        have hS_nonempty : Set.Nonempty {r : ℝ | 0 ≤ r ∧ ∃ y ∈ C, x = r • y} := by
          rcases hCabs x with ⟨r, hr0, y, hyC, hxy⟩
          exact ⟨r, hr0, y, hyC, hxy⟩
        obtain ⟨r, hrS, hrlt⟩ := exists_lt_of_csInf_lt hS_nonempty hlt'
        rcases hrS with ⟨hr0, y, hyC, hxy⟩
        have hdot : dotProduct x xStar = r * dotProduct y xStar := by
          calc
            dotProduct x xStar = dotProduct (r • y) xStar := by simp [hxy]
            _ = dotProduct xStar (r • y) := by simp [dotProduct_comm]
            _ = r * dotProduct xStar y := by
                  simp [dotProduct_smul, smul_eq_mul]
            _ = r * dotProduct y xStar := by simp [dotProduct_comm]
        have hsupE :
            ((dotProduct y xStar : ℝ) : EReal) ≤ supportFunctionEReal C xStar := by
          unfold supportFunctionEReal
          exact le_sSup ⟨y, hyC, rfl⟩
        have hsup : dotProduct y xStar ≤ μ := by
          have : ((dotProduct y xStar : ℝ) : EReal) ≤ (μ : EReal) := by
            simpa [hμE] using hsupE
          exact (EReal.coe_le_coe_iff).1 this
        have hle1 : r * dotProduct y xStar ≤ r * μ :=
          mul_le_mul_of_nonneg_left hsup hr0
        have hle_r : r ≤ gaugeFunction C x + δ := le_of_lt hrlt
        have hle2 : r * μ ≤ (gaugeFunction C x + δ) * μ :=
          mul_le_mul_of_nonneg_right hle_r hμ_nonneg
        have hle' : dotProduct x xStar ≤ (gaugeFunction C x + δ) * μ := by
          calc
            dotProduct x xStar = r * dotProduct y xStar := hdot
            _ ≤ r * μ := hle1
            _ ≤ (gaugeFunction C x + δ) * μ := hle2
        have hδ_nonneg : 0 ≤ δ := le_of_lt hδpos
        have hμ_le : μ ≤ μ + 1 := by linarith
        have hmul_le : μ * δ ≤ (μ + 1) * δ :=
          mul_le_mul_of_nonneg_right hμ_le hδ_nonneg
        have hμ1_ne : μ + 1 ≠ 0 := ne_of_gt hμ1_pos
        have hmul_eq : (μ + 1) * δ = ε := by
          dsimp [δ]
          field_simp [hμ1_ne]
        have hμδ_le : μ * δ ≤ ε := by
          simpa [hmul_eq] using hmul_le
        have hle'' : dotProduct x xStar ≤ μ * gaugeFunction C x + ε := by
          calc
            dotProduct x xStar ≤ (gaugeFunction C x + δ) * μ := hle'
            _ = μ * gaugeFunction C x + μ * δ := by ring
            _ ≤ μ * gaugeFunction C x + ε := by
                  have h' := add_le_add_left hμδ_le (μ * gaugeFunction C x)
                  simpa [add_comm, add_left_comm, add_assoc] using h'
        exact hle''
      have hE :
          ((dotProduct x xStar : ℝ) : EReal) ≤ ((μ * gaugeFunction C x : ℝ) : EReal) := by
        exact_mod_cast hreal
      have hmulE :
          ((μ * gaugeFunction C x : ℝ) : EReal) =
            (μ : EReal) * (gaugeFunction C x : EReal) := by
        simp [EReal.coe_mul]
      simpa [hmulE] using hE
  have hle :
      polarGauge (fun x => (gaugeFunction C x : EReal)) xStar ≤ (μ : EReal) := by
    unfold polarGauge
    exact sInf_le hμmem
  simpa [hμE] using hle

theorem polarGauge_euclideanNormEReal {n : ℕ} :
    polarGauge (euclideanNormEReal (n := n)) = euclideanNormEReal (n := n) := by
  funext xStar
  apply le_antisymm
  · have hCne : (piEuclideanUnitBall n).Nonempty := by
      refine ⟨0, ?_⟩
      simp [piEuclideanUnitBall]
    have hCabs :
        ∀ x : Fin n → ℝ, ∃ r : ℝ, 0 ≤ r ∧ ∃ y ∈ piEuclideanUnitBall n, x = r • y :=
      piEuclideanUnitBall_absorbing (n := n)
    have hle :
        polarGauge (fun x => (gaugeFunction (piEuclideanUnitBall n) x : EReal)) xStar ≤
          supportFunctionEReal (piEuclideanUnitBall n) xStar :=
      polarGauge_of_gaugeFunction_le_supportFunctionEReal (C := piEuclideanUnitBall n) hCne hCabs
        xStar
    have hle' :
        polarGauge (euclideanNormEReal (n := n)) xStar ≤
          supportFunctionEReal (piEuclideanUnitBall n) xStar := by
      simpa [euclideanNormEReal_eq_gaugeFunction_euclideanUnitBall] using hle
    simpa [euclideanNormEReal_eq_supportFunctionEReal_euclideanUnitBall] using hle'
  · have hle :
        supportFunctionEReal (piEuclideanUnitBall n) xStar ≤
          polarGauge (fun x => (gaugeFunction (piEuclideanUnitBall n) x : EReal)) xStar :=
      supportFunctionEReal_le_polarGauge_of_gaugeFunction (C := piEuclideanUnitBall n) xStar
    have hle' :
        supportFunctionEReal (piEuclideanUnitBall n) xStar ≤
          polarGauge (euclideanNormEReal (n := n)) xStar := by
      simpa [euclideanNormEReal_eq_gaugeFunction_euclideanUnitBall] using hle
    simpa [euclideanNormEReal_eq_supportFunctionEReal_euclideanUnitBall] using hle'

/-- The sign-flip on the first coordinate of `EuclideanSpace × ℝ` is an involution. -/
lemma signflip_euclidean_involutive {n : ℕ} :
    let E₂ := EuclideanSpace ℝ (Fin n)
    let H₂ := E₂ × ℝ
    let σ₂ : H₂ → H₂ := fun p => (-p.1, p.2)
    ∀ p : H₂, σ₂ (σ₂ p) = p := by
  dsimp
  intro p
  cases p with
  | mk x μ =>
      simp

/-- The inner product commutes with the sign-flip on the first coordinate in `H₂`. -/
lemma inner_signflip_H2 {n : ℕ} :
    let E₂ := EuclideanSpace ℝ (Fin n)
    let H₂ := WithLp 2 (E₂ × ℝ)
    let σ₂ : H₂ → H₂ := fun p => WithLp.toLp 2 (- (WithLp.ofLp p).1, (WithLp.ofLp p).2)
    ∀ p q : H₂,
      inner (𝕜 := ℝ) (σ₂ p) q = inner (𝕜 := ℝ) p (σ₂ q) := by
  dsimp
  intro p q
  simp [inner_neg_left, inner_neg_right]

/-- The inner dual cone commutes with sign-flip on the first coordinate in `WithLp 2 (E × ℝ)`. -/
lemma innerDual_preimage_signflip {n : ℕ}
    (A : Set (WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ))) :
    (ProperCone.innerDual
        (E := WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ))
        ((fun p => WithLp.toLp 2 (- (WithLp.ofLp p).1, (WithLp.ofLp p).2)) ⁻¹' A) :
        Set (WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ))) =
      (fun p => WithLp.toLp 2 (- (WithLp.ofLp p).1, (WithLp.ofLp p).2)) ⁻¹'
        (ProperCone.innerDual
            (E := WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ)) A :
          Set (WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ))) := by
  classical
  let H₂ := WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ)
  let σ₂ : H₂ → H₂ := fun p => WithLp.toLp 2 (- (WithLp.ofLp p).1, (WithLp.ofLp p).2)
  have hσ : ∀ x : H₂, σ₂ (σ₂ x) = x := by
    intro x
    rcases x with ⟨x, μ⟩
    simp [σ₂]
  ext y
  constructor
  · intro hy
    have hy_mem :
        y ∈ (ProperCone.innerDual (E := H₂) (σ₂ ⁻¹' A) : Set H₂) := by
      simpa [σ₂] using hy
    have hy_mem' : y ∈ ProperCone.innerDual (E := H₂) (σ₂ ⁻¹' A) := by
      simpa using hy_mem
    have hy' : ∀ x ∈ σ₂ ⁻¹' A, 0 ≤ ⟪x, y⟫ := by
      intro x hx
      exact (ProperCone.mem_innerDual (E := H₂) (s := σ₂ ⁻¹' A) (y := y)).1 hy_mem' (x := x) hx
    have hy_inner : σ₂ y ∈ (ProperCone.innerDual (E := H₂) A : Set H₂) := by
      refine (ProperCone.mem_innerDual (E := H₂) (s := A) (y := σ₂ y)).2 ?_
      intro x hx
      have hx' : σ₂ x ∈ σ₂ ⁻¹' A := by
        simpa [Set.preimage, hσ x] using hx
      have hinner : 0 ≤ ⟪σ₂ x, y⟫ := hy' (x := σ₂ x) hx'
      have hinner' : ⟪σ₂ x, y⟫ = ⟪x, σ₂ y⟫ := by
        simp [H₂, σ₂]
      simpa [hinner'] using hinner
    change σ₂ y ∈ (ProperCone.innerDual (E := H₂) A : Set H₂)
    exact hy_inner
  · intro hy
    have hy' : σ₂ y ∈ (ProperCone.innerDual (E := H₂) A : Set H₂) := by
      change y ∈ (σ₂ ⁻¹' (ProperCone.innerDual (E := H₂) A : Set H₂))
      exact hy
    refine (ProperCone.mem_innerDual (E := H₂) (s := σ₂ ⁻¹' A) (y := y)).2 ?_
    intro x hx
    have hx' : σ₂ x ∈ A := by
      simpa [Set.preimage, σ₂] using hx
    have hinner : 0 ≤ ⟪σ₂ x, σ₂ y⟫ :=
      (ProperCone.mem_innerDual (E := H₂) (s := A) (y := σ₂ y)).1 hy' (x := σ₂ x) hx'
    have hinner' : ⟪σ₂ x, σ₂ y⟫ = ⟪x, y⟫ := by
      simp [H₂, σ₂]
    simpa [hinner'] using hinner

/-- Continuous linear equivalence between the inner-product model `H₂` and `((Fin n → ℝ) × ℝ)`. -/
noncomputable def eH_transport_to_H2 (n : ℕ) :
    WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ) ≃L[ℝ] ((Fin n → ℝ) × ℝ) := by
  classical
  -- `EuclideanSpace` is definitional equal to `WithLp 2`, so `WithLp.linearEquiv` applies.
  let eL : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) :=
    (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toContinuousLinearEquiv
  let eH0 : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ) ≃L[ℝ]
      (EuclideanSpace ℝ (Fin n) × ℝ) :=
    (WithLp.linearEquiv 2 ℝ (EuclideanSpace ℝ (Fin n) × ℝ)).toContinuousLinearEquiv
  exact eH0.trans (ContinuousLinearEquiv.prodCongr eL (ContinuousLinearEquiv.refl ℝ ℝ))

/-- Epigraph points of a gauge have nonnegative second coordinate. -/
lemma mem_epigraph_snd_nonneg_of_isGauge {n : ℕ} {k : (Fin n → ℝ) → EReal} (hk : IsGauge k)
    {x : Fin n → ℝ} {r : ℝ}
    (hx : (x, r) ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) k) : 0 ≤ r := by
  have hx' : k x ≤ (r : EReal) :=
    (mem_epigraph_univ_iff (f := k) (x := x) (μ := r)).1 hx
  have h0le : (0 : EReal) ≤ (r : EReal) := le_trans (hk.2.1 x) hx'
  exact (EReal.coe_le_coe_iff).1 h0le

/-- The sign-flip on the first coordinate of `H₂` is an involution. -/
lemma signflip_H2_involutive {n : ℕ} :
    let E₂ := EuclideanSpace ℝ (Fin n)
    let H₂ := WithLp 2 (E₂ × ℝ)
    let σ₂ : H₂ → H₂ := fun p => WithLp.toLp 2 (- (WithLp.ofLp p).1, (WithLp.ofLp p).2)
    ∀ p : H₂, σ₂ (σ₂ p) = p := by
  dsimp
  intro p
  cases p with
  | toLp p =>
      cases p with
      | mk x μ =>
          simp

/-- The inner dual cone in `H₂` is closed. -/
lemma isClosed_innerDual_H2 {n : ℕ}
    (S : Set (WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ))) :
    IsClosed ((ProperCone.innerDual
      (E := WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ)) S :
        Set (WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ)))) := by
  simpa using
    (ProperCone.isClosed
      (C := ProperCone.innerDual (E := WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ)) S))

/-- Explicit formula for the inverse of `eH_transport_to_H2`. -/
lemma eH_transport_to_H2_symm_apply {n : ℕ} (x : Fin n → ℝ) (r : ℝ) :
    let eH := eH_transport_to_H2 n
    eH.symm (x, r) = WithLp.toLp 2 (WithLp.toLp 2 x, r) := by
  classical
  simp [eH_transport_to_H2, ContinuousLinearEquiv.prodCongr_symm,
    ContinuousLinearEquiv.prodCongr_apply]

/-- Inner product formula for the transported sign-flip in `H₂`. -/
lemma inner_eH_symm_signflip {n : ℕ} (x xStar : Fin n → ℝ) (r μ : ℝ) :
    inner (𝕜 := ℝ) ((eH_transport_to_H2 n).symm (x, r))
        ((fun p : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ) =>
          WithLp.toLp 2 (- (WithLp.ofLp p).1, (WithLp.ofLp p).2))
          ((eH_transport_to_H2 n).symm (xStar, μ))) =
      - dotProduct x xStar + r * μ := by
  classical
  let H₂ := WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ)
  let σ₂ : H₂ → H₂ := fun p => WithLp.toLp 2 (- (WithLp.ofLp p).1, (WithLp.ofLp p).2)
  have hx : (eH_transport_to_H2 n).symm (x, r) =
      WithLp.toLp 2 (WithLp.toLp 2 x, r) := by
    simpa using (eH_transport_to_H2_symm_apply (n := n) (x := x) (r := r))
  have hxStar : (eH_transport_to_H2 n).symm (xStar, μ) =
      WithLp.toLp 2 (WithLp.toLp 2 xStar, μ) := by
    simpa using (eH_transport_to_H2_symm_apply (n := n) (x := xStar) (r := μ))
  have hdot :
      inner (𝕜 := ℝ) (WithLp.toLp 2 x) (WithLp.toLp 2 xStar) = dotProduct x xStar := by
    simpa using (dotProduct_eq_inner_euclideanSpace (n := n) (x := x) (y := xStar)).symm
  simp [hx, hxStar, WithLp.prod_inner_apply, inner_neg_right, hdot, add_comm, mul_comm]

end Section15
end Chap03
