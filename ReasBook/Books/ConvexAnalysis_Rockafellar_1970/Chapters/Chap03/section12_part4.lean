/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Zhiyan Wang, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section12_part2

section Chap03
section Section12

/-- A standard inequality for the exponential function: for `a > 0`, the function
`x ↦ x * a - exp x` is bounded above by `a * log a - a`. -/
lemma exp_linear_sub_exp_le_conjugateValue {a x : ℝ} (ha : 0 < a) :
    x * a - Real.exp x ≤ a * Real.log a - a := by
  have h := Real.add_one_le_exp (x - Real.log a)
  have hmul :
      a * ((x - Real.log a) + 1) ≤ a * Real.exp (x - Real.log a) :=
    mul_le_mul_of_nonneg_left h (le_of_lt ha)
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hrewrite : a * Real.exp (x - Real.log a) = Real.exp x := by
    calc
      a * Real.exp (x - Real.log a)
          = a * (Real.exp x / Real.exp (Real.log a)) := by simp [Real.exp_sub]
      _ = a * (Real.exp x / a) := by simp [Real.exp_log ha]
      _ = Real.exp x := by
        field_simp [ha0]
  have hmul' : a * ((x - Real.log a) + 1) ≤ Real.exp x := by simpa [hrewrite] using hmul
  have hadd : a * (x - Real.log a) + a ≤ Real.exp x := by
    simpa [mul_add, add_assoc] using hmul'
  have hsub : a * (x - Real.log a) ≤ Real.exp x - a :=
    (le_sub_iff_add_le).2 hadd
  have hsub' : a * x - a * Real.log a ≤ Real.exp x - a := by
    simpa [mul_sub] using hsub
  have hxle : a * x ≤ Real.exp x - a + a * Real.log a := by
    have := add_le_add_right hsub' (a * Real.log a)
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
  have hxle' :
      a * x - Real.exp x ≤ (Real.exp x - a + a * Real.log a) - Real.exp x :=
    sub_le_sub_right hxle (Real.exp x)
  -- Simplify and commute the product to match the statement.
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
    mul_comm, mul_left_comm, mul_assoc] using hxle'

/-- If `a < 0`, the function `x ↦ x * a - exp x` is unbounded above. -/
lemma exists_gt_linear_sub_exp_of_neg {a μ : ℝ} (ha : a < 0) :
    ∃ x : ℝ, μ < x * a - Real.exp x := by
  have hpos : 0 < -a := by linarith
  have hne : (-a) ≠ 0 := ne_of_gt hpos
  set t : ℝ := max ((μ + 1) / (-a)) 1
  have ht1 : 1 ≤ t := le_max_right _ _
  have htμ : (μ + 1) / (-a) ≤ t := le_max_left _ _
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht1
  have hneg : -t < 0 := by linarith
  have hexp : Real.exp (-t) < 1 := (Real.exp_lt_one_iff).2 hneg
  have hmul' : μ + 1 ≤ t * (-a) := by
    have := mul_le_mul_of_nonneg_right htμ (le_of_lt hpos)
    have hleft : ((μ + 1) / (-a)) * (-a) = μ + 1 := by
      calc
        (μ + 1) / (-a) * (-a) = (μ + 1) * (-a) / (-a) := by
          simpa using (div_mul_eq_mul_div (μ + 1) (-a) (-a))
        _ = μ + 1 := by
          simpa using (mul_div_cancel_right₀ (μ + 1) (b := -a) hne)
    simpa [hleft] using this
  refine ⟨-t, ?_⟩
  have hsub_le : μ + 1 - Real.exp (-t) ≤ t * (-a) - Real.exp (-t) :=
    sub_le_sub_right hmul' (Real.exp (-t))
  have hμlt : μ < μ + 1 - Real.exp (-t) := by
    have htmp : μ + 1 - 1 < μ + 1 - Real.exp (-t) := sub_lt_sub_left hexp (μ + 1)
    have hμ1 : μ + 1 - 1 = μ := by ring
    simpa [hμ1] using htmp
  have : μ < t * (-a) - Real.exp (-t) := lt_of_lt_of_le hμlt hsub_le
  have hta : (-t) * a = t * (-a) := by ring
  simpa [hta] using this

/-- For any negative `μ`, one can make `-exp x` exceed `μ` by choosing `x` very negative. -/
lemma exists_gt_neg_exp_of_neg_mu {μ : ℝ} (hμ : μ < 0) :
    ∃ x : ℝ, μ < -Real.exp x := by
  have hpos : 0 < -μ / 2 := by nlinarith
  refine ⟨Real.log (-μ / 2), ?_⟩
  have : -Real.exp (Real.log (-μ / 2)) = μ / 2 := by
    simp [Real.exp_log hpos]
    ring
  nlinarith [this]

/-- The `xStar 0 > 0` case for the conjugate of `x ↦ exp (x 0)` in dimension `1`. -/
lemma fenchelConjugate_exp_pos_case (xStar : Fin 1 → Real) (ha : 0 < xStar 0) :
    fenchelConjugate 1 (fun x : Fin 1 → Real => ((Real.exp (x 0) : Real) : EReal)) xStar =
      ((xStar 0 * Real.log (xStar 0) - xStar 0 : Real) : EReal) := by
  classical
  set a : ℝ := xStar 0
  have ha' : 0 < a := by simpa [a] using ha
  unfold fenchelConjugate
  refine le_antisymm ?_ ?_
  · refine sSup_le ?_
    rintro y ⟨x, rfl⟩
    have hreal :
        x 0 * a - Real.exp (x 0) ≤ a * Real.log a - a :=
      exp_linear_sub_exp_le_conjugateValue (a := a) (x := x 0) ha'
    have hE :
        ((x 0 * a - Real.exp (x 0) : Real) : EReal) ≤ ((a * Real.log a - a : Real) : EReal) := by
      exact_mod_cast hreal
    simpa [a, dotProduct, (EReal.coe_sub (x 0 * a) (Real.exp (x 0))).symm] using hE
  · have hsup :
        (((fun _ : Fin 1 => Real.log a) ⬝ᵥ xStar : Real) : EReal) -
            ((Real.exp ((fun _ : Fin 1 => Real.log a) 0) : Real) : EReal) ≤
          sSup
            (Set.range fun x : Fin 1 → Real =>
              ((x ⬝ᵥ xStar : Real) : EReal) - ((Real.exp (x 0) : Real) : EReal)) :=
      le_sSup ⟨(fun _ : Fin 1 => Real.log a), rfl⟩
    simpa [a, dotProduct, Real.exp_log ha', mul_comm,
      (EReal.coe_sub ((Real.log a) * a) (Real.exp (Real.log a))).symm] using hsup

/-- The `xStar 0 = 0` case for the conjugate of `x ↦ exp (x 0)` in dimension `1`. -/
lemma fenchelConjugate_exp_zero_case (xStar : Fin 1 → Real) (ha0 : xStar 0 = 0) :
    fenchelConjugate 1 (fun x : Fin 1 → Real => ((Real.exp (x 0) : Real) : EReal)) xStar = 0 := by
  classical
  -- Compare real upper bounds with `0`.
  refine EReal.eq_of_forall_le_coe_iff (a := fenchelConjugate 1
      (fun x : Fin 1 → Real => ((Real.exp (x 0) : Real) : EReal)) xStar) (b := (0 : EReal)) ?_
  intro μ
  constructor
  · intro hμ
    by_contra hμ0
    have hμ0' : ¬ (0 : Real) ≤ μ := by
      intro hμ0'
      exact hμ0 (by exact_mod_cast hμ0' : (0 : EReal) ≤ (μ : EReal))
    have hμneg : μ < 0 := lt_of_not_ge hμ0'
    rcases exists_gt_neg_exp_of_neg_mu (μ := μ) hμneg with ⟨x0, hx0⟩
    have hx0E : ((μ : Real) : EReal) < ((-Real.exp x0 : Real) : EReal) := by
      exact_mod_cast hx0
    -- The range element at `x = fun _ => x0` is `-exp x0`.
    have hle :
        ((-Real.exp x0 : Real) : EReal) ≤
          fenchelConjugate 1 (fun x : Fin 1 → Real => ((Real.exp (x 0) : Real) : EReal)) xStar := by
      unfold fenchelConjugate
      have := le_sSup
        (s := Set.range fun x : Fin 1 → Real =>
          ((x ⬝ᵥ xStar : Real) : EReal) - ((Real.exp (x 0) : Real) : EReal))
        ⟨(fun _ : Fin 1 => x0), rfl⟩
      -- Simplify the chosen element.
      simpa [dotProduct, ha0, (EReal.coe_sub (0 : Real) (Real.exp x0)).symm] using this
    have hlt : ((μ : Real) : EReal) < fenchelConjugate 1
        (fun x : Fin 1 → Real => ((Real.exp (x 0) : Real) : EReal)) xStar :=
      lt_of_lt_of_le hx0E hle
    exact (not_le_of_gt hlt) hμ
  · intro hμ
    have hle0 :
        fenchelConjugate 1 (fun x : Fin 1 → Real => ((Real.exp (x 0) : Real) : EReal)) xStar ≤
          (0 : EReal) := by
      unfold fenchelConjugate
      refine sSup_le ?_
      rintro y ⟨x, rfl⟩
      have hreal : (0 : Real) - Real.exp (x 0) ≤ 0 :=
        sub_nonpos.2 (le_of_lt (Real.exp_pos (x 0)))
      have hE : ((0 : Real) - Real.exp (x 0) : Real) ≤ 0 := hreal
      have hE' : (((0 : Real) - Real.exp (x 0) : Real) : EReal) ≤ (0 : EReal) := by
        exact_mod_cast hE
      -- Rewrite the range element.
      simpa [dotProduct, ha0, (EReal.coe_sub (0 : Real) (Real.exp (x 0))).symm] using hE'
    exact le_trans hle0 hμ

/-- The `xStar 0 < 0` case for the conjugate of `x ↦ exp (x 0)` in dimension `1`. -/
lemma fenchelConjugate_exp_neg_case (xStar : Fin 1 → Real) (ha : xStar 0 < 0) :
    fenchelConjugate 1 (fun x : Fin 1 → Real => ((Real.exp (x 0) : Real) : EReal)) xStar = ⊤ := by
  classical
  set a : ℝ := xStar 0
  have ha' : a < 0 := by simpa [a] using ha
  unfold fenchelConjugate
  refine (EReal.eq_top_iff_forall_lt _).2 ?_
  intro μ
  rcases exists_gt_linear_sub_exp_of_neg (a := a) (μ := μ) ha' with ⟨x0, hx0⟩
  have hx0E : ((μ : Real) : EReal) < ((x0 * a - Real.exp x0 : Real) : EReal) := by
    exact_mod_cast hx0
  have hle :
      ((x0 * a - Real.exp x0 : Real) : EReal) ≤
        sSup
          (Set.range fun x : Fin 1 → Real =>
            ((x ⬝ᵥ xStar : Real) : EReal) - ((Real.exp (x 0) : Real) : EReal)) := by
    have := le_sSup
      (s := Set.range fun x : Fin 1 → Real =>
        ((x ⬝ᵥ xStar : Real) : EReal) - ((Real.exp (x 0) : Real) : EReal))
      ⟨(fun _ : Fin 1 => x0), rfl⟩
    simpa [a, dotProduct, (EReal.coe_sub (x0 * a) (Real.exp x0)).symm] using this
  exact lt_of_lt_of_le hx0E hle

/-- Text 12.2.4: The conjugate function of the exponential function `f(x) = e^x` on `ℝ` is
given by the piecewise formula
`f*(x^*) = x^* log x^* - x^*` if `x^* > 0`, `f*(0) = 0`, and `f*(x^*) = +∞` if `x^* < 0`. -/
theorem fenchelConjugate_exp (xStar : Fin 1 → Real) :
    fenchelConjugate 1 (fun x : Fin 1 → Real => ((Real.exp (x 0) : Real) : EReal)) xStar =
      if xStar 0 > 0 then ((xStar 0 * Real.log (xStar 0) - xStar 0 : Real) : EReal)
      else if xStar 0 = 0 then (0 : EReal) else ⊤ := by
  by_cases hpos : 0 < xStar 0
  · have := fenchelConjugate_exp_pos_case (xStar := xStar) hpos
    simp [hpos, this]
  · by_cases hzero : xStar 0 = 0
    · have := fenchelConjugate_exp_zero_case (xStar := xStar) hzero
      simp [hzero, this]
    · have hneg : xStar 0 < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hzero
      have := fenchelConjugate_exp_neg_case (xStar := xStar) hneg
      simp [hpos, hzero, this]

/-- Turn the hypotheses `1 < p` and `1/p + 1/q = 1` into `p.HolderConjugate q`. -/
lemma holderConjugate_of_oneDiv_add_oneDiv_eq_one (p q : ℝ) (hp : 1 < p)
    (hpq : 1 / p + 1 / q = (1 : ℝ)) : p.HolderConjugate q := by
  refine (Real.holderConjugate_iff).2 ?_
  refine ⟨hp, ?_⟩
  simpa [one_div] using hpq

/-- Young's inequality rearranged as an upper bound for the Fenchel-conjugate range terms. -/
lemma range_term_le_conj_bound_oneDiv_mul_abs_rpow {p q a x : ℝ} (hpq : p.HolderConjugate q) :
    x * a - (1 / p) * Real.rpow (|x|) p ≤ (1 / q) * Real.rpow (|a|) q := by
  -- Switch to the `^` notation for `Real.rpow`.
  simp [Real.rpow_eq_pow]
  have hyoung : x * a ≤ |x| ^ p / p + |a| ^ q / q := Real.young_inequality x a hpq
  have hyoung' :
      x * a ≤ (1 / q) * (|a| ^ q) + (1 / p) * (|x| ^ p) := by
    -- Commute the summands and rewrite divisions as multiplication by inverses.
    simpa [div_eq_mul_inv, one_div, add_comm, add_left_comm, add_assoc, mul_assoc, mul_left_comm,
      mul_comm] using hyoung
  -- Move the `(1/p) * |x|^p` term to the left.
  have hsub :
      x * a - (1 / p) * (|x| ^ p) ≤ (1 / q) * (|a| ^ q) :=
    (sub_le_iff_le_add).2 (by simpa [add_assoc, add_left_comm, add_comm] using hyoung')
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm]
    using hsub

/-- Value of `x*a - (1/p)*|x|^p` at the explicit maximizer `x = sign(a) * |a|^(q-1)`. -/
lemma opt_value_oneDiv_mul_abs_rpow {p q : ℝ} (hpq : p.HolderConjugate q) (a : ℝ) :
    let x0 : ℝ := if 0 ≤ a then Real.rpow (|a|) (q - 1) else -Real.rpow (|a|) (q - 1)
    x0 * a - (1 / p) * Real.rpow (|x0|) p = (1 / q) * Real.rpow (|a|) q := by
  -- Switch to the `^` notation for `Real.rpow`.
  simp [Real.rpow_eq_pow]
  -- Put the candidate maximizer in a convenient form.
  let t : ℝ := |a| ^ (q - 1)
  have ht_nonneg : 0 ≤ t := by
    -- `|a|` is nonnegative, so any real power is nonnegative.
    simpa [t] using Real.rpow_nonneg (abs_nonneg a) (q - 1)
  let x0 : ℝ := if 0 ≤ a then t else -t
  -- Rewrite the goal in terms of `x0`.
  have hx0' :
      (if 0 ≤ a then |a| ^ (q - 1) * a else -(|a| ^ (q - 1) * a)) = x0 * a := by
    by_cases ha : 0 ≤ a <;> simp [x0, t, ha, mul_comm]
  have hx0_abs : |x0| = t := by
    by_cases ha : 0 ≤ a <;> simp [x0, t, ha, ht_nonneg]
  have hx0_mul : x0 * a = t * |a| := by
    by_cases ha : 0 ≤ a
    · have ha' : |a| = a := abs_of_nonneg ha
      simp [x0, t, ha, ha', mul_comm]
    · have ha' : a < 0 := lt_of_not_ge ha
      have ha'' : |a| = -a := abs_of_neg ha'
      calc
        x0 * a = (-t) * a := by simp [x0, t, ha]
        _ = t * (-a) := by ring
        _ = t * |a| := by simp [ha'']
  have hq_ne : q ≠ 0 := hpq.symm.ne_zero
  have hexp : (q - 1) * p = q := by
    have hpqmul : q * p = p + q := by simpa [mul_comm] using hpq.mul_eq_add
    calc
      (q - 1) * p = q * p - 1 * p := by ring
      _ = (p + q) - p := by simp [hpqmul]
      _ = q := by ring
  have ht_mul : t * |a| = |a| ^ q := by
    have h :=
      Real.rpow_add' (abs_nonneg a) (y := q - 1) (z := 1) (by simpa using hq_ne)
    have hsum : (q - 1) + 1 = q := by ring
    -- `t = |a|^(q-1)`.
    simpa [t, hsum, Real.rpow_one] using h.symm
  have ht_pow : t ^ p = |a| ^ q := by
    -- `( |a|^(q-1) )^p = |a|^((q-1)*p) = |a|^q`.
    have h := (Real.rpow_mul (abs_nonneg a) (q - 1) p).symm
    simpa [t, hexp] using h
  have hcoeff : (1 : ℝ) - p⁻¹ = q⁻¹ := by linarith [hpq.inv_add_inv_eq_one]
  -- Now compute the value at `x0`.
  calc
    (if 0 ≤ a then |a| ^ (q - 1) * a else -(|a| ^ (q - 1) * a)) - p⁻¹ * |if 0 ≤ a then |a| ^ (q - 1) else -|a| ^ (q - 1)| ^ p
        = x0 * a - p⁻¹ * |x0| ^ p := by
          have hx0_abs' :
              |if 0 ≤ a then |a| ^ (q - 1) else -|a| ^ (q - 1)| = |x0| := by
            simp [x0, t]
          calc
            (if 0 ≤ a then |a| ^ (q - 1) * a else -(|a| ^ (q - 1) * a)) -
                p⁻¹ * |if 0 ≤ a then |a| ^ (q - 1) else -|a| ^ (q - 1)| ^ p =
              x0 * a - p⁻¹ * |if 0 ≤ a then |a| ^ (q - 1) else -|a| ^ (q - 1)| ^ p := by
                simp [hx0']
            _ = x0 * a - p⁻¹ * |x0| ^ p := by
                simp [hx0_abs']
    _ = t * |a| - p⁻¹ * t ^ p := by simp [hx0_abs, hx0_mul]
    _ = |a| ^ q - p⁻¹ * |a| ^ q := by simp [ht_mul, ht_pow]
    _ = (1 - p⁻¹) * (|a| ^ q) := by ring
    _ = q⁻¹ * (|a| ^ q) := by simp [hcoeff]

/-- Text 12.2.5: Let `p ∈ (1, +∞)`. The conjugate of the function `f(x) = (1/p) * |x|^p` on `ℝ`
is given by `f*(x*) = (1/q) * |x*|^q`, where `1/p + 1/q = 1`. -/
theorem fenchelConjugate_oneDiv_mul_abs_rpow (p q : Real) (hp : 1 < p)
    (hpq : 1 / p + 1 / q = (1 : Real)) :
    ∀ xStar : Fin 1 → Real,
      fenchelConjugate 1
          (fun x : Fin 1 → Real =>
            (((1 / p) * Real.rpow (|x 0|) p : Real) : EReal))
          xStar =
        (((1 / q) * Real.rpow (|xStar 0|) q : Real) : EReal) := by
  classical
  intro xStar
  set a : ℝ := xStar 0
  have hpq' : p.HolderConjugate q :=
    holderConjugate_of_oneDiv_add_oneDiv_eq_one (p := p) (q := q) hp hpq
  -- Candidate maximizer (depends on the sign of `a`).
  set x0 : ℝ := if 0 ≤ a then Real.rpow (|a|) (q - 1) else -Real.rpow (|a|) (q - 1)
  have hx0 :
      x0 * a - (1 / p) * Real.rpow (|x0|) p = (1 / q) * Real.rpow (|a|) q := by
    simpa [x0, a] using (opt_value_oneDiv_mul_abs_rpow (p := p) (q := q) hpq' a)
  unfold fenchelConjugate
  refine le_antisymm ?_ ?_
  · -- Upper bound: each range term is bounded by `(1/q) * |a|^q`.
    refine sSup_le ?_
    rintro y ⟨x, rfl⟩
    have hreal :
        x 0 * a - (1 / p) * Real.rpow (|x 0|) p ≤ (1 / q) * Real.rpow (|a|) q :=
      range_term_le_conj_bound_oneDiv_mul_abs_rpow (p := p) (q := q) (a := a) (x := x 0) hpq'
    have hE :
        ((x 0 * a - (1 / p) * Real.rpow (|x 0|) p : ℝ) : EReal) ≤
          (((1 / q) * Real.rpow (|a|) q : ℝ) : EReal) := by
      exact_mod_cast hreal
    simpa [a, dotProduct,
      (EReal.coe_sub (x 0 * a) ((1 / p) * Real.rpow (|x 0|) p)).symm] using hE
  · -- Lower bound: evaluate at the explicit maximizer `x0`.
    have hsup :
        (((fun _ : Fin 1 => x0) ⬝ᵥ xStar : ℝ) : EReal) -
            (((1 / p) * Real.rpow (|(fun _ : Fin 1 => x0) 0|) p : ℝ) : EReal) ≤
          sSup
            (Set.range fun x : Fin 1 → Real =>
              ((x ⬝ᵥ xStar : ℝ) : EReal) -
                (((1 / p) * Real.rpow (|x 0|) p : ℝ) : EReal)) :=
      le_sSup ⟨(fun _ : Fin 1 => x0), rfl⟩
    have hx0E :
        ((x0 * a - (1 / p) * Real.rpow (|x0|) p : ℝ) : EReal) =
          (((1 / q) * Real.rpow (|a|) q : ℝ) : EReal) := by
      exact_mod_cast hx0
    -- Rewrite the chosen range element using the computed value.
    have hrepl :
        (((fun _ : Fin 1 => x0) ⬝ᵥ xStar : ℝ) : EReal) -
            (((1 / p) * Real.rpow (|(fun _ : Fin 1 => x0) 0|) p : ℝ) : EReal) =
          (((1 / q) * Real.rpow (|a|) q : ℝ) : EReal) := by
      simpa [a, dotProduct, mul_comm,
        (EReal.coe_sub (x0 * a) ((1 / p) * Real.rpow (|x0|) p)).symm] using hx0E
    -- Convert `hsup` into the desired lower bound.
    have hsup' := hsup
    rw [hrepl] at hsup'
    simpa [a] using hsup'

/-- Basic identities for `q` when `0 < p < 1` and `1/p + 1/q = 1`. -/
lemma q_neg_and_coeff_identities_of_oneDiv_add_oneDiv_eq_one {p q : Real} (hp0 : 0 < p)
    (hp1 : p < 1) (hpq : 1 / p + 1 / q = (1 : Real)) :
    q ≠ 0 ∧ q < 0 ∧ (1 / p - 1 = -(1 / q)) ∧ (q - 1) * p = q := by
  have hpne : p ≠ 0 := ne_of_gt hp0
  have hqne : q ≠ 0 := by
    intro hq0
    have h1 : (1 / p : ℝ) = 1 := by simpa [hq0] using hpq
    have hp_eq : (p : ℝ) = 1 := by
      have := congrArg (fun t : ℝ => t * p) h1
      -- `((1/p)*p) = 1*p`.
      simpa [one_div, hpne, mul_assoc] using this.symm
    have hp1' := hp1
    simp [hp_eq] at hp1'
  have hp_inv_gt_one : (1 : ℝ) < 1 / p := by
    have h := one_div_lt_one_div_of_lt hp0 hp1
    -- `1/1 < 1/p`.
    simpa using h
  have h1q : (1 / q : ℝ) = 1 - 1 / p := by linarith [hpq]
  have h1q_neg : (1 / q : ℝ) < 0 := by
    have : (1 - 1 / p : ℝ) < 0 := by linarith
    simpa [h1q] using this
  have hqneg : q < 0 := (inv_lt_zero).1 (by simpa [one_div] using h1q_neg)
  have hcoeff : (1 / p - 1 : ℝ) = -(1 / q) := by linarith [hpq]
  have hpqmul : (p : ℝ) * q = p + q := by
    have h := hpq
    field_simp [hpne, hqne] at h
    -- `q + p = p*q`.
    simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using h.symm
  have hmul : (q - 1) * p = q := by
    have hqp : q * p = p + q := by simpa [mul_comm] using hpqmul
    calc
      (q - 1) * p = q * p - 1 * p := by ring
      _ = (p + q) - p := by simp [hqp, mul_comm]
      _ = q := by ring
  exact ⟨hqne, hqneg, hcoeff, hmul⟩

/-- For `0 < p < 1` and `t ≥ 0`, we have the tangent-line upper bound
`t^p ≤ (1 - p) + p * t`. -/
lemma rpow_le_affine_at_one_of_lt_one {p t : Real} (hp0 : 0 < p) (hp1 : p < 1) (ht : 0 ≤ t) :
    Real.rpow t p ≤ (1 - p) + p * t := by
  have h :=
    Real.geom_mean_le_arith_mean2_weighted (w₁ := p) (w₂ := 1 - p) (p₁ := t) (p₂ := 1)
      (hw₁ := le_of_lt hp0) (hw₂ := by linarith) (hp₁ := ht) (hp₂ := by norm_num) (hw := by ring)
  -- Simplify the geometric mean term `t^p * 1^(1-p)`.
  simpa [Real.rpow_eq_pow, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
    h

/-- Value of `x*a + (1/p)*x^p` at the candidate maximizer `x0 = |a|^(q-1)` in the `a < 0` case. -/
lemma opt_value_neg_oneDiv_mul_rpow {p q a : Real} (hp0 : 0 < p) (hp1 : p < 1)
    (hpq : 1 / p + 1 / q = (1 : Real)) (ha : a < 0) :
    let x0 : Real := Real.rpow (|a|) (q - 1)
    x0 * a + (1 / p) * Real.rpow x0 p = (-(1 / q)) * Real.rpow (|a|) q := by
  rcases q_neg_and_coeff_identities_of_oneDiv_add_oneDiv_eq_one (p := p) (q := q) hp0 hp1 hpq with
    ⟨_hqne, _hqneg, hcoeff, hmul⟩
  have hpne : p ≠ 0 := ne_of_gt hp0
  set b : ℝ := |a|
  have hbpos : 0 < b := abs_pos.2 (ne_of_lt ha)
  have ha_eq : a = -b := by
    have : |a| = -a := abs_of_neg ha
    have hb : b = -a := by simpa [b] using this
    linarith
  set x0 : ℝ := Real.rpow b (q - 1)
  have hx0_mul_b : x0 * b = Real.rpow b q := by
    have h := (Real.rpow_add hbpos (q - 1) 1).symm
    have hsum : (q - 1) + 1 = q := by ring
    simpa [x0, Real.rpow_one, hsum, mul_assoc] using h
  have hx0a : x0 * a = -(Real.rpow b q) := by
    calc
      x0 * a = x0 * (-b) := by simp [ha_eq]
      _ = -(x0 * b) := by ring
      _ = -(Real.rpow b q) := by simp [hx0_mul_b]
  have hx0p : Real.rpow x0 p = Real.rpow b q := by
    have h := (Real.rpow_mul (le_of_lt hbpos) (q - 1) p).symm
    -- `(b^(q-1))^p = b^((q-1)*p) = b^q`.
    simpa [x0, hmul] using h
  -- Finish by direct computation.
  calc
    x0 * a + (1 / p) * Real.rpow x0 p = -(Real.rpow b q) + (1 / p) * Real.rpow b q := by
      rw [hx0a, hx0p]
    _ = (1 / p - 1) * Real.rpow b q := by ring
    _ = (-(1 / q)) * Real.rpow b q := by rw [hcoeff]
    _ = (-(1 / q)) * Real.rpow (|a|) q := by simp [b]

/-- For `a < 0`, each finite range term in the Fenchel conjugate is bounded above by the
optimal value `-(1/q) * |a|^q`. -/
lemma range_term_le_conjValue_neg_case {p q a x : Real} (hp0 : 0 < p) (hp1 : p < 1)
    (hpq : 1 / p + 1 / q = (1 : Real)) (ha : a < 0) (hx : 0 ≤ x) :
    x * a + (1 / p) * Real.rpow x p ≤ (-(1 / q)) * Real.rpow (|a|) q := by
  rcases q_neg_and_coeff_identities_of_oneDiv_add_oneDiv_eq_one (p := p) (q := q) hp0 hp1 hpq with
    ⟨_hqne, _hqneg, hcoeff, hmul⟩
  have hpne : p ≠ 0 := ne_of_gt hp0
  -- Switch to the `^` notation for `Real.rpow`.
  simp [Real.rpow_eq_pow]
  set b : ℝ := |a|
  have hbpos : 0 < b := abs_pos.2 (ne_of_lt ha)
  have ha_eq : a = -b := by
    have : |a| = -a := abs_of_neg ha
    have hb : b = -a := by simpa [b] using this
    linarith
  set x0 : ℝ := b ^ (q - 1)
  have hx0pos : 0 < x0 := by
    simpa [x0, Real.rpow_eq_pow] using Real.rpow_pos_of_pos hbpos (q - 1)
  have hx0ne : x0 ≠ 0 := ne_of_gt hx0pos
  set t : ℝ := x / x0
  have ht : 0 ≤ t := div_nonneg hx (le_of_lt hx0pos)
  have hx_eq : x0 * t = x := by
    simpa [t] using (mul_div_cancel₀ (a := x) (b := x0) hx0ne)
  have hx_decomp : x = x0 * t := hx_eq.symm
  have hx0pow : x0 ^ p = b ^ q := by
    have h := (Real.rpow_mul (le_of_lt hbpos) (q - 1) p).symm
    -- `(b^(q-1))^p = b^((q-1)*p) = b^q`.
    simpa [x0, hmul] using h
  have hx0_mul_b : x0 * b = b ^ q := by
    have h := (Real.rpow_add hbpos (q - 1) 1).symm
    have hsum : (q - 1) + 1 = q := by ring
    simpa [x0, Real.rpow_one, hsum, mul_assoc] using h
  have hx0a : x0 * a = -(b ^ q) := by
    calc
      x0 * a = x0 * (-b) := by simp [ha_eq]
      _ = -(x0 * b) := by ring
      _ = -(b ^ q) := by simp [hx0_mul_b]
  have hxpow : (x0 * t) ^ p = b ^ q * t ^ p := by
    calc
      (x0 * t) ^ p = x0 ^ p * t ^ p := by
        simpa using (Real.mul_rpow (x := x0) (y := t) (z := p) (le_of_lt hx0pos) ht)
      _ = b ^ q * t ^ p := by simp [hx0pow]
  have ht_pow : t ^ p ≤ (1 - p) + p * t := by
    -- Use the tangent-line bound at `t = 1`.
    simpa [Real.rpow_eq_pow] using rpow_le_affine_at_one_of_lt_one (p := p) hp0 hp1 (t := t) ht
  have ht_ineq : p⁻¹ * t ^ p - t ≤ p⁻¹ - 1 := by
    have hmul' : p⁻¹ * t ^ p ≤ p⁻¹ * ((1 - p) + p * t) :=
      mul_le_mul_of_nonneg_left ht_pow (by positivity)
    have hmul'' : p⁻¹ * ((1 - p) + p * t) = (p⁻¹ - 1) + t := by
      calc
        p⁻¹ * ((1 - p) + p * t) = p⁻¹ * (1 - p) + p⁻¹ * (p * t) := by ring
        _ = (p⁻¹ - 1) + t := by
          have h1 : (p⁻¹ : ℝ) * (1 - p) = p⁻¹ - 1 := by
            calc
              (p⁻¹ : ℝ) * (1 - p) = (p⁻¹ : ℝ) * 1 - (p⁻¹ : ℝ) * p := by ring
              _ = p⁻¹ - 1 := by simp [hpne]
          simp [h1, hpne]
    have hmul''' : p⁻¹ * t ^ p ≤ (p⁻¹ - 1) + t := by simpa [hmul''] using hmul'
    exact (sub_le_iff_le_add).2 hmul'''
  have hbq_nonneg : 0 ≤ b ^ q := by
    -- `b = |a|` is nonnegative.
    simpa [b, Real.rpow_eq_pow] using Real.rpow_nonneg (abs_nonneg a) q
  have hscaled : b ^ q * (p⁻¹ * t ^ p - t) ≤ b ^ q * (p⁻¹ - 1) :=
    mul_le_mul_of_nonneg_left ht_ineq hbq_nonneg
  have hx_lhs : x * a + p⁻¹ * x ^ p = b ^ q * (p⁻¹ * t ^ p - t) := by
    calc
      x * a + p⁻¹ * x ^ p = (x0 * t) * a + p⁻¹ * (x0 * t) ^ p := by
        simp [hx_decomp]
      _ = (x0 * a) * t + p⁻¹ * (b ^ q * t ^ p) := by
        simp [hxpow, mul_left_comm, mul_comm]
      _ = (-(b ^ q)) * t + p⁻¹ * (b ^ q * t ^ p) := by simp [hx0a]
      _ = b ^ q * (p⁻¹ * t ^ p - t) := by ring
  have hcoeff' : (p⁻¹ - 1 : ℝ) = -q⁻¹ := by simpa [one_div] using hcoeff
  have hrhs : b ^ q * (p⁻¹ - 1) = -(b ^ q * q⁻¹) := by
    calc
      b ^ q * (p⁻¹ - 1) = b ^ q * (-q⁻¹) := by simp [hcoeff']
      _ = -(b ^ q * q⁻¹) := by ring
  have : x * a + p⁻¹ * x ^ p ≤ -(b ^ q * q⁻¹) := by
    have : b ^ q * (p⁻¹ * t ^ p - t) ≤ -(b ^ q * q⁻¹) := by simpa [hrhs] using hscaled
    simpa [hx_lhs] using this
  simpa [b, mul_assoc, mul_left_comm, mul_comm] using this

/-- The `xStar 0 ≥ 0` case: the conjugate is unbounded above, hence `⊤`. -/
lemma fenchelConjugate_neg_oneDiv_mul_rpow_top_case (p : Real) (hp0 : 0 < p) (xStar : Fin 1 → ℝ)
    (ha : 0 ≤ xStar 0) :
    fenchelConjugate 1
        (fun x : Fin 1 → ℝ =>
          if 0 ≤ x 0 then ((-(1 / p) * Real.rpow (x 0) p : ℝ) : EReal) else ⊤)
        xStar = ⊤ := by
  unfold fenchelConjugate
  refine (EReal.eq_top_iff_forall_lt _).2 ?_
  intro μ
  by_cases hμ : μ < 0
  · -- Use `x = 0`.
    have hμE : ((μ : ℝ) : EReal) < ((0 : ℝ) : EReal) := by exact_mod_cast hμ
    have hle :
        ((0 : ℝ) : EReal) ≤
          sSup
            (Set.range fun x : Fin 1 → ℝ =>
              ((x ⬝ᵥ xStar : ℝ) : EReal) -
                (if 0 ≤ x 0 then ((-(1 / p) * Real.rpow (x 0) p : ℝ) : EReal) else ⊤)) := by
      have := le_sSup
        (s := Set.range fun x : Fin 1 → ℝ =>
          ((x ⬝ᵥ xStar : ℝ) : EReal) -
            (if 0 ≤ x 0 then ((-(1 / p) * Real.rpow (x 0) p : ℝ) : EReal) else ⊤))
        ⟨(fun _ : Fin 1 => (0 : ℝ)), rfl⟩
      have hpne : (p : ℝ) ≠ 0 := ne_of_gt hp0
      simpa [dotProduct, hpne, (EReal.coe_sub (0 : ℝ) (0 : ℝ)).symm, Real.zero_rpow hpne] using this
    exact lt_of_lt_of_le hμE hle
  · -- Use a large `x ≥ 0` so that `(1/p)*x^p > μ` (and add the nonnegative linear part).
    have hμ0 : 0 ≤ μ := le_of_not_gt hμ
    have hpne : (p : ℝ) ≠ 0 := ne_of_gt hp0
    set c : ℝ := p * (μ + 1)
    have hcpos : 0 < c := by nlinarith [hp0, hμ0]
    set x0 : ℝ := Real.rpow c (1 / p)
    have hx0nonneg : 0 ≤ x0 := by
      simpa [x0] using Real.rpow_nonneg (le_of_lt hcpos) (1 / p)
    have hx0pow : Real.rpow x0 p = c := by
      have h := (Real.rpow_mul (le_of_lt hcpos) (1 / p) p).symm
      have hmul : (p⁻¹ : ℝ) * p = 1 := by simp [hpne]
      simpa [x0, one_div, hmul, Real.rpow_one] using h
    have hx0term : (1 / p) * Real.rpow x0 p = μ + 1 := by
      calc
        (1 / p) * Real.rpow x0 p = (1 / p) * c := by rw [hx0pow]
        _ = μ + 1 := by
          -- `c = p * (μ + 1)`.
          simp [c, one_div, hpne]
    have hx0a_nonneg : 0 ≤ x0 * xStar 0 := mul_nonneg hx0nonneg ha
    have hreal : μ < x0 * xStar 0 + (1 / p) * Real.rpow x0 p := by
      have : μ < μ + 1 := by linarith
      linarith [this, hx0a_nonneg, hx0term]
    have hrealE :
        ((μ : ℝ) : EReal) < ((x0 * xStar 0 + (1 / p) * Real.rpow x0 p : ℝ) : EReal) := by
      exact_mod_cast hreal
    have hle :
        ((x0 * xStar 0 + (1 / p) * Real.rpow x0 p : ℝ) : EReal) ≤
          sSup
            (Set.range fun x : Fin 1 → ℝ =>
              ((x ⬝ᵥ xStar : ℝ) : EReal) -
                (if 0 ≤ x 0 then ((-(1 / p) * Real.rpow (x 0) p : ℝ) : EReal) else ⊤)) := by
      have := le_sSup
        (s := Set.range fun x : Fin 1 → ℝ =>
          ((x ⬝ᵥ xStar : ℝ) : EReal) -
            (if 0 ≤ x 0 then ((-(1 / p) * Real.rpow (x 0) p : ℝ) : EReal) else ⊤))
        ⟨(fun _ : Fin 1 => x0), rfl⟩
      -- Simplify the chosen range element (rewriting `a - (-b)` as `a + b`).
      simpa [dotProduct, hx0nonneg, sub_eq_add_neg, add_assoc, add_comm, add_left_comm, mul_assoc,
        mul_left_comm, mul_comm, (EReal.coe_sub (x0 * xStar 0) (-(1 / p) * Real.rpow x0 p)).symm] using
        this
    exact lt_of_lt_of_le hrealE hle

/-- Text 12.2.6: Let `0 < p < 1`. Consider the extended-real function on `ℝ` given by
`f(x) = -(1/p) * x^p` for `x ≥ 0` and `f(x) = +∞` otherwise. Its conjugate has the piecewise
formula `f*(x*) = -(1/q) * |x*|^q` for `x* < 0` and `f*(x*) = +∞` for `x* ≥ 0`, where
`1/p + 1/q = 1` (in particular `q < 0`). -/
theorem fenchelConjugate_neg_oneDiv_mul_rpow (p q : Real) (hp0 : 0 < p) (hp1 : p < 1)
    (hpq : 1 / p + 1 / q = (1 : Real)) :
    ∀ xStar : Fin 1 → Real,
      fenchelConjugate 1
          (fun x : Fin 1 → Real =>
            if 0 ≤ x 0 then ((-(1 / p) * Real.rpow (x 0) p : Real) : EReal) else ⊤)
          xStar =
        if xStar 0 < 0 then ((-(1 / q) * Real.rpow (|xStar 0|) q : Real) : EReal) else ⊤ := by
  classical
  intro xStar
  by_cases ha : xStar 0 < 0
  · -- Negative `xStar 0`: finite conjugate value.
    set a : ℝ := xStar 0
    have ha' : a < 0 := by simpa [a] using ha
    unfold fenchelConjugate
    simp [ha]
    refine le_antisymm ?_ ?_
    · refine sSup_le ?_
      rintro y ⟨x, rfl⟩
      by_cases hx : 0 ≤ x 0
      · have hreal :
            x 0 * a + (1 / p) * Real.rpow (x 0) p ≤ (-(1 / q)) * Real.rpow (|a|) q :=
          range_term_le_conjValue_neg_case (p := p) (q := q) (a := a) (x := x 0) hp0 hp1 hpq ha' hx
        have hE :
            ((x 0 * a + (1 / p) * Real.rpow (x 0) p : ℝ) : EReal) ≤
              (((-(1 / q)) * Real.rpow (|a|) q : ℝ) : EReal) := by
          exact_mod_cast hreal
        simpa [a, dotProduct, hx, sub_eq_add_neg, add_assoc, add_comm, add_left_comm, mul_assoc,
          mul_left_comm, mul_comm,
          (EReal.coe_sub (x 0 * a) (-(1 / p) * Real.rpow (x 0) p)).symm] using hE
      · -- If `x 0 < 0`, the range term is `⊥`.
        simp [hx]
    · -- Evaluate at the explicit maximizer `x0 = |a|^(q-1)`.
      set x0 : ℝ := Real.rpow (|a|) (q - 1)
      have hx0 : 0 ≤ x0 := Real.rpow_nonneg (abs_nonneg a) (q - 1)
      have hx0_val :
          x0 * a + (1 / p) * Real.rpow x0 p = (-(1 / q)) * Real.rpow (|a|) q := by
        simpa [x0] using (opt_value_neg_oneDiv_mul_rpow (p := p) (q := q) (a := a) hp0 hp1 hpq ha')
      have hsup :
          (((fun _ : Fin 1 => x0) ⬝ᵥ xStar : ℝ) : EReal) -
              (if 0 ≤ (fun _ : Fin 1 => x0) 0 then
                ((-(1 / p) * Real.rpow ((fun _ : Fin 1 => x0) 0) p : ℝ) : EReal) else ⊤) ≤
            sSup
              (Set.range fun x : Fin 1 → ℝ =>
                ((x ⬝ᵥ xStar : ℝ) : EReal) -
                  (if 0 ≤ x 0 then ((-(1 / p) * Real.rpow (x 0) p : ℝ) : EReal) else ⊤)) :=
        le_sSup ⟨(fun _ : Fin 1 => x0), rfl⟩
      have hsup' :
          ((x0 * a + (1 / p) * Real.rpow x0 p : ℝ) : EReal) ≤
            sSup
              (Set.range fun x : Fin 1 → ℝ =>
                ((x ⬝ᵥ xStar : ℝ) : EReal) -
                  (if 0 ≤ x 0 then ((-(1 / p) * Real.rpow (x 0) p : ℝ) : EReal) else ⊤)) := by
        simpa [a, dotProduct, hx0, sub_eq_add_neg, add_assoc, add_comm, add_left_comm,
          mul_assoc, mul_left_comm, mul_comm,
          (EReal.coe_sub (x0 * a) (-(1 / p) * Real.rpow x0 p)).symm] using hsup
      have hx0E :
          (↑a * ↑x0 + ↑p⁻¹ * ↑(x0 ^ p) : EReal) = -(↑q⁻¹ * ↑(|a| ^ q)) := by
        have hx0E' :
            ((x0 * a + (1 / p) * Real.rpow x0 p : ℝ) : EReal) =
              (((-(1 / q)) * Real.rpow (|a|) q : ℝ) : EReal) := by
          exact_mod_cast hx0_val
        simpa [one_div, Real.rpow_eq_pow, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_comm,
          add_left_comm] using hx0E'
      -- Rewrite the chosen range element using the computed value.
      simpa [hx0E, one_div, Real.rpow_eq_pow, mul_assoc, mul_left_comm, mul_comm, add_assoc,
        add_comm, add_left_comm] using hsup'
  · -- Nonnegative `xStar 0`: unbounded above.
    have ha0 : 0 ≤ xStar 0 := le_of_not_gt ha
    have htop := fenchelConjugate_neg_oneDiv_mul_rpow_top_case (p := p) hp0 xStar ha0
    simpa [ha] using htop

end Section12
end Chap03
