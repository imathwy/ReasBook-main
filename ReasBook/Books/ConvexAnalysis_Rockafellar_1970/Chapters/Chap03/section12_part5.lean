/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Zhiyan Wang, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section12_part4

section Chap03
section Section12

/-- Simplify the Fenchel-conjugate range term for the function
`x ↦ if |x| ≤ a then -√(a^2-x^2) else +∞` in dimension `1`. -/
lemma range_term_neg_sqrt_sq_sub_sq_simp (a : Real) (x xStar : Fin 1 → Real) :
    (((x ⬝ᵥ xStar : Real) : EReal) -
        (if |x 0| ≤ a then ((-Real.sqrt (a ^ 2 - (x 0) ^ 2) : Real) : EReal) else ⊤)) =
      if |x 0| ≤ a then
        ((x 0 * xStar 0 + Real.sqrt (a ^ 2 - (x 0) ^ 2) : Real) : EReal)
      else ⊥ := by
  by_cases hx : |x 0| ≤ a
  · -- Inside the constraint we get a real value `x*s + √(a^2-x^2)`.
    have hdot : (x ⬝ᵥ xStar : Real) = x 0 * xStar 0 := by simp [dotProduct]
    -- Avoid `simp` rewriting `((x 0 * xStar 0 : Real) : EReal)` into a product in `EReal`,
    -- so that we can apply `EReal.coe_sub` cleanly.
    rw [if_pos hx, if_pos hx, hdot]
    rw [(EReal.coe_sub (x 0 * xStar 0) (-Real.sqrt (a ^ 2 - (x 0) ^ 2))).symm]
    simp [sub_neg_eq_add]
  · -- Outside the constraint, subtracting `⊤` yields `⊥`.
    simp [hx]

/-- A Cauchy–Schwarz-type bound for the range terms
`x*s + √(a^2-x^2)` under the constraint `|x| ≤ a` and `a ≥ 0`. -/
lemma mul_add_sqrt_sq_sub_sq_le {a x s : Real} (ha : 0 ≤ a) (hx : |x| ≤ a) :
    x * s + Real.sqrt (a ^ 2 - x ^ 2) ≤ a * Real.sqrt (1 + s ^ 2) := by
  have hx2 : x ^ 2 ≤ a ^ 2 := by
    have hx' : |x| ≤ |a| := by simpa [abs_of_nonneg ha] using hx
    exact (sq_le_sq).2 hx'
  have hnonneg : 0 ≤ a ^ 2 - x ^ 2 := sub_nonneg.2 hx2
  set y : Real := Real.sqrt (a ^ 2 - x ^ 2)
  have hy2 : y ^ 2 = a ^ 2 - x ^ 2 := by
    simpa [y] using (Real.sq_sqrt hnonneg)
  have hsum : x ^ 2 + y ^ 2 = a ^ 2 := by
    nlinarith [hy2]
  have hcs : (x * s + y) ^ 2 ≤ (x ^ 2 + y ^ 2) * (s ^ 2 + 1) := by
    have hdiff : 0 ≤ (x ^ 2 + y ^ 2) * (s ^ 2 + 1) - (x * s + y) ^ 2 := by
      have : (x ^ 2 + y ^ 2) * (s ^ 2 + 1) - (x * s + y) ^ 2 = (x - y * s) ^ 2 := by ring
      simpa [this] using sq_nonneg (x - y * s)
    linarith
  have hcs' : (x * s + y) ^ 2 ≤ a ^ 2 * (1 + s ^ 2) := by
    simpa [hsum, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using hcs
  have hz : 0 ≤ (1 + s ^ 2) := by nlinarith
  have hsq :
      (x * s + y) ^ 2 ≤ (a * Real.sqrt (1 + s ^ 2)) ^ 2 := by
    have hR : (a * Real.sqrt (1 + s ^ 2)) ^ 2 = a ^ 2 * (1 + s ^ 2) := by
      calc
        (a * Real.sqrt (1 + s ^ 2)) ^ 2 = a ^ 2 * (Real.sqrt (1 + s ^ 2)) ^ 2 := by ring
        _ = a ^ 2 * (1 + s ^ 2) := by simp [Real.sq_sqrt hz]
    simpa [hR] using hcs'
  have hB : 0 ≤ a * Real.sqrt (1 + s ^ 2) := by
    exact mul_nonneg ha (Real.sqrt_nonneg _)
  have habs' :
      |x * s + y| ≤ |a * Real.sqrt (1 + s ^ 2)| := (sq_le_sq).1 hsq
  have habs : |x * s + y| ≤ a * Real.sqrt (1 + s ^ 2) := by
    simpa [abs_of_nonneg hB] using habs'
  have hle : x * s + y ≤ a * Real.sqrt (1 + s ^ 2) := le_trans (le_abs_self _) habs
  simpa [y] using hle

/-- A concrete point `x0` achieving the upper bound in `mul_add_sqrt_sq_sub_sq_le`. -/
lemma exists_argmax_mul_add_sqrt_sq_sub_sq (a s : Real) (ha : 0 ≤ a) :
    ∃ x0 : Real, |x0| ≤ a ∧ x0 * s + Real.sqrt (a ^ 2 - x0 ^ 2) = a * Real.sqrt (1 + s ^ 2) := by
  set t : Real := Real.sqrt (1 + s ^ 2)
  have ht_pos : 0 < t := by
    have : 0 < (1 + s ^ 2) := by nlinarith
    simpa [t] using Real.sqrt_pos.2 this
  have ht_ne : t ≠ 0 := ne_of_gt ht_pos
  set x0 : Real := a * s / t
  refine ⟨x0, ?_, ?_⟩
  · have hs_le_t : |s| ≤ t := by
      have hs2 : s ^ 2 ≤ 1 + s ^ 2 := by nlinarith
      simpa [t] using (Real.abs_le_sqrt (x := s) (y := 1 + s ^ 2) hs2)
    have hdiv : |s| / t ≤ 1 := (div_le_one ht_pos).2 hs_le_t
    have hmul : a * (|s| / t) ≤ a := by
      simpa using (mul_le_mul_of_nonneg_left hdiv ha)
    have habs_x0 : |x0| = a * (|s| / t) := by
      simp [x0, abs_mul, abs_of_nonneg ha, abs_of_pos ht_pos, mul_assoc, div_eq_mul_inv]
    simpa [habs_x0] using hmul
  · have hz : 0 ≤ (1 + s ^ 2) := by nlinarith
    have ht2 : t ^ 2 = 1 + s ^ 2 := by
      simpa [t] using (Real.sq_sqrt hz)
    have hrad : a ^ 2 - x0 ^ 2 = (a / t) ^ 2 := by
      dsimp [x0]
      field_simp [ht_ne]
      ring_nf
      nlinarith [ht2]
    have hsqrt : Real.sqrt (a ^ 2 - x0 ^ 2) = a / t := by
      have hrad_nonneg : 0 ≤ a ^ 2 - x0 ^ 2 := by
        rw [hrad]
        exact sq_nonneg (a / t)
      have hdiv_nonneg : 0 ≤ a / t := div_nonneg ha (le_of_lt ht_pos)
      exact (Real.sqrt_eq_iff_mul_self_eq hrad_nonneg hdiv_nonneg).2 (by simpa [pow_two] using hrad)
    have ht2' : t ^ 2 = s ^ 2 + 1 := by simpa [add_comm, add_left_comm, add_assoc] using ht2
    have hdivt : (s ^ 2 + 1) / t = t := by
      calc
        (s ^ 2 + 1) / t = (t ^ 2) / t := by simp [ht2'.symm]
        _ = t := by simp [pow_two, ht_ne]
    calc
      x0 * s + Real.sqrt (a ^ 2 - x0 ^ 2)
          = x0 * s + a / t := by simp [hsqrt]
      _ = a * ((s ^ 2 + 1) / t) := by
        simp [x0]
        ring
      _ = a * t := by simp [hdivt]
      _ = a * Real.sqrt (1 + s ^ 2) := by simp [t]

/-- Text 12.2.7: Let `f : ℝ → [-∞, +∞]` be the extended-real function
`f(x) = -√(a^2 - x^2)` for `|x| ≤ a` (with `a ≥ 0`) and `f(x) = +∞` otherwise. Then its
conjugate is given by `f*(x*) = a * √(1 + x*^2)`. Here the conjugate is represented by
`fenchelConjugate`. -/
theorem fenchelConjugate_neg_sqrt_sq_sub_sq (a : Real) (ha : 0 ≤ a) :
    ∀ xStar : Fin 1 → Real,
      fenchelConjugate 1
          (fun x : Fin 1 → Real =>
            if |x 0| ≤ a then ((-Real.sqrt (a ^ 2 - (x 0) ^ 2) : Real) : EReal) else ⊤)
          xStar =
        ((a * Real.sqrt (1 + (xStar 0) ^ 2) : Real) : EReal) := by
  classical
  intro xStar
  unfold fenchelConjugate
  refine le_antisymm ?_ ?_
  · refine sSup_le ?_
    rintro y ⟨x, rfl⟩
    dsimp
    have hsqrt_cast :
        -((Real.sqrt (a ^ 2 - x 0 ^ 2) : Real) : EReal) =
          ((-Real.sqrt (a ^ 2 - x 0 ^ 2) : Real) : EReal) := by
      simp
    -- Normalize the `if`-branch to match `range_term_neg_sqrt_sq_sub_sq_simp`.
    rw [hsqrt_cast]
    by_cases hx : |x 0| ≤ a
    · have hreal :
          x 0 * xStar 0 + Real.sqrt (a ^ 2 - (x 0) ^ 2) ≤ a * Real.sqrt (1 + (xStar 0) ^ 2) :=
        mul_add_sqrt_sq_sub_sq_le (a := a) (x := x 0) (s := xStar 0) ha hx
      have hE :
          ((x 0 * xStar 0 + Real.sqrt (a ^ 2 - (x 0) ^ 2) : Real) : EReal) ≤
            ((a * Real.sqrt (1 + (xStar 0) ^ 2) : Real) : EReal) := by
        exact_mod_cast hreal
      rw [range_term_neg_sqrt_sq_sub_sq_simp (a := a) (x := x) (xStar := xStar)]
      simp [hx]
      exact hE
    · rw [range_term_neg_sqrt_sq_sub_sq_simp (a := a) (x := x) (xStar := xStar)]
      simp [hx]
  · -- Choose a concrete maximizer to get the lower bound.
    rcases exists_argmax_mul_add_sqrt_sq_sub_sq (a := a) (s := xStar 0) ha with ⟨x0, hx0, hval⟩
    let x : Fin 1 → Real := fun _ => x0
    have hx0' : |x 0| ≤ a := by simpa [x] using hx0
    have hle :
        ((x ⬝ᵥ xStar : Real) : EReal) -
            (if |x 0| ≤ a then ((-Real.sqrt (a ^ 2 - (x 0) ^ 2) : Real) : EReal) else ⊤) ≤
          sSup
            (Set.range fun x : Fin 1 → Real =>
              ((x ⬝ᵥ xStar : Real) : EReal) -
                (if |x 0| ≤ a then ((-Real.sqrt (a ^ 2 - (x 0) ^ 2) : Real) : EReal) else ⊤)) :=
      le_sSup ⟨x, rfl⟩
    have hrange :
        ((x ⬝ᵥ xStar : Real) : EReal) -
            (if |x 0| ≤ a then ((-Real.sqrt (a ^ 2 - (x 0) ^ 2) : Real) : EReal) else ⊤) =
          ((a * Real.sqrt (1 + (xStar 0) ^ 2) : Real) : EReal) := by
      rw [range_term_neg_sqrt_sq_sub_sq_simp (a := a) (x := x) (xStar := xStar)]
      simp [hx0', x, hval]
    have hle' := hle
    rw [hrange] at hle'
    exact hle'

/-- Text 12.2.8: Consider `f(x) = -log x - 1/2` for `x > 0` (and `+∞` otherwise). The conjugate is
given by
`f*(x*) = -log(-x*) - 1/2` if `x* < 0` and `f*(x*) = +∞` if `x* ≥ 0`. Here the conjugate is
represented by `fenchelConjugate`. -/
theorem fenchelConjugate_neg_log_sub_oneHalf :
    ∀ xStar : Fin 1 → Real,
      fenchelConjugate 1
          (fun x : Fin 1 → Real =>
            if 0 < x 0 then ((-Real.log (x 0) - (1 / 2 : Real) : Real) : EReal) else ⊤)
          xStar =
        if xStar 0 < 0 then ((-Real.log (-xStar 0) - (1 / 2 : Real) : Real) : EReal) else ⊤ := by
  classical
  intro xStar
  by_cases hs : xStar 0 < 0
  · -- Finite conjugate value for negative `x*`.
    rw [if_pos hs]
    unfold fenchelConjugate
    refine le_antisymm ?_ ?_
    · refine sSup_le ?_
      rintro y ⟨x, rfl⟩
      dsimp
      by_cases hx : 0 < x 0
      · have hdot : (x ⬝ᵥ xStar : Real) = x 0 * xStar 0 := by simp [dotProduct]
        -- Reduce to a real inequality using `log_le_sub_one_of_pos`.
        have hreal :
            x 0 * xStar 0 + Real.log (x 0) + (1 / 2 : Real) ≤
              -Real.log (-xStar 0) - (1 / 2 : Real) := by
          have ha : 0 < -xStar 0 := by linarith
          have ht : 0 < (-xStar 0) * x 0 := mul_pos ha hx
          have hlog_le :
              Real.log ((-xStar 0) * x 0) ≤ (-xStar 0) * x 0 - 1 :=
            Real.log_le_sub_one_of_pos ht
          have hlog_minus :
              Real.log ((-xStar 0) * x 0) - (-xStar 0) * x 0 ≤ (-1 : Real) := by
            have := sub_le_sub_right hlog_le ((-xStar 0) * x 0)
            nlinarith
          have ha_ne : (-xStar 0) ≠ 0 := ne_of_gt ha
          have hx_ne : x 0 ≠ 0 := ne_of_gt hx
          have hlog_mul :
              Real.log ((-xStar 0) * x 0) = Real.log (-xStar 0) + Real.log (x 0) := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using (Real.log_mul ha_ne hx_ne)
          have hlogx :
              Real.log (x 0) = Real.log ((-xStar 0) * x 0) - Real.log (-xStar 0) := by
            linarith [hlog_mul]
          have hmul : x 0 * xStar 0 = -((-xStar 0) * x 0) := by ring
          have hmain : x 0 * xStar 0 + Real.log (x 0) ≤ -Real.log (-xStar 0) - 1 := by
            have h1 :
                Real.log ((-xStar 0) * x 0) - (-xStar 0) * x 0 - Real.log (-xStar 0) ≤
                  -Real.log (-xStar 0) - 1 := by
              linarith [hlog_minus]
            have h2 :
                x 0 * xStar 0 + Real.log (x 0) =
                  Real.log ((-xStar 0) * x 0) - (-xStar 0) * x 0 - Real.log (-xStar 0) := by
              simp [hmul, hlogx]
              ring_nf
            simpa [h2] using h1
          linarith [hmain]
        have hE :
            ((x 0 * xStar 0 + Real.log (x 0) + (1 / 2 : Real) : Real) : EReal) ≤
              ((-Real.log (-xStar 0) - (1 / 2 : Real) : Real) : EReal) := by
          exact_mod_cast hreal
        have hrange :
            (((x 0 * xStar 0 : Real) : EReal) -
                ((-Real.log (x 0) - (1 / 2 : Real) : Real) : EReal)) =
              ((x 0 * xStar 0 + Real.log (x 0) + (1 / 2 : Real) : Real) : EReal) := by
          rw [(EReal.coe_sub (x 0 * xStar 0) (-Real.log (x 0) - (1 / 2 : Real))).symm]
          ring_nf
        rw [if_pos hx, hdot]
        have hlog_cast :
            (-((Real.log (x 0) : Real) : EReal) - ((1 / 2 : Real) : EReal)) =
              ((-Real.log (x 0) - (1 / 2 : Real) : Real) : EReal) := by
          simp
        have hlog_castStar :
            (-((Real.log (-xStar 0) : Real) : EReal) - ((1 / 2 : Real) : EReal)) =
              ((-Real.log (-xStar 0) - (1 / 2 : Real) : Real) : EReal) := by
          simp
        rw [hlog_cast, hlog_castStar]
        rw [hrange]
        exact hE
      · simp [hx]
    · -- Achieve the value at the explicit maximizer `x0 = 1/(-x*)`.
      let x0 : Real := 1 / (-xStar 0)
      have hx0 : 0 < x0 := by
        have : 0 < -xStar 0 := by linarith
        simpa [x0] using (one_div_pos.2 this)
      let x : Fin 1 → Real := fun _ => x0
      have hle :
          (((x ⬝ᵥ xStar : Real) : EReal) -
                (if 0 < x 0 then ((-Real.log (x 0) - (1 / 2 : Real) : Real) : EReal) else ⊤)) ≤
              sSup
                (Set.range fun x : Fin 1 → Real =>
                  ((x ⬝ᵥ xStar : Real) : EReal) -
                    (if 0 < x 0 then ((-Real.log (x 0) - (1 / 2 : Real) : Real) : EReal) else ⊤)) :=
        le_sSup ⟨x, rfl⟩
      have hs_ne : xStar 0 ≠ 0 := ne_of_lt hs
      have hx0s : x0 * xStar 0 = (-1 : Real) := by
        dsimp [x0]
        field_simp [hs_ne]
      have hlog : Real.log x0 = -Real.log (-xStar 0) := by
        dsimp [x0]
        simp [one_div, Real.log_inv]
      have hdot : (x ⬝ᵥ xStar : Real) = x0 * xStar 0 := by simp [x, x0, dotProduct]
      have hx00 : x 0 = x0 := rfl
      have hrange :
          (((x ⬝ᵥ xStar : Real) : EReal) -
                (if 0 < x 0 then ((-Real.log (x 0) - (1 / 2 : Real) : Real) : EReal) else ⊤)) =
              ((-Real.log (-xStar 0) - (1 / 2 : Real) : Real) : EReal) := by
        rw [if_pos hx0, hdot, hx00]
        rw [(EReal.coe_sub (x0 * xStar 0) (-Real.log x0 - (1 / 2 : Real))).symm]
        have hreal :
            x0 * xStar 0 - (-Real.log x0 - (1 / 2 : Real)) =
              -Real.log (-xStar 0) - (1 / 2 : Real) := by
          calc
            x0 * xStar 0 - (-Real.log x0 - (1 / 2 : Real)) =
                x0 * xStar 0 + Real.log x0 + (1 / 2 : Real) := by
                  ring_nf
            _ = -Real.log (-xStar 0) - (1 / 2 : Real) := by
                  simp [hx0s, hlog]
                  ring_nf
        exact_mod_cast hreal
      have hle' := hle
      rw [hrange] at hle'
      exact hle'
  · -- Unbounded above when `x* ≥ 0`.
    rw [if_neg hs]
    unfold fenchelConjugate
    refine (EReal.eq_top_iff_forall_lt _).2 ?_
    intro μ
    let x0 : Real := Real.exp μ
    let x : Fin 1 → Real := fun _ => x0
    have hx0 : 0 < x0 := by simpa [x0] using Real.exp_pos μ
    have hx : 0 < x 0 := by simpa [x, x0] using hx0
    have hs0 : 0 ≤ xStar 0 := le_of_not_gt hs
    have hx0_mul : 0 ≤ x0 * xStar 0 := mul_nonneg (le_of_lt hx0) hs0
    have hμ_real : μ < x0 * xStar 0 + Real.log x0 + (1 / 2 : Real) := by
      have hpos : 0 < (1 / 2 : Real) := by norm_num
      have hlt : μ < μ + (1 / 2 : Real) := by linarith
      have hle : μ + (1 / 2 : Real) ≤ x0 * xStar 0 + μ + (1 / 2 : Real) := by
        nlinarith [hx0_mul]
      have hμ' : μ < x0 * xStar 0 + μ + (1 / 2 : Real) := lt_of_lt_of_le hlt hle
      simpa [x0, Real.log_exp, add_assoc, add_left_comm, add_comm] using hμ'
    have hμ : ((μ : Real) : EReal) <
        ((x0 * xStar 0 + Real.log x0 + (1 / 2 : Real) : Real) : EReal) := by
      exact_mod_cast hμ_real
    have hle :
        (((x ⬝ᵥ xStar : Real) : EReal) -
              (if 0 < x 0 then ((-Real.log (x 0) - (1 / 2 : Real) : Real) : EReal) else ⊤)) ≤
            sSup
              (Set.range fun x : Fin 1 → Real =>
                ((x ⬝ᵥ xStar : Real) : EReal) -
                  (if 0 < x 0 then ((-Real.log (x 0) - (1 / 2 : Real) : Real) : EReal) else ⊤)) :=
      le_sSup ⟨x, rfl⟩
    have hdot : (x ⬝ᵥ xStar : Real) = x0 * xStar 0 := by simp [x, x0, dotProduct]
    have hx00 : x 0 = x0 := rfl
    have hrange :
        (((x ⬝ᵥ xStar : Real) : EReal) -
              (if 0 < x 0 then ((-Real.log (x 0) - (1 / 2 : Real) : Real) : EReal) else ⊤)) =
            ((x0 * xStar 0 + Real.log x0 + (1 / 2 : Real) : Real) : EReal) := by
      rw [if_pos hx, hdot, hx00]
      rw [(EReal.coe_sub (x0 * xStar 0) (-Real.log x0 - (1 / 2 : Real))).symm]
      ring_nf
    have hlt :
        ((μ : Real) : EReal) <
          (((x ⬝ᵥ xStar : Real) : EReal) -
            (if 0 < x 0 then ((-Real.log (x 0) - (1 / 2 : Real) : Real) : EReal) else ⊤)) :=
      lt_of_lt_of_eq hμ hrange.symm
    exact lt_of_lt_of_le hlt hle

/-- The quadratic function `w(x) = (1/2) * ⟪x, x⟫` on `ℝ^n`, written on coordinates
`x : Fin n → ℝ` and valued in `EReal`. -/
noncomputable def quadraticHalfInner (n : Nat) : (Fin n → Real) → EReal :=
  fun x => (((1 / 2 : Real) * (x ⬝ᵥ x) : Real) : EReal)

end Section12
end Chap03
