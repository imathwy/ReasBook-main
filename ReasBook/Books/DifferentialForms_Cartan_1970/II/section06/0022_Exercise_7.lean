import Mathlib
import cartan.II.section05.«0028_Proposition_8_1»
import cartan.II.section06.«0008_Theorem_2»

open scoped BigOperators unitInterval

noncomputable section

-- Declarations for this item will be appended below by the statement pipeline.

namespace Path

private def polynomialClosedDiscMap (P : Polynomial ℂ) (R : NNReal) :
    C(Metric.closedBall (0 : ℂ) (R : ℝ), ℂ) :=
  ⟨fun z ↦ P.eval z, P.continuous.comp continuous_subtype_val⟩

/- The image of the positively oriented radius-`R` circle under `P`, viewed as a closed path.
This is the source-facing owner for Exercise 7(1), built from the chapter's canonical boundary-loop
constructor `closedDiscBoundaryPath`. -/
abbrev polynomialCirclePath (P : Polynomial ℂ) (R : NNReal) :
    Path (P.eval (R : ℂ)) (P.eval (R : ℂ)) :=
  (closedDiscBoundaryPath R (polynomialClosedDiscMap P R)).cast
    (by simp [polynomialClosedDiscMap, closedDiscBoundaryBasepoint])
    (by simp [polynomialClosedDiscMap, closedDiscBoundaryBasepoint])

@[simp] theorem polynomialCirclePath_apply (P : Polynomial ℂ) (R : NNReal) (t : I) :
    polynomialCirclePath P R t = P.eval (circleMap 0 (R : ℝ) (2 * Real.pi * (t : ℝ))) := by
  simpa [polynomialCirclePath, polynomialClosedDiscMap] using
    (closedDiscBoundaryPath_apply R (polynomialClosedDiscMap P R) t)

/-- Helper for Exercise 7: the dominant monomial loop `t ↦ c * t^n` on a large circle has winding
index `n` about the origin. -/
lemma hasIndexAt_zero_polynomialCirclePath_C_mul_X_pow {c : ℂ} (hc : c ≠ 0) (n : ℕ)
    {R : NNReal} (hR : 0 < R) :
    (polynomialCirclePath (Polynomial.C c * Polynomial.X ^ n) R).HasIndexAt 0 (n : ℤ) := by
  let w : C(I, ℂ) :=
    ⟨fun t ↦ Complex.log c + ((n : ℂ) * (((Real.log (R : ℝ)) : ℂ) + (2 * Real.pi * (t : ℝ)) * Complex.I)),
      by
        fun_prop⟩
  refine ⟨w, ?_, ?_⟩
  · intro t
    -- Split off the constant logarithm of `c`, then rewrite the remaining exponential as the
    -- standard radius-`R` circle raised to the `n`th power.
    have hbase :
        Complex.exp (((Real.log (R : ℝ)) : ℂ) + (2 * Real.pi * (t : ℝ)) * Complex.I) =
          circleMap 0 (R : ℝ) (2 * Real.pi * (t : ℝ)) := by
      calc
        Complex.exp (((Real.log (R : ℝ)) : ℂ) + (2 * Real.pi * (t : ℝ)) * Complex.I)
            = Complex.exp (((Real.log (R : ℝ)) : ℂ)) *
                Complex.exp ((2 * Real.pi * (t : ℝ)) * Complex.I) := by
                  rw [Complex.exp_add]
        _ = (R : ℂ) * Complex.exp ((2 * Real.pi * (t : ℝ)) * Complex.I) := by
              rw [← Complex.ofReal_exp]
              simpa using congrArg (fun x : ℝ ↦ (x : ℂ)) (Real.exp_log hR)
        _ = circleMap 0 (R : ℝ) (2 * Real.pi * (t : ℝ)) := by
              simp [circleMap_zero]
    -- Evaluate the monomial polynomial on the boundary parametrization.
    rw [polynomialCirclePath_apply, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X_pow]
    calc
      Complex.exp (w t)
          = Complex.exp (Complex.log c) *
              Complex.exp (((n : ℂ) * (((Real.log (R : ℝ)) : ℂ) +
                (2 * Real.pi * (t : ℝ)) * Complex.I))) := by
                simp [w, Complex.exp_add]
      _ = c * Complex.exp ((((Real.log (R : ℝ)) : ℂ) +
              (2 * Real.pi * (t : ℝ)) * Complex.I) * n) := by
            rw [Complex.exp_log hc]
            congr 1
            ring
      _ = c * Complex.exp ((((Real.log (R : ℝ)) : ℂ) +
              (2 * Real.pi * (t : ℝ)) * Complex.I)) ^ n := by
            congr 1
            simpa [mul_comm] using
              (Complex.exp_nat_mul
                ((((Real.log (R : ℝ)) : ℂ) + (2 * Real.pi * (t : ℝ)) * Complex.I)) n)
      _ = c * (circleMap 0 (R : ℝ) (2 * Real.pi * (t : ℝ))) ^ n := by
            rw [hbase]
      _ = c * (circleMap 0 (R : ℝ) (2 * Real.pi * (t : ℝ))) ^ n - 0 := by ring
  · -- The logarithm lift gains exactly `2πni` after one turn around the boundary circle.
    calc
      w 1
          = Complex.log c +
              (n : ℂ) * (((Real.log (R : ℝ)) : ℂ) + (2 * Real.pi : ℂ) * Complex.I) := by
                simp [w]
      _ = Complex.log c + (n : ℂ) * (((Real.log (R : ℝ)) : ℂ) + 0 * Complex.I) +
            ((2 * Real.pi : ℂ) * (n : ℂ)) * Complex.I := by ring
      _ = w 0 + ((2 * Real.pi : ℂ) * (n : ℂ)) * Complex.I := by
            simp [w]

/-- Helper for Exercise 7: scaling a dominated perturbation by a unit-interval parameter still
prevents cancellation with the original loop. -/
lemma add_smul_ne_zero_of_norm_lt {z z₁ : ℂ} {γ : Path z z} {γ₁ : Path z₁ z₁}
    (hγ₁ : ∀ t : I, ‖γ₁ t‖ < ‖γ t‖) (s t : I) :
    γ t + (s : ℂ) * γ₁ t ≠ 0 := by
  have hs : ‖(s : ℂ)‖ ≤ 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg s.2.1] using s.2.2
  have hscaled : ‖(s : ℂ) * γ₁ t‖ < ‖γ t‖ := by
    have hmul : ‖(s : ℂ)‖ * ‖γ₁ t‖ ≤ ‖γ₁ t‖ := by
      nlinarith [norm_nonneg (γ₁ t), hs]
    calc
      ‖(s : ℂ) * γ₁ t‖ = ‖(s : ℂ)‖ * ‖γ₁ t‖ := norm_mul _ _
      _ ≤ ‖γ₁ t‖ := hmul
      _ < ‖γ t‖ := hγ₁ t
  intro h_add
  -- Vanishing would force equal norms, contradicting the scaled domination estimate.
  have hnorm : ‖γ t‖ = ‖(s : ℂ) * γ₁ t‖ := by
    calc
      ‖γ t‖ = ‖-((s : ℂ) * γ₁ t)‖ := by
        congr
        simpa using eq_neg_of_add_eq_zero_left h_add
      _ = ‖(s : ℂ) * γ₁ t‖ := norm_neg _
  have : ‖(s : ℂ) * γ₁ t‖ < ‖(s : ℂ) * γ₁ t‖ := by
    simpa [hnorm] using hscaled
  exact lt_irrefl _ this

/-- Helper for Exercise 7: a strict lower-order perturbation of a loop preserves its winding-index
logarithm lift about the origin. -/
lemma hasIndexAt_zero_add_of_abs_lt {z z₁ : ℂ} {γ : Path z z} {γ₁ : Path z₁ z₁} {n : ℤ}
    (hγ : γ.HasIndexAt 0 n) (hγ₁ : ∀ t : I, ‖γ₁ t‖ < ‖γ t‖) :
    (γ.add γ₁).HasIndexAt 0 n := by
  rcases hγ with ⟨w, hwexp, hwjump⟩
  let Δ : ℂ := ((2 * Real.pi : ℂ) * (n : ℂ)) * Complex.I
  have hΔexp : Complex.exp Δ = 1 := by
    -- Normalize the period to the standard `n * (2πi)` form.
    rw [show Δ = (n : ℂ) * (2 * Real.pi * Complex.I) by
      dsimp [Δ]
      ring]
    exact Complex.exp_int_mul_two_pi_mul_I n
  have hnegΔexp : Complex.exp (-Δ) = 1 := by
    rw [Complex.exp_neg, hΔexp, inv_one]
  let G : C(I × I, {u : ℂ // u ≠ 0}) :=
    ⟨fun p ↦ ⟨γ p.2 + (p.1 : ℂ) * γ₁ p.2, add_smul_ne_zero_of_norm_lt hγ₁ p.1 p.2⟩, by
      apply Continuous.subtype_mk
      fun_prop⟩
  have hG_zero : ∀ t : I, G (0, t) = ⟨Complex.exp (w t), Complex.exp_ne_zero _⟩ := by
    intro t
    apply Subtype.ext
    -- The lifted homotopy is anchored on the original logarithm lift at `s = 0`.
    simpa [G] using (hwexp t).symm
  let W : C(I × I, ℂ) := Complex.isCoveringMap_exp.liftHomotopy G w hG_zero
  have hW_lifts :
      (fun u : ℂ ↦ (⟨Complex.exp u, Complex.exp_ne_zero u⟩ : {u : ℂ // u ≠ 0})) ∘ W = G :=
    Complex.isCoveringMap_exp.liftHomotopy_lifts G w hG_zero
  have hW_zero : ∀ t : I, W (0, t) = w t :=
    Complex.isCoveringMap_exp.liftHomotopy_zero G w hG_zero
  let leftLift : C(I, ℂ) :=
    ⟨fun s ↦ W (s, 0), by
      fun_prop⟩
  let rightLift : C(I, ℂ) :=
    ⟨fun s ↦ W (s, 1) + (-Δ), by
      fun_prop⟩
  have hvertical_eq_fun : ⇑leftLift = ⇑rightLift := by
    -- The left edge and the period-corrected right edge lift the same boundary trace.
    refine Complex.isCoveringMap_exp.eq_of_comp_eq leftLift.continuous rightLift.continuous ?_ 0 ?_
    · ext s
      change Complex.exp (leftLift s) = Complex.exp (rightLift s)
      have hs_left : Complex.exp (leftLift s) = γ 0 + (s : ℂ) * γ₁ 0 := by
        simpa [leftLift, G] using congrArg Subtype.val (congr_fun hW_lifts (s, 0))
      have hs_right : Complex.exp (W (s, 1)) = γ 1 + (s : ℂ) * γ₁ 1 := by
        simpa [G] using congrArg Subtype.val (congr_fun hW_lifts (s, 1))
      calc
        Complex.exp (leftLift s) = γ 0 + (s : ℂ) * γ₁ 0 := hs_left
        _ = γ 1 + (s : ℂ) * γ₁ 1 := by simp
        _ = Complex.exp (W (s, 1)) := hs_right.symm
        _ = Complex.exp (rightLift s) := by
              simp [rightLift, Complex.exp_add, hnegΔexp]
    · calc
        leftLift 0 = W (0, 0) := rfl
        _ = w 0 := hW_zero 0
        _ = w 1 + (-Δ) := by
              rw [hwjump]
              ring
        _ = W (0, 1) + (-Δ) := by rw [hW_zero 1]
        _ = rightLift 0 := rfl
  have hvertical_eq : leftLift = rightLift := by
    ext s
    exact congr_fun hvertical_eq_fun s
  let topLift : C(I, ℂ) :=
    ⟨fun t ↦ W (1, t), by
      fun_prop⟩
  have htop_exp : ∀ t : I, Complex.exp (topLift t) = γ.add γ₁ t := by
    intro t
    -- Restrict the lifted homotopy to the top edge to recover the perturbed loop.
    simpa [topLift, G] using congrArg Subtype.val (congr_fun hW_lifts (1, t))
  have htop_jump : topLift 1 = topLift 0 + Δ := by
    -- The vertical-edge uniqueness transports the original endpoint jump to the top edge.
    have htop_eq : W (1, 0) = W (1, 1) + (-Δ) := by
      simpa [leftLift, rightLift] using congrArg (fun F : C(I, ℂ) ↦ F 1) hvertical_eq
    calc
      topLift 1 = W (1, 1) := rfl
      _ = (W (1, 1) + (-Δ)) + Δ := by ring
      _ = W (1, 0) + Δ := by rw [htop_eq]
      _ = topLift 0 + Δ := rfl
  -- Package the top edge of the lifted homotopy as the required logarithm lift.
  refine ⟨topLift, ?_, ?_⟩
  · intro t
    simpa using htop_exp t
  · simpa [Δ] using htop_jump

/-- Helper for Exercise 7: the lower-degree polynomial `eraseLead P` satisfies the standard
coefficient-sum estimate on circles of radius `R ≥ 1`. -/
lemma eraseLead_eval_norm_le_coeff_sum_mul_radius_pow_pred
    (P : Polynomial ℂ) (hn : 0 < P.natDegree)
    {R : ℝ} (hR1 : 1 ≤ R) {z : ℂ} (hz : ‖z‖ = R) :
    ‖P.eraseLead.eval z‖ ≤
      Finset.sum (Finset.range P.natDegree) (fun i ↦ ‖(P.eraseLead).coeff i‖) *
        R ^ (P.natDegree - 1) := by
  have hdeg : P.eraseLead.natDegree < P.natDegree := by
    have hpred : P.natDegree - 1 < P.natDegree := by
      simpa [Nat.pred_eq_sub_one] using Nat.pred_lt (Nat.ne_of_gt hn)
    exact lt_of_le_of_lt (Polynomial.eraseLead_natDegree_le P) hpred
  rw [Polynomial.eval_eq_sum_range' hdeg z]
  calc
    ‖Finset.sum (Finset.range P.natDegree) (fun i ↦ (P.eraseLead).coeff i * z ^ i)‖ ≤
        Finset.sum (Finset.range P.natDegree) (fun i ↦ ‖(P.eraseLead).coeff i * z ^ i‖) := by
          exact norm_sum_le _ _
    _ = Finset.sum (Finset.range P.natDegree) (fun i ↦ ‖(P.eraseLead).coeff i‖ * ‖z‖ ^ i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [norm_mul, norm_pow]
    _ ≤ Finset.sum (Finset.range P.natDegree)
          (fun i ↦ ‖(P.eraseLead).coeff i‖ * R ^ (P.natDegree - 1)) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          have hi_le : i ≤ P.natDegree - 1 := Nat.le_pred_of_lt (Finset.mem_range.mp hi)
          have hpow : ‖z‖ ^ i ≤ R ^ (P.natDegree - 1) := by
            rw [hz]
            exact pow_le_pow_right₀ hR1 hi_le
          exact mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
    _ =
        Finset.sum (Finset.range P.natDegree) (fun i ↦ ‖(P.eraseLead).coeff i‖) *
          R ^ (P.natDegree - 1) := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            (Finset.sum_mul (Finset.range P.natDegree) (fun i ↦ ‖(P.eraseLead).coeff i‖)
              (R ^ (P.natDegree - 1))).symm

/-- Helper for Exercise 7: evaluating the leading-monomial part plus `eraseLead P` at the base
point `R` recovers `P.eval R`. -/
lemma polynomialCirclePath_leading_add_eraseLead_basepoint
    (P : Polynomial ℂ) (R : NNReal) :
    P.eval (R : ℂ) =
      (Polynomial.C P.leadingCoeff * Polynomial.X ^ P.natDegree).eval (R : ℂ) +
        P.eraseLead.eval (R : ℂ) := by
  -- Evaluate the identity `eraseLead P + leading term = P` at the basepoint `R`.
  have hbase :
      P.eraseLead.eval (R : ℂ) +
        (Polynomial.C P.leadingCoeff * Polynomial.X ^ P.natDegree).eval (R : ℂ) =
          P.eval (R : ℂ) := by
    have h :=
      congrArg (fun Q : Polynomial ℂ ↦ Q.eval (R : ℂ)) (Polynomial.eraseLead_add_C_mul_X_pow P)
    change (P.eraseLead + (Polynomial.C P.leadingCoeff * Polynomial.X ^ P.natDegree)).eval (R : ℂ) =
      P.eval (R : ℂ) at h
    rw [Polynomial.eval_add] at h
    exact h
  exact hbase.symm.trans (by simp [add_comm])

/-- Helper for Exercise 7: on sufficiently large circles, the lower-degree part `eraseLead`
is dominated by the leading monomial term. -/
lemma exists_radius_eraseLead_eval_lt_leading_term_on_circle
    (P : Polynomial ℂ) (hn : 0 < P.natDegree) :
    ∃ R₀ : NNReal, 0 < R₀ ∧
      ∀ R ≥ R₀, ∀ t : I,
        ‖P.eraseLead.eval (circleMap 0 (R : ℝ) (2 * Real.pi * (t : ℝ)))‖ <
          ‖P.leadingCoeff * (circleMap 0 (R : ℝ) (2 * Real.pi * (t : ℝ))) ^ P.natDegree‖ := by
  let coeffSum : ℝ := Finset.sum (Finset.range P.natDegree) (fun i ↦ ‖(P.eraseLead).coeff i‖)
  let leadNorm : ℝ := ‖P.leadingCoeff‖
  have hlead_pos : 0 < leadNorm := by
    -- Positive degree forces the leading coefficient to be nonzero.
    exact norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.ne_zero_of_natDegree_gt hn))
  let R₀ : NNReal := ⟨max 1 (coeffSum / leadNorm + 1), by positivity⟩
  have hR₀pos : 0 < R₀ := by
    change (0 : ℝ) < max 1 (coeffSum / leadNorm + 1)
    positivity
  refine ⟨R₀, hR₀pos, ?_⟩
  intro R hR t
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by
    exact le_trans (le_max_left _ _) hR
  have hRpos : 0 < (R : ℝ) := by
    exact lt_of_lt_of_le (show (0 : ℝ) < 1 by norm_num) hR1
  have hcoeff_lt : coeffSum < leadNorm * (R : ℝ) := by
    have haux : coeffSum / leadNorm + 1 ≤ (R : ℝ) := by
      exact le_trans (le_max_right _ _) hR
    have hdiv_lt : coeffSum / leadNorm < (R : ℝ) := by
      linarith
    have hmul_lt : coeffSum < (R : ℝ) * leadNorm := by
      exact (div_lt_iff₀ hlead_pos).mp hdiv_lt
    simpa [mul_comm] using hmul_lt
  have hcircle_norm :
      ‖circleMap 0 (R : ℝ) (2 * Real.pi * (t : ℝ))‖ = (R : ℝ) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg R.2] using
      norm_circleMap_zero (R : ℝ) (2 * Real.pi * (t : ℝ))
  have hbound :=
    eraseLead_eval_norm_le_coeff_sum_mul_radius_pow_pred P hn hR1 hcircle_norm
  have hpow_pos : 0 < (R : ℝ) ^ (P.natDegree - 1) := by
    exact pow_pos hRpos _
  have hmain :
      coeffSum * (R : ℝ) ^ (P.natDegree - 1) <
        leadNorm * (R : ℝ) ^ P.natDegree := by
    have hmul :
        coeffSum * (R : ℝ) ^ (P.natDegree - 1) <
          (leadNorm * (R : ℝ)) * (R : ℝ) ^ (P.natDegree - 1) := by
      exact mul_lt_mul_of_pos_right hcoeff_lt hpow_pos
    have hsplit :
        (leadNorm * (R : ℝ)) * (R : ℝ) ^ (P.natDegree - 1) =
          leadNorm * (R : ℝ) ^ P.natDegree := by
      calc
        (leadNorm * (R : ℝ)) * (R : ℝ) ^ (P.natDegree - 1)
            = leadNorm * ((R : ℝ) * (R : ℝ) ^ (P.natDegree - 1)) := by ring
        _ = leadNorm * ((R : ℝ) ^ (P.natDegree - 1) * (R : ℝ)) := by
              exact congrArg (fun x : ℝ ↦ leadNorm * x) (mul_comm _ _)
        _ = leadNorm * (R : ℝ) ^ (P.natDegree - 1 + 1) := by
              exact congrArg (fun x : ℝ ↦ leadNorm * x)
                (pow_succ (R : ℝ) (P.natDegree - 1)).symm
        _ = leadNorm * (R : ℝ) ^ P.natDegree := by
              rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hn)]
    exact hmul.trans_eq hsplit
  have hlead_eval :
      ‖P.leadingCoeff * (circleMap 0 (R : ℝ) (2 * Real.pi * (t : ℝ))) ^ P.natDegree‖ =
        leadNorm * (R : ℝ) ^ P.natDegree := by
    -- On the boundary, the leading term contributes exactly `‖leadingCoeff‖ * R^n`.
    rw [norm_mul, norm_pow, hcircle_norm]
  -- Combine the coefficient estimate with the radius choice.
  calc
    ‖P.eraseLead.eval (circleMap 0 (R : ℝ) (2 * Real.pi * (t : ℝ)))‖ ≤
        coeffSum * (R : ℝ) ^ (P.natDegree - 1) := hbound
    _ < leadNorm * (R : ℝ) ^ P.natDegree := hmain
    _ = ‖P.leadingCoeff * (circleMap 0 (R : ℝ) (2 * Real.pi * (t : ℝ))) ^ P.natDegree‖ := by
          rw [hlead_eval]

/-- Helper for Exercise 7: `HasIndexAt` is preserved when a closed path is cast along an endpoint
equality. -/
lemma hasIndexAt_zero_of_cast {z z' : ℂ} {γ : Path z z} {n : ℤ}
    (hγ : γ.HasIndexAt 0 n) (hz : z' = z) :
    (γ.cast hz hz).HasIndexAt 0 n := by
  -- Casting changes only the endpoint labels, not the underlying loop.
  subst z'
  simpa using hγ

/-- Helper for Exercise 7: after casting endpoints, the sum of the leading-monomial loop and the
`eraseLead` loop is exactly the polynomial boundary loop. -/
lemma polynomialCirclePath_leading_add_eraseLead_cast
    (P : Polynomial ℂ) (R : NNReal) :
    (((polynomialCirclePath (Polynomial.C P.leadingCoeff * Polynomial.X ^ P.natDegree) R).add
        (polynomialCirclePath P.eraseLead R)).cast
      (polynomialCirclePath_leading_add_eraseLead_basepoint P R)
      (polynomialCirclePath_leading_add_eraseLead_basepoint P R)) =
      polynomialCirclePath P R := by
  -- Compare the two loops pointwise after expanding `P = leading + eraseLead`.
  ext t
  rw [Path.cast_coe, Path.add_apply, polynomialCirclePath_apply, polynomialCirclePath_apply,
    polynomialCirclePath_apply]
  let z : ℂ := circleMap 0 (R : ℝ) (2 * Real.pi * (t : ℝ))
  have hpoly :
      P.eraseLead.eval z +
        (Polynomial.C P.leadingCoeff * Polynomial.X ^ P.natDegree).eval z = P.eval z := by
    have h :=
      congrArg (fun Q : Polynomial ℂ ↦ Q.eval z) (Polynomial.eraseLead_add_C_mul_X_pow P)
    change (P.eraseLead + (Polynomial.C P.leadingCoeff * Polynomial.X ^ P.natDegree)).eval z =
      P.eval z at h
    rw [Polynomial.eval_add] at h
    exact h
  simpa [z, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X_pow, add_comm] using hpoly

/-- Helper for Exercise 7: once the leading monomial dominates `eraseLead` on the boundary,
the polynomial boundary loop has the same winding index as its leading monomial loop. -/
lemma polynomialCirclePath_hasIndexAt_zero_of_domination
    (P : Polynomial ℂ) (hn : 0 < P.natDegree) {R : NNReal} (hR : 0 < R)
    (hdom : ∀ t : I,
      ‖P.eraseLead.eval (circleMap 0 (R : ℝ) (2 * Real.pi * (t : ℝ)))‖ <
        ‖P.leadingCoeff * (circleMap 0 (R : ℝ) (2 * Real.pi * (t : ℝ))) ^ P.natDegree‖) :
    (polynomialCirclePath P R).HasIndexAt 0 (P.natDegree : ℤ) := by
  let γ : Path
      ((Polynomial.C P.leadingCoeff * Polynomial.X ^ P.natDegree).eval (R : ℂ))
      ((Polynomial.C P.leadingCoeff * Polynomial.X ^ P.natDegree).eval (R : ℂ)) :=
    polynomialCirclePath (Polynomial.C P.leadingCoeff * Polynomial.X ^ P.natDegree) R
  let η : Path (P.eraseLead.eval (R : ℂ)) (P.eraseLead.eval (R : ℂ)) :=
    polynomialCirclePath P.eraseLead R
  have hγ :
      γ.HasIndexAt 0 (P.natDegree : ℤ) := by
    -- The leading monomial loop already carries index `natDegree P`.
    simpa [γ] using
      hasIndexAt_zero_polynomialCirclePath_C_mul_X_pow
        (Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.ne_zero_of_natDegree_gt hn)) P.natDegree hR
  have hη_dom : ∀ t : I, ‖η t‖ < ‖γ t‖ := by
    intro t
    -- Rewrite the two constituent loops to the boundary parametrization from the hypothesis.
    simpa [γ, η, polynomialCirclePath_apply, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X_pow] using hdom t
  have hsum :
      (γ.add η).HasIndexAt 0 (P.natDegree : ℤ) := by
    -- Proposition 8.3's additive homotopy step transfers the index through strict domination.
    exact hasIndexAt_zero_add_of_abs_lt hγ hη_dom
  have hcast :
      ((((polynomialCirclePath (Polynomial.C P.leadingCoeff * Polynomial.X ^ P.natDegree) R).add
          (polynomialCirclePath P.eraseLead R)).cast
        (polynomialCirclePath_leading_add_eraseLead_basepoint P R)
        (polynomialCirclePath_leading_add_eraseLead_basepoint P R))).HasIndexAt 0
        (P.natDegree : ℤ) := by
    -- Move the index witness across the endpoint cast before identifying the loop.
    simpa [γ, η] using
      hasIndexAt_zero_of_cast hsum (polynomialCirclePath_leading_add_eraseLead_basepoint P R)
  -- Route correction: finish through the dedicated cast-rewrite lemma instead of redoing the
  -- endpoint simplification inside the main proof.
  simpa [polynomialCirclePath_leading_add_eraseLead_cast P R] using hcast

-- Proof sketch: for large `R`, the dominant term `z ↦ P.leadingCoeff * z^n` strictly dominates
-- the lower-degree part of `P` on `|z| = R`; Proposition 8.3 then shows that the polynomial image
-- loop has the same winding index about `0` as this leading monomial loop, whose index is `n`
-- because `P.leadingCoeff ≠ 0` when `0 < P.natDegree`.
/-- Exercise 7 (1): for a complex polynomial `P(t) = a_n t^n + a_{n-1} t^(n-1) + ⋯ + a₀` of
positive degree, the image of the radius-`R` circle under `P` avoids the origin and has winding
index `P.natDegree` about `0` for all sufficiently large `R`. -/
theorem exists_radius_polynomialCirclePath_hasIndexAt_zero
    (P : Polynomial ℂ) (hn : 0 < P.natDegree) :
    ∃ R₀ : NNReal, 0 < R₀ ∧
      ∀ R ≥ R₀,
        (polynomialCirclePath P R).HasIndexAt 0 (P.natDegree : ℤ) := by
  rcases exists_radius_eraseLead_eval_lt_leading_term_on_circle P hn with
    ⟨R₀, hR₀pos, hR₀dom⟩
  refine ⟨R₀, hR₀pos, ?_⟩
  intro R hR
  -- Use the large-radius domination estimate to reduce to the leading monomial loop.
  exact polynomialCirclePath_hasIndexAt_zero_of_domination P hn
    (lt_of_lt_of_le hR₀pos hR) (hR₀dom R hR)

end Path

/- Exercise 7 (2): every nonconstant complex polynomial has a complex root. This is exactly the
canonical mathlib theorem `Complex.exists_root`; the `natDegree` hypothesis used in the text is
kept only as a thin companion corollary. -/
recall Complex.exists_root

/-- The textbook `natDegree` version of Exercise 7 (2), deduced directly from
`Complex.exists_root`. -/
theorem exists_complex_root_of_natDegree_pos (P : Polynomial ℂ) (hdeg : 0 < P.natDegree) :
    ∃ z : ℂ, P.IsRoot z :=
  Complex.exists_root (Polynomial.natDegree_pos_iff_degree_pos.mp hdeg)
