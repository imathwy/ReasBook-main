import Mathlib
import cartan.III.section11.«0001_Proposition_2_1».LaurentTailAPI

-- Semantic recall note: `lean_leansearch` was unavailable in this environment; the statement shape
-- was verified against local mathlib interval-integral and circle-integral notation, together with
-- nearby Laurent-series precedent in this repository.

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Interval Real Topology
open Metric
open MeasureTheory

noncomputable section

/-- Helper for Exercise 12: the unit circle avoids the origin. -/
lemma exercise12_ne_zero_of_mem_unit_sphere {z : ℂ} (hz : z ∈ sphere (0 : ℂ) 1) : z ≠ 0 := by
  -- A point on `|z| = 1` has nonzero norm, hence it cannot be the origin.
  have hz_norm : ‖z‖ = (1 : ℝ) := by
    simpa using mem_sphere_iff_norm.mp hz
  exact fun hz0 ↦ by simp [hz0] at hz_norm

/-- Helper for Exercise 12: the circle integral of `z ^ k` detects only the residue term
`k = -1`. -/
lemma exercise12_circleIntegral_zpow_eq_residue (k : ℤ) :
    (∮ z in C(0, 1), z ^ k) = if k = -1 then 2 * Real.pi * Complex.I else 0 := by
  by_cases hk : k = -1
  · -- The residue case is the basic Cauchy kernel integral at the origin.
    rw [if_pos hk]
    subst hk
    have hzero_mem : (0 : ℂ) ∈ ball (0 : ℂ) (1 : ℝ) := by
      simp [Metric.mem_ball]
    simpa using
      (circleIntegral.integral_sub_inv_of_mem_ball (c := (0 : ℂ)) (w := (0 : ℂ))
        (R := (1 : ℝ)) hzero_mem)
  · -- Every other Laurent monomial has vanishing unit-circle integral.
    rw [if_neg hk]
    simpa using
      (circleIntegral.integral_sub_zpow_of_ne hk (c := (0 : ℂ)) (w := (0 : ℂ)) (R := (1 : ℝ)))

/-- Helper for Exercise 12: a Laurent monomial times a constant is circle-integrable on
the unit circle. -/
lemma exercise12_circleIntegrable_const_mul_zpow (a : ℂ) (k : ℤ) :
    CircleIntegrable (fun z : ℂ ↦ a * z ^ k) 0 1 := by
  -- The only issue for `zpow` continuity is the origin, and the unit circle avoids it.
  refine (continuousOn_const.mul ((continuousOn_zpow₀ (m := k)).mono ?_)).circleIntegrable ?_
  · intro z hz
    exact exercise12_ne_zero_of_mem_unit_sphere hz
  · norm_num

/-- Helper for Exercise 12: after dividing a binomial summand by `z^(m+n+1)`, the resulting term
is the expected Laurent monomial on the punctured plane. -/
lemma exercise12_binomial_term_div_eq_laurent
    (ε z : ℂ) (hz : z ≠ 0) (m n k : ℕ) :
    ((z ^ 2) ^ k * ε ^ (m - k) * (Nat.choose m k : ℂ)) / z ^ (m + n + 1) =
      ((Nat.choose m k : ℂ) * ε ^ (m - k)) *
        z ^ (((2 * k : ℕ) : ℤ) - ((m + n + 1 : ℕ) : ℤ)) := by
  -- Reorder the scalar factors, then convert the quotient of powers into one Laurent power.
  calc
    ((z ^ 2) ^ k * ε ^ (m - k) * (Nat.choose m k : ℂ)) / z ^ (m + n + 1)
      = (((Nat.choose m k : ℂ) * ε ^ (m - k)) * (z ^ 2) ^ k) / z ^ (m + n + 1) := by ring
    _ = ((Nat.choose m k : ℂ) * ε ^ (m - k)) * (((z ^ 2) ^ k) / z ^ (m + n + 1)) := by
          rw [div_eq_mul_inv]
          ring
    _ = ((Nat.choose m k : ℂ) * ε ^ (m - k)) *
          (z ^ (((2 * k : ℕ) : ℤ) - ((m + n + 1 : ℕ) : ℤ))) := by
          congr 1
          calc
            ((z ^ 2) ^ k) / z ^ (m + n + 1)
              = z ^ (2 * k : ℕ) / z ^ (m + n + 1) := by rw [pow_mul]
            _ = z ^ (((2 * k : ℕ) : ℤ) - ((m + n + 1 : ℕ) : ℤ)) := by
                  have hzpow_nat : z ^ (2 * k : ℕ) = z ^ (((2 * k : ℕ) : ℤ)) := by
                    rw [← zpow_natCast]
                  have hzpow_inv :
                      (z ^ (m + n + 1 : ℕ))⁻¹ = z ^ (-((m + n + 1 : ℕ) : ℤ)) := by
                    rw [← zpow_natCast, zpow_neg]
                  rw [div_eq_mul_inv]
                  rw [hzpow_nat, hzpow_inv]
                  simpa [sub_eq_add_neg] using
                    (zpow_add₀ hz (((2 * k : ℕ) : ℤ)) (-((m + n + 1 : ℕ) : ℤ))).symm

/-- Helper for Exercise 12: on the punctured plane, the quotient
`((z^2 + ε)^m) / z^(m+n+1)` expands as a finite Laurent sum. -/
lemma exercise12_binomial_div_eq_laurent_sum
    (ε z : ℂ) (hz : z ≠ 0) (m n : ℕ) :
    ((z ^ 2 + ε) ^ m) / z ^ (m + n + 1) =
      (∑ k ∈ Finset.range (m + 1),
        ((Nat.choose m k : ℂ) * ε ^ (m - k)) *
          z ^ (((2 * k : ℕ) : ℤ) - ((m + n + 1 : ℕ) : ℤ))) := by
  -- Expand the binomial, distribute the fixed denominator, and convert each quotient to one `zpow`.
  calc
    ((z ^ 2 + ε) ^ m) / z ^ (m + n + 1)
      = (∑ k ∈ Finset.range (m + 1),
          ((z ^ 2) ^ k * ε ^ (m - k) * (Nat.choose m k : ℂ))) / z ^ (m + n + 1) := by
            rw [add_pow]
    _ = ∑ k ∈ Finset.range (m + 1),
          (((z ^ 2) ^ k * ε ^ (m - k) * (Nat.choose m k : ℂ)) / z ^ (m + n + 1)) := by
            rw [Finset.sum_div]
    _ = ∑ k ∈ Finset.range (m + 1),
          ((Nat.choose m k : ℂ) * ε ^ (m - k)) *
            z ^ (((2 * k : ℕ) : ℤ) - ((m + n + 1 : ℕ) : ℤ)) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            exact exercise12_binomial_term_div_eq_laurent ε z hz m n k

/-- Helper for Exercise 12: after the standard `1 / (2πi)` normalization, a constant multiple of a
single Laurent monomial contributes exactly its residue coefficient. -/
lemma exercise12_normalized_circleIntegral_const_mul_zpow
    (a : ℂ) (k : ℤ) :
    ((2 * Real.pi * Complex.I : ℂ)⁻¹) * ∮ z in C(0, 1), a * z ^ k =
      if k = -1 then a else 0 := by
  -- The residue lemma leaves only the `z⁻¹` term, and the normalization cancels `2πi`.
  rw [circleIntegral.integral_const_mul, exercise12_circleIntegral_zpow_eq_residue]
  by_cases hk : k = -1
  · rw [if_pos hk]
    have htwo_pi_I : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      norm_num [Real.pi_ne_zero]
    calc
      (2 * Real.pi * Complex.I : ℂ)⁻¹ * (a * (2 * Real.pi * Complex.I))
        = a * ((2 * Real.pi * Complex.I : ℂ)⁻¹ * (2 * Real.pi * Complex.I)) := by ac_rfl
      _ = a * 1 := by rw [inv_mul_cancel₀ htwo_pi_I]
      _ = a := by simp
    simp [hk]
  · rw [if_neg hk]
    simp [hk]

/-- The modified Bessel function `I_n(x)` given by its standard cosine-integral formula.
This has the notation `I_[n]`. -/
noncomputable def modifiedBesselI (n : ℕ) (x : ℂ) : ℂ :=
  (Real.pi : ℂ)⁻¹ *
    ∫ t in (0 : ℝ)..Real.pi, Complex.exp (x * Real.cos t) * Real.cos ((n : ℝ) * t)

@[inherit_doc modifiedBesselI] scoped[Bessel] notation "I_[" n "]" => modifiedBesselI n

/-- The Bessel function of the first kind `J_n(x)` given by its standard cosine-integral formula.
This has the notation `J_[n]`. -/
noncomputable def besselJ (n : ℕ) (x : ℂ) : ℂ :=
  (Real.pi : ℂ)⁻¹ *
    ∫ t in (0 : ℝ)..Real.pi, Complex.cos ((n : ℂ) * t - x * Real.sin t)

@[inherit_doc besselJ] scoped[Bessel] notation "J_[" n "]" => besselJ n

open scoped Bessel

/-- Helper for Exercise 12: reflecting an interval integral across `π` rewrites the integral over
`[0, 2π]` as the paired integral over `[0, π]`. -/
lemma intervalIntegral_pair_reflect_two_pi
    (f : ℝ → ℂ)
    (hf : IntervalIntegrable f volume (0 : ℝ) (2 * Real.pi)) :
    ∫ t in (0 : ℝ)..2 * Real.pi, f t =
      ∫ t in (0 : ℝ)..Real.pi, (f t + f (2 * Real.pi - t)) := by
  have hpi_le : Real.pi ≤ 2 * Real.pi := by
    nlinarith [Real.pi_pos]
  have hπ_mem : Real.pi ∈ Set.uIcc (0 : ℝ) (2 * Real.pi) := by
    simp [Real.pi_pos.le, hpi_le]
  have hsplit := (IntervalIntegrable.trans_iff (f := f) (μ := volume) (a := (0 : ℝ))
    (b := Real.pi) (c := 2 * Real.pi) hπ_mem).mp hf
  have hf_left : IntervalIntegrable f volume (0 : ℝ) Real.pi := hsplit.1
  have hf_right : IntervalIntegrable f volume Real.pi (2 * Real.pi) := hsplit.2
  have hf_reflect :
      IntervalIntegrable (fun t : ℝ ↦ f (2 * Real.pi - t)) volume (0 : ℝ) Real.pi := by
    simpa [sub_eq_add_neg, two_mul] using
      hf_right.symm.comp_sub_left (2 * Real.pi) (h := by finiteness)
  -- Split `[0, 2π]` at `π`, then rewrite the upper half by the substitution `t ↦ 2π - t`.
  calc
    ∫ t in (0 : ℝ)..2 * Real.pi, f t
      = (∫ t in (0 : ℝ)..Real.pi, f t) + ∫ t in Real.pi..2 * Real.pi, f t := by
          symm
          exact intervalIntegral.integral_add_adjacent_intervals hf_left hf_right
    _ = (∫ t in (0 : ℝ)..Real.pi, f t) + ∫ t in (0 : ℝ)..Real.pi, f (2 * Real.pi - t) := by
          simpa [sub_eq_add_neg, two_mul] using congrArg
            (fun u : ℂ ↦ (∫ t in (0 : ℝ)..Real.pi, f t) + u)
            (intervalIntegral.integral_comp_sub_left (f := f) (a := (0 : ℝ))
              (b := Real.pi) (d := 2 * Real.pi)).symm
    _ = ∫ t in (0 : ℝ)..Real.pi, (f t + f (2 * Real.pi - t)) := by
          simpa using (intervalIntegral.integral_add hf_left hf_reflect).symm

/-- Helper for Exercise 12: opposite purely imaginary exponentials add up to twice the complex
cosine. -/
lemma exercise12_exp_mul_I_add_exp_neg_mul_I (u : ℂ) :
    Complex.exp (u * Complex.I) + Complex.exp (-u * Complex.I) = 2 * Complex.cos u := by
  -- This is the standard `e^{iu} + e^{-iu} = 2 cos u` identity in mathlib form.
  rw [← Complex.cos_add_sin_I, ← Complex.cos_sub_sin_I]
  ring

/-- Helper for Exercise 12: the reciprocal of `cos t + i sin t` is `cos t - i sin t`. -/
lemma exercise12_cos_add_sin_mul_I_inv (t : ℝ) :
    (Complex.cos (t : ℂ) + Complex.sin (t : ℂ) * Complex.I)⁻¹ =
      Complex.cos (t : ℂ) - Complex.sin (t : ℂ) * Complex.I := by
  -- Multiply by the conjugate expression and use `cos² + sin² = 1`.
  apply inv_eq_of_mul_eq_one_right
  calc
    (Complex.cos (t : ℂ) + Complex.sin (t : ℂ) * Complex.I) *
        (Complex.cos (t : ℂ) - Complex.sin (t : ℂ) * Complex.I)
      = Complex.cos (t : ℂ) ^ 2 + Complex.sin (t : ℂ) ^ 2 := by
          ring_nf
          simp [Complex.I_sq]
    _ = 1 := by exact Complex.cos_sq_add_sin_sq (t : ℂ)

/-- Helper for Exercise 12: on the unit circle, the derivative factor divided by `z^(n+1)`
reduces to the pure Fourier phase `I * e^{-int}`. -/
lemma unit_circle_deriv_div_pow_eq_fourier_phase
    (n : ℕ) (t : ℝ) :
    deriv (circleMap 0 1) t / (circleMap 0 1 t) ^ (n + 1) =
      Complex.I * Complex.exp (-(((n : ℂ) * t) * Complex.I)) := by
  -- Route correction: separate the derivative-versus-power cancellation from the later
  -- trigonometric normalization so both Bessel bridges reuse the same Fourier phase.
  have hphase :
      (((t - (((n : ℝ) + 1) * t) : ℝ) : ℂ) * Complex.I) =
        -(((n : ℂ) * t) * Complex.I) := by
    norm_num [sub_eq_add_neg]
    ring
  calc
    deriv (circleMap 0 1) t / (circleMap 0 1 t) ^ (n + 1)
      = (circleMap 0 1 t * Complex.I) / (circleMap 0 1 t) ^ (n + 1) := by
          rw [deriv_circleMap]
    _ = Complex.I * ((circleMap 0 1 t) / (circleMap 0 1 t) ^ (n + 1)) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ac_rfl
    _ = Complex.I * ((circleMap 0 1 t) / circleMap 0 (1 ^ (n + 1)) (((n : ℝ) + 1) * t)) := by
          rw [circleMap_zero_pow]
          congr 2
          norm_num [Nat.cast_add, Nat.cast_one]
    _ = Complex.I * circleMap 0 (1 / 1 ^ (n + 1)) (t - (((n : ℝ) + 1) * t)) := by
          rw [circleMap_zero_div]
    _ = Complex.I * Complex.exp (-(((n : ℂ) * t) * Complex.I)) := by
          rw [circleMap_zero, hphase]
          simp

/-- Helper for Exercise 12: on the unit circle, `z + z⁻¹` collapses to `2 cos t`. -/
lemma unit_circle_sum_inv_eq_two_cos
    (t : ℝ) :
    circleMap 0 1 t + (circleMap 0 1 t)⁻¹ = (2 * Real.cos t : ℂ) := by
  -- Expand both unit-circle points into `cos t ± i sin t`, then the imaginary parts cancel.
  calc
    circleMap 0 1 t + (circleMap 0 1 t)⁻¹
      = ((Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I) +
          ((Real.cos t : ℂ) - (Real.sin t : ℂ) * Complex.I) := by
            simp [circleMap_zero, Complex.exp_mul_I, exercise12_cos_add_sin_mul_I_inv,
              Complex.ofReal_cos, Complex.ofReal_sin]
    _ = (2 * Real.cos t : ℂ) := by
          ring

/-- Helper for Exercise 12: on the unit circle, `z - z⁻¹` collapses to `2 i sin t`. -/
lemma unit_circle_sub_inv_eq_two_I_sin
    (t : ℝ) :
    circleMap 0 1 t - (circleMap 0 1 t)⁻¹ = ((2 * Real.sin t : ℂ) * Complex.I) := by
  -- Expand both unit-circle points into `cos t ± i sin t`, then the real parts cancel.
  calc
    circleMap 0 1 t - (circleMap 0 1 t)⁻¹
      = ((Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I) -
          ((Real.cos t : ℂ) - (Real.sin t : ℂ) * Complex.I) := by
            simp [circleMap_zero, Complex.exp_mul_I, exercise12_cos_add_sin_mul_I_inv,
              Complex.ofReal_cos, Complex.ofReal_sin]
    _ = ((2 * Real.sin t : ℂ) * Complex.I) := by
          ring

/-- Helper for Exercise 12: reflecting `2π - t` in the modified-Bessel kernel removes the
periodic `2πn` phase and leaves the positive Fourier mode. -/
lemma reflected_modified_bessel_phase
    (n : ℕ) (t : ℝ) :
    Complex.exp (-(((n : ℂ) * (2 * Real.pi - t)) * Complex.I)) =
      Complex.exp ((((n : ℂ) * t) * Complex.I)) := by
  -- Split the reflected phase into the periodic `2πn` contribution and the desired `nt` term.
  have hperiod' :
      Complex.exp ((n : ℂ) * (2 * Real.pi * Complex.I)) = 1 := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using Complex.exp_nat_mul_two_pi_mul_I n
  have hperiod :
      Complex.exp (-((n : ℂ) * (2 * Real.pi * Complex.I))) = 1 := by
    rw [Complex.exp_neg]
    rw [hperiod']
    simp
  have hrewrite :
      -(((n : ℂ) * (2 * Real.pi - t)) * Complex.I) =
        -((n : ℂ) * (2 * Real.pi * Complex.I)) + (((n : ℂ) * t) * Complex.I) := by
    ring
  rw [hrewrite, Complex.exp_add, hperiod, one_mul]

/-- Helper for Exercise 12: reflecting `2π - t` in the ordinary Bessel kernel removes the
periodic `2πn` phase and flips the sine term to the textbook cosine argument. -/
lemma reflected_bessel_phase
    (n : ℕ) (x : ℂ) (t : ℝ) :
    Complex.exp ((x * Real.sin (2 * Real.pi - t) - (n : ℂ) * (2 * Real.pi - t)) * Complex.I) =
      Complex.exp ((((n : ℂ) * t - x * Real.sin t) * Complex.I)) := by
  -- Reflect the odd sine term, then separate the periodic `2πn` factor from the remaining phase.
  have hperiod' :
      Complex.exp ((n : ℂ) * (2 * Real.pi * Complex.I)) = 1 := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using Complex.exp_nat_mul_two_pi_mul_I n
  have hperiod :
      Complex.exp (-((n : ℂ) * (2 * Real.pi * Complex.I))) = 1 := by
    rw [Complex.exp_neg]
    rw [hperiod']
    simp
  have hrewrite :
      (x * Real.sin (2 * Real.pi - t) - (n : ℂ) * (2 * Real.pi - t)) * Complex.I =
        -((n : ℂ) * (2 * Real.pi * Complex.I)) +
          (((n : ℂ) * t - x * Real.sin t) * Complex.I) := by
    have hneg :
        x * (↑(-Real.sin t) : ℂ) * Complex.I = -(x * Complex.I * (Real.sin t : ℂ)) := by
      calc
        x * (↑(-Real.sin t) : ℂ) * Complex.I
          = x * (-(Real.sin t : ℂ)) * Complex.I := by simp
        _ = -(x * (Real.sin t : ℂ)) * Complex.I := by ring
        _ = -((x * (Real.sin t : ℂ)) * Complex.I) := by simp
        _ = -(x * Complex.I * (Real.sin t : ℂ)) := by ring
    calc
      (x * Real.sin (2 * Real.pi - t) - (n : ℂ) * (2 * Real.pi - t)) * Complex.I
        = x * (↑(-Real.sin t) : ℂ) * Complex.I - Complex.I * (n : ℂ) * Real.pi * 2 +
            Complex.I * (n : ℂ) * t := by
              rw [Real.sin_two_pi_sub]
              ring
      _ = -(x * Complex.I * (Real.sin t : ℂ)) - Complex.I * (n : ℂ) * Real.pi * 2 +
            Complex.I * (n : ℂ) * t := by
              rw [hneg]
      _ = -((n : ℂ) * (2 * Real.pi * Complex.I)) +
            (((n : ℂ) * t - x * Real.sin t) * Complex.I) := by
              ring
  rw [hrewrite, Complex.exp_add, hperiod, one_mul]

/-- Helper for Exercise 12: the unit-circle coefficient integrand for `I_n` pulls back to the
standard oscillatory kernel. -/
lemma modifiedBesselI_circle_integrand
    (n : ℕ) (x : ℂ) (t : ℝ) :
    deriv (circleMap 0 1) t *
      (Complex.exp (x * (circleMap 0 1 t + (circleMap 0 1 t)⁻¹) / 2) /
        (circleMap 0 1 t) ^ (n + 1)) =
      Complex.I * Complex.exp (x * Real.cos t) *
        Complex.exp (-(((n : ℂ) * t) * Complex.I)) := by
  -- Route correction: first separate the derivative-over-power quotient, then rewrite the
  -- remaining unit-circle algebra by the explicit identity `z + z⁻¹ = 2 cos t`.
  calc
    deriv (circleMap 0 1) t *
        (Complex.exp (x * (circleMap 0 1 t + (circleMap 0 1 t)⁻¹) / 2) /
          (circleMap 0 1 t) ^ (n + 1))
      = deriv (circleMap 0 1) t *
          (Complex.exp (x * (circleMap 0 1 t + (circleMap 0 1 t)⁻¹) / 2) *
            ((circleMap 0 1 t) ^ (n + 1))⁻¹) := by
            rw [div_eq_mul_inv]
    _ = Complex.exp (x * (circleMap 0 1 t + (circleMap 0 1 t)⁻¹) / 2) *
          (deriv (circleMap 0 1) t * ((circleMap 0 1 t) ^ (n + 1))⁻¹) := by
            ac_rfl
    _ = Complex.exp (x * (circleMap 0 1 t + (circleMap 0 1 t)⁻¹) / 2) *
          (deriv (circleMap 0 1) t / (circleMap 0 1 t) ^ (n + 1)) := by
            simp [div_eq_mul_inv]
    _ = Complex.exp (x * (circleMap 0 1 t + (circleMap 0 1 t)⁻¹) / 2) *
          (Complex.I * Complex.exp (-(((n : ℂ) * t) * Complex.I))) := by
            rw [unit_circle_deriv_div_pow_eq_fourier_phase]
    _ = Complex.I * Complex.exp (x * Real.cos t) *
          Complex.exp (-(((n : ℂ) * t) * Complex.I)) := by
            rw [unit_circle_sum_inv_eq_two_cos]
            have hexp :
                Complex.exp (x * (2 * Real.cos t : ℂ) / 2) =
                  Complex.exp (x * Real.cos t) := by
              congr 1
              ring
            rw [hexp]
            ring

/-- Helper for Exercise 12: pairing the reflected `I_n` contour kernels cancels the sine part and
produces twice the textbook cosine integrand. -/
lemma modifiedBesselI_circle_integrand_pair
    (n : ℕ) (x : ℂ) (t : ℝ) :
    (Complex.I * Complex.exp (x * Real.cos t) *
        Complex.exp (-(((n : ℂ) * t) * Complex.I))) +
      (Complex.I * Complex.exp (x * Real.cos (2 * Real.pi - t)) *
        Complex.exp (-(((n : ℂ) * (2 * Real.pi - t)) * Complex.I))) =
      (2 * Complex.I) * (Complex.exp (x * Real.cos t) * Real.cos ((n : ℝ) * t)) := by
  -- Rewrite the reflected term to the positive Fourier mode, then collapse the opposite phases
  -- with `e^{iu} + e^{-iu} = 2 cos u`.
  have hcos :
      Complex.cos ((n : ℂ) * t) = (Real.cos ((n : ℝ) * t) : ℂ) := by
    simp [Complex.ofReal_cos]
  set u : ℂ := (n : ℂ) * t
  have hsum := exercise12_exp_mul_I_add_exp_neg_mul_I u
  rw [Real.cos_two_pi_sub, reflected_modified_bessel_phase]
  calc
    Complex.I * Complex.exp (x * Real.cos t) *
        Complex.exp (-(((n : ℂ) * t) * Complex.I)) +
      Complex.I * Complex.exp (x * Real.cos t) *
        Complex.exp ((((n : ℂ) * t) * Complex.I))
      = Complex.I * Complex.exp (x * Real.cos t) *
          (Complex.exp (u * Complex.I) +
            Complex.exp (-(u * Complex.I))) := by
              ring
    _ = Complex.I * Complex.exp (x * Real.cos t) *
          (2 * Complex.cos ((n : ℂ) * t)) := by
            simpa [u, neg_mul] using
              congrArg (fun v : ℂ ↦ Complex.I * Complex.exp (x * Real.cos t) * v) hsum
    _ = (2 * Complex.I) * (Complex.exp (x * Real.cos t) * Real.cos ((n : ℝ) * t)) := by
            rw [hcos]
            ring

/-- Helper for Exercise 12: rewrite the normalized unit-circle integral as an ordinary interval
integral on `[0, 2π]`. -/
lemma exercise12_circleIntegral_pullback_interval_form
    (g : ℂ → ℂ) :
    ((2 * Real.pi * Complex.I : ℂ)⁻¹) * ∮ z in C(0, 1), g z =
      ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
        ∫ t in (0 : ℝ)..2 * Real.pi, deriv (circleMap 0 1) t * g (circleMap 0 1 t) := by
  -- Convert the circle integral to its `Icc` parametrization and then replace `Icc` by `Ioc`
  -- so the result matches the standard interval-integral notation on `[0, 2π]`.
  rw [circleIntegral_def_Icc]
  simp only [smul_eq_mul]
  rw [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le Real.two_pi_pos.le]

/-- Helper for Exercise 12: after pairing the pullback kernel on `[0, 2π]`, the normalization by
`(2 π i)⁻¹` collapses to the textbook `(π)⁻¹` factor on `[0, π]`. -/
lemma exercise12_normalized_pair_collapse
    (F K : ℝ → ℂ)
    (hF : IntervalIntegrable F volume (0 : ℝ) (2 * Real.pi))
    (hpair : ∀ t, F t + F (2 * Real.pi - t) = (2 * Complex.I) * K t) :
    ((2 * Real.pi * Complex.I : ℂ)⁻¹) * ∫ t in (0 : ℝ)..2 * Real.pi, F t =
      (Real.pi : ℂ)⁻¹ * ∫ t in (0 : ℝ)..Real.pi, K t := by
  have htwo_pi_I : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    norm_num [Real.pi_ne_zero]
  have hscalar :
      ((2 * Real.pi * Complex.I : ℂ)⁻¹) * (2 * Complex.I) = (Real.pi : ℂ)⁻¹ := by
    field_simp [htwo_pi_I, Real.pi_ne_zero]
  calc
    ((2 * Real.pi * Complex.I : ℂ)⁻¹) * ∫ t in (0 : ℝ)..2 * Real.pi, F t
      = ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
          ∫ t in (0 : ℝ)..Real.pi, (F t + F (2 * Real.pi - t)) := by
            rw [intervalIntegral_pair_reflect_two_pi F hF]
    _ = ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
          ∫ t in (0 : ℝ)..Real.pi, (2 * Complex.I) * K t := by
            congr 1
            refine intervalIntegral.integral_congr_ae <|
              Filter.Eventually.of_forall (fun t _ ↦ hpair t)
    _ = ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
          ((2 * Complex.I) * ∫ t in (0 : ℝ)..Real.pi, K t) := by
            rw [intervalIntegral.integral_const_mul]
    _ = (Real.pi : ℂ)⁻¹ * ∫ t in (0 : ℝ)..Real.pi, K t := by
            rw [← mul_assoc, hscalar]

/-- Helper for Exercise 12: the modified Bessel coefficient is the normalized unit-circle
coefficient of the Laurent expansion. -/
lemma modifiedBesselI_eq_unit_circle_coeff
    (n : ℕ) (x : ℂ) :
    I_[n] x =
      ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
        ∮ z in C(0, 1), Complex.exp (x * (z + z⁻¹) / 2) / z ^ (n + 1) := by
  let F : ℝ → ℂ := fun t ↦
    Complex.I * Complex.exp (x * Real.cos t) * Complex.exp (-(((n : ℂ) * t) * Complex.I))
  let K : ℝ → ℂ := fun t ↦
    Complex.exp (x * Real.cos t) * Real.cos ((n : ℝ) * t)
  have hF : IntervalIntegrable F volume (0 : ℝ) (2 * Real.pi) := by
    -- The paired kernel is continuous on the compact interval, hence interval-integrable.
    apply Continuous.intervalIntegrable
    dsimp [F]
    fun_prop
  -- Route correction: first pull the contour integral back to `[0, 2π]`, then collapse the
  -- reflected pair to the textbook `[0, π]` cosine integral.
  symm
  calc
    ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
        ∮ z in C(0, 1), Complex.exp (x * (z + z⁻¹) / 2) / z ^ (n + 1)
      = ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
          ∫ t in (0 : ℝ)..2 * Real.pi,
            deriv (circleMap 0 1) t *
              (Complex.exp (x * (circleMap 0 1 t + (circleMap 0 1 t)⁻¹) / 2) /
                (circleMap 0 1 t) ^ (n + 1)) := by
                  simpa using
                    (exercise12_circleIntegral_pullback_interval_form
                      (fun z ↦ Complex.exp (x * (z + z⁻¹) / 2) / z ^ (n + 1)))
    _ = ((2 * Real.pi * Complex.I : ℂ)⁻¹) * ∫ t in (0 : ℝ)..2 * Real.pi, F t := by
          congr 1
          refine intervalIntegral.integral_congr_ae <|
            Filter.Eventually.of_forall (fun t _ ↦ by
              simpa [F] using modifiedBesselI_circle_integrand n x t)
    _ = (Real.pi : ℂ)⁻¹ * ∫ t in (0 : ℝ)..Real.pi, K t := by
          exact exercise12_normalized_pair_collapse F K hF
            (fun t ↦ by
              simpa [F, K, sub_eq_add_neg] using modifiedBesselI_circle_integrand_pair n x t)
    _ = I_[n] x := by
          rfl

/-- Helper for Exercise 12: the unit-circle coefficient integrand for `J_n` pulls back to the
standard Bessel oscillatory kernel. -/
lemma besselJ_circle_integrand
    (n : ℕ) (x : ℂ) (t : ℝ) :
    deriv (circleMap 0 1) t *
      (Complex.exp (x * (circleMap 0 1 t - (circleMap 0 1 t)⁻¹) / 2) /
        (circleMap 0 1 t) ^ (n + 1)) =
      Complex.I *
        Complex.exp ((x * Real.sin t - (n : ℂ) * t) * Complex.I) := by
  -- Route correction: first isolate the Fourier quotient, then replace `z - z⁻¹` by
  -- `2 i sin t` before merging the two exponentials into the textbook oscillatory phase.
  calc
    deriv (circleMap 0 1) t *
        (Complex.exp (x * (circleMap 0 1 t - (circleMap 0 1 t)⁻¹) / 2) /
          (circleMap 0 1 t) ^ (n + 1))
      = deriv (circleMap 0 1) t *
          (Complex.exp (x * (circleMap 0 1 t - (circleMap 0 1 t)⁻¹) / 2) *
            ((circleMap 0 1 t) ^ (n + 1))⁻¹) := by
            rw [div_eq_mul_inv]
    _ = Complex.exp (x * (circleMap 0 1 t - (circleMap 0 1 t)⁻¹) / 2) *
          (deriv (circleMap 0 1) t * ((circleMap 0 1 t) ^ (n + 1))⁻¹) := by
            ac_rfl
    _ = Complex.exp (x * (circleMap 0 1 t - (circleMap 0 1 t)⁻¹) / 2) *
          (deriv (circleMap 0 1) t / (circleMap 0 1 t) ^ (n + 1)) := by
            simp [div_eq_mul_inv]
    _ = Complex.exp (x * (circleMap 0 1 t - (circleMap 0 1 t)⁻¹) / 2) *
          (Complex.I * Complex.exp (-(((n : ℂ) * t) * Complex.I))) := by
            rw [unit_circle_deriv_div_pow_eq_fourier_phase]
    _ = Complex.I *
          (Complex.exp (x * (circleMap 0 1 t - (circleMap 0 1 t)⁻¹) / 2) *
            Complex.exp (-(((n : ℂ) * t) * Complex.I))) := by
            ring
    _ = Complex.I *
          Complex.exp ((x * Real.sin t - (n : ℂ) * t) * Complex.I) := by
            rw [unit_circle_sub_inv_eq_two_I_sin]
            rw [← Complex.exp_add]
            congr 1
            ring

/-- Helper for Exercise 12: pairing the reflected `J_n` contour kernels cancels the odd sine part
and produces twice the textbook Bessel cosine integrand. -/
lemma besselJ_circle_integrand_pair
    (n : ℕ) (x : ℂ) (t : ℝ) :
    (Complex.I * Complex.exp ((x * Real.sin t - (n : ℂ) * t) * Complex.I)) +
      (Complex.I * Complex.exp ((x * Real.sin (2 * Real.pi - t) -
        (n : ℂ) * (2 * Real.pi - t)) * Complex.I)) =
      (2 * Complex.I) * Complex.cos ((n : ℂ) * t - x * Real.sin t) := by
  -- Rewrite the reflected phase to the positive mode, then combine the opposite phases into the
  -- cosine of the textbook Bessel argument.
  have hfirst :
      Complex.exp ((x * Real.sin t - (n : ℂ) * t) * Complex.I) =
        Complex.exp (-(((n : ℂ) * t - x * Real.sin t) * Complex.I)) := by
    congr 1
    ring
  set u : ℂ := (n : ℂ) * t - x * Real.sin t
  have hsum := exercise12_exp_mul_I_add_exp_neg_mul_I u
  have hsum' :
      Complex.I * (Complex.exp (u * Complex.I) + Complex.exp (-(u * Complex.I))) =
        Complex.I * (2 * Complex.cos u) := by
    simpa [neg_mul] using congrArg (fun v : ℂ ↦ Complex.I * v) hsum
  rw [reflected_bessel_phase, hfirst]
  calc
    Complex.I * Complex.exp (-(((n : ℂ) * t - x * Real.sin t) * Complex.I)) +
      Complex.I * Complex.exp ((((n : ℂ) * t - x * Real.sin t) * Complex.I))
      = Complex.I *
          (Complex.exp (u * Complex.I) + Complex.exp (-(u * Complex.I))) := by
              ring
    _ = Complex.I * (2 * Complex.cos ((n : ℂ) * t - x * Real.sin t)) := by
          simpa [u] using hsum'
    _ = (2 * Complex.I) * Complex.cos ((n : ℂ) * t - x * Real.sin t) := by
          ring

/-- Helper for Exercise 12: the Bessel `J_n` coefficient is the normalized unit-circle coefficient
of the Laurent expansion. -/
lemma besselJ_eq_unit_circle_coeff
    (n : ℕ) (x : ℂ) :
    J_[n] x =
      ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
        ∮ z in C(0, 1), Complex.exp (x * (z - z⁻¹) / 2) / z ^ (n + 1) := by
  let F : ℝ → ℂ := fun t ↦
    Complex.I * Complex.exp ((x * Real.sin t - (n : ℂ) * t) * Complex.I)
  let K : ℝ → ℂ := fun t ↦
    Complex.cos ((n : ℂ) * t - x * Real.sin t)
  have hF : IntervalIntegrable F volume (0 : ℝ) (2 * Real.pi) := by
    -- The pulled-back Bessel kernel is continuous, so the interval integral is available.
    apply Continuous.intervalIntegrable
    dsimp [F]
    fun_prop
  -- Route correction: reuse the same pullback-plus-pairing architecture as for `I_n`.
  symm
  calc
    ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
        ∮ z in C(0, 1), Complex.exp (x * (z - z⁻¹) / 2) / z ^ (n + 1)
      = ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
          ∫ t in (0 : ℝ)..2 * Real.pi,
            deriv (circleMap 0 1) t *
              (Complex.exp (x * (circleMap 0 1 t - (circleMap 0 1 t)⁻¹) / 2) /
                (circleMap 0 1 t) ^ (n + 1)) := by
                  simpa using
                    (exercise12_circleIntegral_pullback_interval_form
                      (fun z ↦ Complex.exp (x * (z - z⁻¹) / 2) / z ^ (n + 1)))
    _ = ((2 * Real.pi * Complex.I : ℂ)⁻¹) * ∫ t in (0 : ℝ)..2 * Real.pi, F t := by
          congr 1
          refine intervalIntegral.integral_congr_ae <|
            Filter.Eventually.of_forall (fun t _ ↦ by
              simpa [F] using besselJ_circle_integrand n x t)
    _ = (Real.pi : ℂ)⁻¹ * ∫ t in (0 : ℝ)..Real.pi, K t := by
          exact exercise12_normalized_pair_collapse F K hF
            (fun t ↦ by
              simpa [F, K, sub_eq_add_neg] using besselJ_circle_integrand_pair n x t)
    _ = J_[n] x := by
          rfl

/-- Helper for Exercise 12: membership in the annulus `0 < |z| < ρ` forces `z ≠ 0`. -/
lemma exercise12_ne_zero_of_mem_complexOpenAnnulus_zero
    {ρ : ENNReal} {z : ℂ} (hz : z ∈ complexOpenAnnulus 0 ρ) : z ≠ 0 := by
  -- The inner annulus inequality is exactly the statement that the norm is positive.
  intro hz0
  have hzpos : (0 : ENNReal) < ‖z‖₊ := hz.1
  simp [hz0] at hzpos

/-- Helper for Exercise 12: precomposing a Laurent series on `0 < |z| < ρ` with `z ↦ -z`
multiplies its coefficients by `(-1)^n`. -/
lemma exercise12_neg_laurentSeriesOnAnnulus
    {ρ : NNReal} {a : ℤ → ℂ} (ha : IsLaurentSeriesOnAnnulus a 0 ρ) :
    IsLaurentSeriesOnAnnulus (fun n ↦ (-1 : ℂ) ^ n * a n) 0 ρ := by
  have hmaps : Set.MapsTo (fun z : ℂ ↦ -z) (complexOpenAnnulus 0 ρ) (complexOpenAnnulus 0 ρ) := by
    intro z hz
    simpa [complexOpenAnnulus] using hz
  have hcomp :
      HasSumLocallyUniformlyOn
        (fun n z ↦ laurentTerm a n (-z))
        (fun z ↦ ∑' n : ℤ, laurentTerm a n (-z))
        (complexOpenAnnulus 0 ρ) := by
    -- Negation preserves the annulus, so we may pull the Laurent family back along `z ↦ -z`.
    exact ha.hasSumLocallyUniformlyOn.comp (fun z : ℂ ↦ -z) hmaps continuous_neg.continuousOn
  -- Rewrite the pulled-back Laurent family `a_n (-z)^n` into `((-1)^n a_n) z^n`.
  refine SummableLocallyUniformlyOn_congr ?_ hcomp.summableLocallyUniformlyOn
  intro n z hz
  change laurentTerm a n (-z) = laurentTerm (fun n ↦ (-1 : ℂ) ^ n * a n) n z
  calc
    laurentTerm a n (-z)
      = a n * (-z) ^ n := by
          simp [laurentTerm]
    _ = ((-1 : ℂ) ^ n * a n) * z ^ n := by
          calc
            a n * (-z) ^ n = a n * (((-1 : ℂ) ^ n) * z ^ n) := by
              congr 1
              calc
                (-z) ^ n = (((-1 : ℂ) * z) : ℂ) ^ n := by
                  congr 1
                  ring
                _ = ((-1 : ℂ) ^ n) * z ^ n := by
                  simpa using (mul_zpow (-1 : ℂ) z n)
            _ = ((-1 : ℂ) ^ n * a n) * z ^ n := by
              ring
    _ = laurentTerm (fun n ↦ (-1 : ℂ) ^ n * a n) n z := by
          simp [laurentTerm]

/-- Helper for Exercise 12: the annulus `0 < |z| < R` is open. -/
lemma exercise12_isOpen_complexOpenAnnulus (R : ENNReal) :
    IsOpen (complexOpenAnnulus 0 R) := by
  simpa [complexOpenAnnulus] using
    (isOpen_lt (continuous_const : Continuous fun _ : ℂ ↦ (0 : ENNReal))
      (ENNReal.continuous_coe.comp continuous_nnnorm)).inter
      (isOpen_lt (ENNReal.continuous_coe.comp continuous_nnnorm)
        (continuous_const : Continuous fun _ : ℂ ↦ R))

/-- Helper for Exercise 12: multiplying a locally uniformly summable series by a fixed
continuous factor preserves local uniform summability on the same set. -/
lemma exercise12_hasSumLocallyUniformlyOn_mul_fixed
    {X ι : Type*} [TopologicalSpace X] {s : Set X} {F : ι → X → ℂ} {G g : X → ℂ}
    (h : HasSumLocallyUniformlyOn F G s) (hg : ContinuousOn g s) (hG : ContinuousOn G s) :
    HasSumLocallyUniformlyOn (fun i x ↦ g x * F i x) (fun x ↦ g x * G x) s := by
  rw [hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn] at h ⊢
  have hconst : TendstoLocallyUniformlyOn (fun _ : Finset ι ↦ g) g Filter.atTop s := by
    intro u hu x hx
    refine ⟨s, self_mem_nhdsWithin, ?_⟩
    filter_upwards with n y hy
    exact refl_mem_uniformity hu
  refine (hconst.mul₀ h hg hG).congr ?_
  intro t x hx
  simp [Finset.mul_sum]

/-- Helper for Exercise 12: on a compact set, locally uniform summability upgrades to uniform
summability. -/
lemma exercise12_hasSumUniformlyOn_of_hasSumLocallyUniformlyOn_isCompact
    {X ι : Type*} [TopologicalSpace X] {s : Set X} {F : ι → X → ℂ} {G : X → ℂ}
    (hs : IsCompact s) (h : HasSumLocallyUniformlyOn F G s) :
    HasSumUniformlyOn F G s := by
  rw [hasSumUniformlyOn_iff_tendstoUniformlyOn]
  rw [← tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hs]
  exact hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp h

/-- Helper for Exercise 12: a positive-radius circle lies in the annulus `ρ₂ < ‖z‖ < ρ₁`
whenever its radius lies strictly between `ρ₂` and `ρ₁`. -/
lemma exercise12_sphere_subset_complexOpenAnnulus_of_lt_lt
    {ρ₂ ρ₁ R : NNReal} (hρ₂ : ρ₂ < R) (hρ₁ : R < ρ₁) :
    Metric.sphere (0 : ℂ) (R : ℝ) ⊆ complexOpenAnnulus ρ₂ ρ₁ := by
  intro z hz
  have hzR : ‖z‖ = (R : ℝ) := by
    simpa [Metric.mem_sphere, dist_eq_norm, sub_zero] using hz
  have hzR' : ‖z‖₊ = R := by
    exact NNReal.coe_injective (by simp [hzR])
  change (ρ₂ : ENNReal) < ‖z‖₊ ∧ ‖z‖₊ < (ρ₁ : ENNReal)
  constructor
  · simpa [hzR'] using (show (ρ₂ : ENNReal) < (R : ENNReal) by exact_mod_cast hρ₂)
  · simpa [hzR'] using (show (R : ENNReal) < (ρ₁ : ENNReal) by exact_mod_cast hρ₁)

/-- Helper for Exercise 12: points on a positive-radius circle are nonzero. -/
lemma exercise12_ne_zero_of_mem_sphere_zero_of_pos {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : z ∈ Metric.sphere (0 : ℂ) R) : z ≠ 0 := by
  have hzR : ‖z‖ = R := by
    simpa using mem_sphere_iff_norm.mp hz
  exact fun hz0 ↦ (ne_of_gt hR) <| by simpa [hz0] using hzR.symm

/-- Helper for Exercise 12: each Laurent monomial is continuous on a positive-radius circle. -/
lemma exercise12_laurentTerm_continuousOn_sphere
    {a : ℤ → ℂ} {R : NNReal} (hR : 0 < (R : ℝ)) (m : ℤ) :
    ContinuousOn (laurentTerm a m) (Metric.sphere (0 : ℂ) (R : ℝ)) := by
  refine (continuousOn_const.mul (continuousOn_zpow₀ (m := m))).mono ?_
  intro z hz
  exact exercise12_ne_zero_of_mem_sphere_zero_of_pos hR hz

/-- Helper for Exercise 12: uniform convergence of a Laurent family on a circle allows termwise
circle integration. -/
lemma exercise12_circleIntegral_tsum_of_summableUniformlyOn_sphere
    {F : ℤ → ℂ → ℂ} {R : NNReal}
    (hcont : ∀ m, ContinuousOn (F m) (Metric.sphere (0 : ℂ) (R : ℝ)))
    (hsum : SummableUniformlyOn F (Metric.sphere (0 : ℂ) (R : ℝ))) :
    (∮ z in C(0, (R : ℝ)), ∑' m : ℤ, F m z) = ∑' m : ℤ, ∮ z in C(0, (R : ℝ)), F m z := by
  have hhas :
      HasSumUniformlyOn F (fun z ↦ ∑' m : ℤ, F m z) (Metric.sphere (0 : ℂ) (R : ℝ)) :=
    hsum.hasSumUniformlyOn
  have hcont_partial :
      ∀ s : Finset ℤ,
        ContinuousOn (fun z : ℂ ↦ ∑ m ∈ s, F m z) (Metric.sphere (0 : ℂ) (R : ℝ)) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simpa using (continuousOn_const : ContinuousOn (fun _ : ℂ ↦ (0 : ℂ)) _)
    · intro m s hm hs
      simpa [Finset.sum_insert, hm] using (hcont m).add hs
  have htendsto :
      Filter.Tendsto (fun s : Finset ℤ ↦ ∮ z in C(0, (R : ℝ)), ∑ m ∈ s, F m z) Filter.atTop
        (𝓝 (∮ z in C(0, (R : ℝ)), ∑' m : ℤ, F m z)) :=
    hhas.tendstoUniformlyOn.tendsto_circleIntegral_of_continuousOn R.2
      (Filter.Eventually.of_forall hcont_partial)
  have hsum_int :
      HasSum (fun m : ℤ ↦ ∮ z in C(0, (R : ℝ)), F m z)
        (∮ z in C(0, (R : ℝ)), ∑' m : ℤ, F m z) := by
    rw [HasSum]
    convert htendsto using 1
    ext s
    symm
    exact circleIntegral.integral_fun_sum fun m _ ↦ (hcont m).circleIntegrable R.2
  exact hsum_int.tsum_eq.symm

/-- Helper for Exercise 12: on the unit circle, the Cauchy coefficient formula for a Laurent
series on `0 < |z| < R` identifies the nonnegative coefficient `a n`. -/
lemma exercise12_laurent_nonneg_coeff_eq_unit_circle_coeff
    {R : NNReal} {a : ℤ → ℂ} (ha : IsLaurentSeriesOnAnnulus a 0 R)
    (h1R : (1 : NNReal) < R) (n : ℕ) :
    ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
        ∮ w in C(0, 1), (∑' m : ℤ, a m * w ^ m) / w ^ (n + 1) =
      a (n : ℤ) := by
  have hbase :
      HasSumLocallyUniformlyOn (laurentTerm a) (fun z ↦ ∑' m : ℤ, laurentTerm a m z)
        (sphere (0 : ℂ) (1 : ℝ)) := by
    refine ha.hasSumLocallyUniformlyOn.mono ?_
    exact exercise12_sphere_subset_complexOpenAnnulus_of_lt_lt
      (ρ₂ := 0) (ρ₁ := R) (R := 1) (by norm_num) h1R
  have hsum_cont :
      ContinuousOn (fun z : ℂ ↦ ∑' m : ℤ, laurentTerm a m z) (sphere (0 : ℂ) (1 : ℝ)) := by
    have hpartial_cont :
        ∀ s : Finset ℤ,
          ContinuousOn (fun z : ℂ ↦ ∑ m ∈ s, laurentTerm a m z) (sphere (0 : ℂ) (1 : ℝ)) := by
      intro s
      refine Finset.induction_on s ?_ ?_
      · simpa using (continuousOn_const : ContinuousOn (fun _ : ℂ ↦ (0 : ℂ)) _)
      · intro m s hm hs
        simpa [Finset.sum_insert, hm] using
          (exercise12_laurentTerm_continuousOn_sphere (a := a) (R := 1) (by norm_num) m).add hs
    exact
      (hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hbase).continuousOn
        (Filter.Frequently.of_forall hpartial_cont)
  have hshift_cont :
      ContinuousOn (fun z : ℂ ↦ z ^ (Int.negSucc n)) (sphere (0 : ℂ) (1 : ℝ)) := by
    refine (continuousOn_zpow₀ (m := Int.negSucc n)).mono ?_
    intro z hz
    exact exercise12_ne_zero_of_mem_sphere_zero_of_pos (by norm_num : (0 : ℝ) < 1) hz
  have hshifted :
      SummableUniformlyOn
        (fun m z ↦ z ^ (Int.negSucc n) * laurentTerm a m z)
        (sphere (0 : ℂ) (1 : ℝ)) := by
    let s : Set ℂ := sphere (0 : ℂ) (1 : ℝ)
    have hshiftedLoc :
        HasSumLocallyUniformlyOn
          (fun m z ↦ z ^ (Int.negSucc n) * laurentTerm a m z)
          (fun z ↦ z ^ (Int.negSucc n) * ∑' m : ℤ, laurentTerm a m z) s :=
      exercise12_hasSumLocallyUniformlyOn_mul_fixed hbase hshift_cont hsum_cont
    exact
      (exercise12_hasSumUniformlyOn_of_hasSumLocallyUniformlyOn_isCompact
        (by simpa [s] using isCompact_sphere (0 : ℂ) (1 : ℝ)) hshiftedLoc).summableUniformlyOn
  have hsumCircle :
      (∮ z in C(0, (1 : ℝ)), ∑' m : ℤ, z ^ (Int.negSucc n) * laurentTerm a m z) =
        ∑' m : ℤ, ∮ z in C(0, (1 : ℝ)), z ^ (Int.negSucc n) * laurentTerm a m z := by
    exact
      exercise12_circleIntegral_tsum_of_summableUniformlyOn_sphere (R := 1)
        (fun m ↦
          (hshift_cont.mul
            (exercise12_laurentTerm_continuousOn_sphere (a := a) (R := 1) (by norm_num) m)))
        hshifted
  have hterm (m : ℤ) :
      (∮ z in C(0, (1 : ℝ)), z ^ (Int.negSucc n) * laurentTerm a m z) =
        if m = (n : ℤ) then (2 * Real.pi * Complex.I : ℂ) * a (n : ℤ) else 0 := by
    have hcongr :
        (∮ z in C(0, (1 : ℝ)), z ^ (Int.negSucc n) * laurentTerm a m z) =
          ∮ z in C(0, (1 : ℝ)), a m * z ^ (Int.negSucc n + m) := by
      refine circleIntegral.integral_congr (by norm_num : (0 : ℝ) ≤ 1) ?_
      intro z hz
      have hz0 : z ≠ 0 :=
        exercise12_ne_zero_of_mem_sphere_zero_of_pos (by norm_num : (0 : ℝ) < 1) hz
      calc
        z ^ (Int.negSucc n) * laurentTerm a m z
          = z ^ (Int.negSucc n) * (a m * z ^ m) := by simp [laurentTerm]
        _ = a m * (z ^ (Int.negSucc n) * z ^ m) := by ac_rfl
        _ = a m * z ^ (Int.negSucc n + m) := by rw [zpow_add₀ hz0]
    calc
      (∮ z in C(0, (1 : ℝ)), z ^ (Int.negSucc n) * laurentTerm a m z)
        = ∮ z in C(0, (1 : ℝ)), a m * z ^ (Int.negSucc n + m) := hcongr
      _ = a m * (∮ z in C(0, (1 : ℝ)), z ^ (Int.negSucc n + m)) := by
            rw [circleIntegral.integral_const_mul]
      _ = a m * (if Int.negSucc n + m = -1 then 2 * Real.pi * Complex.I else 0) := by
            rw [exercise12_circleIntegral_zpow_eq_residue]
      _ = if m = (n : ℤ) then (2 * Real.pi * Complex.I : ℂ) * a (n : ℤ) else 0 := by
            by_cases hm : m = (n : ℤ)
            · subst hm
              have hres : Int.negSucc n + (n : ℤ) = -1 := by omega
              rw [if_pos hres]
              simp [mul_comm, mul_left_comm]
            · have hneq : Int.negSucc n + m ≠ -1 := by
                intro hres
                exact hm (by omega)
              rw [if_neg hneq, if_neg hm]
              simp
  calc
    ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
        ∮ w in C(0, 1), (∑' m : ℤ, a m * w ^ m) / w ^ (n + 1)
      = ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
          ∮ w in C(0, 1), ∑' m : ℤ, w ^ (Int.negSucc n) * laurentTerm a m w := by
            refine congrArg (fun s : ℂ ↦ ((2 * Real.pi * Complex.I : ℂ)⁻¹) * s) ?_
            refine circleIntegral.integral_congr (by norm_num : (0 : ℝ) ≤ 1) ?_
            intro w hw
            have hwAnn : w ∈ complexOpenAnnulus 0 R :=
              exercise12_sphere_subset_complexOpenAnnulus_of_lt_lt (ρ₂ := 0) (ρ₁ := R) (R := 1)
                (by norm_num) h1R hw
            have hw0 : w ≠ 0 :=
              exercise12_ne_zero_of_mem_sphere_zero_of_pos (by norm_num : (0 : ℝ) < 1) hw
            calc
              (∑' m : ℤ, a m * w ^ m) / w ^ (n + 1)
                = (1 / w) ^ n • w⁻¹ • (∑' m : ℤ, a m * w ^ m) := by
                    rw [smul_eq_mul, smul_eq_mul, div_eq_mul_inv]
                    calc
                      (∑' m : ℤ, a m * w ^ m) * (w ^ (n + 1 : ℕ))⁻¹
                        = (w ^ (n + 1 : ℕ))⁻¹ * (∑' m : ℤ, a m * w ^ m) := by ac_rfl
                      _ = (((1 / w : ℂ) ^ n) * w⁻¹) * (∑' m : ℤ, a m * w ^ m) := by
                          congr 1
                          calc
                            (w ^ (n + 1 : ℕ))⁻¹ = ((w ^ n) * w)⁻¹ := by rw [pow_succ]
                            _ = w⁻¹ * (w ^ n)⁻¹ := by rw [mul_inv_rev]
                            _ = (w ^ n)⁻¹ * w⁻¹ := by ac_rfl
                            _ = (1 / w : ℂ) ^ n * w⁻¹ := by simp [one_div]
                      _ = (1 / w) ^ n * (w⁻¹ * ∑' m : ℤ, a m * w ^ m) := by ring
              _ = ∑' m : ℤ, w ^ (Int.negSucc n) * laurentTerm a m w := by
                    calc
                      (1 / w) ^ n • w⁻¹ • (∑' m : ℤ, a m * w ^ m)
                        = w ^ (Int.negSucc n) * ∑' m : ℤ, a m * w ^ m := by
                            rw [smul_eq_mul, smul_eq_mul]
                            calc
                              (1 / w : ℂ) ^ n * (w⁻¹ * ∑' m : ℤ, a m * w ^ m)
                                  = (((1 / w : ℂ) ^ n) * w⁻¹) * ∑' m : ℤ, a m * w ^ m := by ring
                              _ = w ^ (Int.negSucc n) * ∑' m : ℤ, a m * w ^ m := by
                                  congr 1
                                  calc
                                    ((1 / w : ℂ) ^ n) * w⁻¹ = (w ^ n)⁻¹ * w⁻¹ := by simp [one_div]
                                    _ = w⁻¹ * (w ^ n)⁻¹ := by ac_rfl
                                    _ = (w ^ n * w)⁻¹ := by rw [mul_inv_rev]
                                    _ = ((w ^ (n + 1 : ℕ)) : ℂ)⁻¹ := by rw [pow_succ]
                                    _ = w ^ (Int.negSucc n) := by rw [zpow_negSucc]
                      _ = w ^ (Int.negSucc n) * ∑' m : ℤ, laurentTerm a m w := by
                            refine congrArg (fun s : ℂ ↦ w ^ (Int.negSucc n) * s) ?_
                            refine tsum_congr ?_
                            intro m
                            simp [laurentTerm]
                      _ = ∑' m : ℤ, w ^ (Int.negSucc n) * laurentTerm a m w := by
                            rw [tsum_mul_left]
    _ = ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
          ∑' m : ℤ, ∮ w in C(0, 1), w ^ (Int.negSucc n) * laurentTerm a m w := by
            rw [hsumCircle]
    _ = ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
          ∑' m : ℤ, if m = (n : ℤ) then (2 * Real.pi * Complex.I : ℂ) * a (n : ℤ) else 0 := by
            refine congrArg (fun s : ℂ ↦ ((2 * Real.pi * Complex.I : ℂ)⁻¹) * s) ?_
            refine tsum_congr ?_
            intro m
            exact hterm m
    _ = ((2 * Real.pi * Complex.I : ℂ)⁻¹) * ((2 * Real.pi * Complex.I : ℂ) * a (n : ℤ)) := by
          rw [tsum_ite_eq]
    _ = a (n : ℤ) := by
          have htwo_pi_i_ne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
            simp [Real.pi_ne_zero]
          rw [← mul_assoc, inv_mul_cancel₀ htwo_pi_i_ne, one_mul]

/-- Helper for Exercise 12: on the unit circle, the reciprocal Cauchy coefficient formula for a
Laurent series on `0 < |z| < R` identifies the negative coefficient `a (Int.negSucc n)`. -/
lemma exercise12_laurent_neg_coeff_eq_unit_circle_reciprocal_coeff
    {R : NNReal} {a : ℤ → ℂ} (ha : IsLaurentSeriesOnAnnulus a 0 R)
    (h1R : (1 : NNReal) < R) (n : ℕ) :
    ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
        ∮ w in C(0, 1),
          (1 / w) ^ n * w⁻¹ * ((w⁻¹) * ∑' m : ℤ, a m * (w⁻¹) ^ m) =
      a (Int.negSucc n) := by
  have hbase :
      HasSumLocallyUniformlyOn
        (fun m w ↦ laurentTerm a m (w⁻¹))
        (fun w ↦ ∑' m : ℤ, laurentTerm a m (w⁻¹))
        (sphere (0 : ℂ) (1 : ℝ)) := by
    refine ha.hasSumLocallyUniformlyOn.comp (fun w : ℂ ↦ w⁻¹) ?_ ?_
    · intro w hw
      have hw_norm : ‖w‖ = (1 : ℝ) := by simpa using mem_sphere_iff_norm.mp hw
      have hw_inv_norm : ‖w⁻¹‖ = (1 : ℝ) := by simp [norm_inv, hw_norm]
      have hw_inv_norm' : ‖w⁻¹‖₊ = (1 : NNReal) := by
        exact NNReal.coe_injective (by simpa using hw_inv_norm)
      change (0 : ENNReal) < ‖w⁻¹‖₊ ∧ ‖w⁻¹‖₊ < (R : ENNReal)
      constructor
      · simp [hw_inv_norm']
      · have : ((1 : NNReal) : ENNReal) < (R : ENNReal) := by exact_mod_cast h1R
        simpa [hw_inv_norm'] using this
    · refine continuousOn_inv₀.mono ?_
      intro w hw
      exact exercise12_ne_zero_of_mem_sphere_zero_of_pos (by norm_num : (0 : ℝ) < 1) hw
  have hsum_cont :
      ContinuousOn (fun w : ℂ ↦ ∑' m : ℤ, laurentTerm a m (w⁻¹)) (sphere (0 : ℂ) (1 : ℝ)) := by
    have hpartial_cont :
        ∀ s : Finset ℤ,
          ContinuousOn (fun w : ℂ ↦ ∑ m ∈ s, laurentTerm a m (w⁻¹)) (sphere (0 : ℂ) (1 : ℝ)) := by
      intro s
      refine Finset.induction_on s ?_ ?_
      · simpa using (continuousOn_const : ContinuousOn (fun _ : ℂ ↦ (0 : ℂ)) _)
      · intro m s hm hs
        have hcont_inv : ContinuousOn (fun w : ℂ ↦ w⁻¹) (sphere (0 : ℂ) (1 : ℝ)) := by
          refine continuousOn_inv₀.mono ?_
          intro w hw
          exact exercise12_ne_zero_of_mem_sphere_zero_of_pos (by norm_num : (0 : ℝ) < 1) hw
        have hmaps :
            Set.MapsTo (fun w : ℂ ↦ w⁻¹) (sphere (0 : ℂ) (1 : ℝ))
              (sphere (0 : ℂ) (1 : ℝ)) := by
          intro w hw
          have hw_norm : ‖w‖ = (1 : ℝ) := by simpa using mem_sphere_iff_norm.mp hw
          rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_inv, hw_norm]
          norm_num
        simpa [Finset.sum_insert, hm] using
          ((exercise12_laurentTerm_continuousOn_sphere (a := a) (R := 1) (by norm_num) m).comp
            hcont_inv hmaps).add hs
    exact
      (hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hbase).continuousOn
        (Filter.Frequently.of_forall hpartial_cont)
  have hshift_cont :
      ContinuousOn (fun w : ℂ ↦ w ^ (-(n + 2 : ℤ))) (sphere (0 : ℂ) (1 : ℝ)) := by
    refine (continuousOn_zpow₀ (m := (-(n + 2 : ℤ)))).mono ?_
    intro w hw
    exact exercise12_ne_zero_of_mem_sphere_zero_of_pos (by norm_num : (0 : ℝ) < 1) hw
  have hshifted :
      SummableUniformlyOn
        (fun m w ↦ w ^ (-(n + 2 : ℤ)) * laurentTerm a m (w⁻¹))
        (sphere (0 : ℂ) (1 : ℝ)) := by
    let s : Set ℂ := sphere (0 : ℂ) (1 : ℝ)
    have hshiftedLoc :
        HasSumLocallyUniformlyOn
          (fun m w ↦ w ^ (-(n + 2 : ℤ)) * laurentTerm a m (w⁻¹))
          (fun w ↦ w ^ (-(n + 2 : ℤ)) * ∑' m : ℤ, laurentTerm a m (w⁻¹)) s :=
      exercise12_hasSumLocallyUniformlyOn_mul_fixed hbase hshift_cont hsum_cont
    exact
      (exercise12_hasSumUniformlyOn_of_hasSumLocallyUniformlyOn_isCompact
        (by simpa [s] using isCompact_sphere (0 : ℂ) (1 : ℝ)) hshiftedLoc).summableUniformlyOn
  have hsumCircle :
      (∮ w in C(0, (1 : ℝ)), ∑' m : ℤ, w ^ (-(n + 2 : ℤ)) * laurentTerm a m (w⁻¹)) =
        ∑' m : ℤ, ∮ w in C(0, (1 : ℝ)), w ^ (-(n + 2 : ℤ)) * laurentTerm a m (w⁻¹) := by
    exact
      exercise12_circleIntegral_tsum_of_summableUniformlyOn_sphere (R := 1)
        (fun m ↦
          (hshift_cont.mul <| by
            have hcont_inv : ContinuousOn (fun w : ℂ ↦ w⁻¹) (sphere (0 : ℂ) (1 : ℝ)) := by
              refine continuousOn_inv₀.mono ?_
              intro w hw
              exact exercise12_ne_zero_of_mem_sphere_zero_of_pos (by norm_num : (0 : ℝ) < 1) hw
            have hmaps :
                Set.MapsTo (fun w : ℂ ↦ w⁻¹) (sphere (0 : ℂ) (1 : ℝ))
                  (sphere (0 : ℂ) (1 : ℝ)) := by
              intro w hw
              have hw_norm : ‖w‖ = (1 : ℝ) := by simpa using mem_sphere_iff_norm.mp hw
              rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_inv, hw_norm]
              norm_num
            exact
              (exercise12_laurentTerm_continuousOn_sphere (a := a) (R := 1) (by norm_num) m).comp
                hcont_inv hmaps))
        hshifted
  have hterm (m : ℤ) :
      (∮ w in C(0, (1 : ℝ)), w ^ (-(n + 2 : ℤ)) * laurentTerm a m (w⁻¹)) =
        if m = Int.negSucc n then (2 * Real.pi * Complex.I : ℂ) * a (Int.negSucc n) else 0 := by
    have hcongr :
        (∮ w in C(0, (1 : ℝ)), w ^ (-(n + 2 : ℤ)) * laurentTerm a m (w⁻¹)) =
          ∮ w in C(0, (1 : ℝ)), a m * w ^ (-(n + 2 : ℤ) - m) := by
      refine circleIntegral.integral_congr (by norm_num : (0 : ℝ) ≤ 1) ?_
      intro w hw
      have hw0 : w ≠ 0 :=
        exercise12_ne_zero_of_mem_sphere_zero_of_pos (by norm_num : (0 : ℝ) < 1) hw
      calc
        w ^ (-(n + 2 : ℤ)) * laurentTerm a m (w⁻¹)
          = w ^ (-(n + 2 : ℤ)) * (a m * (w⁻¹) ^ m) := by simp [laurentTerm]
        _ = a m * (w ^ (-(n + 2 : ℤ)) * (w⁻¹) ^ m) := by ac_rfl
        _ = a m * (w ^ (-(n + 2 : ℤ)) * (w ^ m)⁻¹) := by rw [inv_zpow]
        _ = a m * (w ^ (-(n + 2 : ℤ)) * w ^ (-m)) := by rw [← zpow_neg]
        _ = a m * w ^ (-(n + 2 : ℤ) - m) := by
            rw [show (-(n + 2 : ℤ) - m) = (-(n + 2 : ℤ)) + (-m) by ring]
            rw [zpow_add₀ hw0]
    calc
      (∮ w in C(0, (1 : ℝ)), w ^ (-(n + 2 : ℤ)) * laurentTerm a m (w⁻¹))
        = ∮ w in C(0, (1 : ℝ)), a m * w ^ (-(n + 2 : ℤ) - m) := hcongr
      _ = a m * (∮ w in C(0, (1 : ℝ)), w ^ (-(n + 2 : ℤ) - m)) := by
            rw [circleIntegral.integral_const_mul]
      _ = a m * (if (-(n + 2 : ℤ) - m = -1) then 2 * Real.pi * Complex.I else 0) := by
            rw [exercise12_circleIntegral_zpow_eq_residue]
      _ = if m = Int.negSucc n then (2 * Real.pi * Complex.I : ℂ) * a (Int.negSucc n) else 0 := by
            by_cases hm : m = Int.negSucc n
            · subst hm
              have hres : (-(n + 2 : ℤ) - Int.negSucc n = -1) := by omega
              rw [if_pos hres]
              simp [mul_comm, mul_left_comm]
            · have hneq : (-(n + 2 : ℤ) - m ≠ -1) := by
                intro hres
                exact hm (by omega)
              rw [if_neg hneq, if_neg hm]
              simp
  calc
    ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
        ∮ w in C(0, 1),
          (1 / w) ^ n * w⁻¹ * ((w⁻¹) * ∑' m : ℤ, a m * (w⁻¹) ^ m)
      = ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
          ∮ w in C(0, 1), ∑' m : ℤ, w ^ (-(n + 2 : ℤ)) * laurentTerm a m (w⁻¹) := by
            refine congrArg (fun s : ℂ ↦ ((2 * Real.pi * Complex.I : ℂ)⁻¹) * s) ?_
            refine circleIntegral.integral_congr (by norm_num : (0 : ℝ) ≤ 1) ?_
            intro w hw
            have hwAnn : w⁻¹ ∈ complexOpenAnnulus 0 R := by
              have hw_norm : ‖w‖ = (1 : ℝ) := by simpa using mem_sphere_iff_norm.mp hw
              have hw_inv_norm : ‖w⁻¹‖ = (1 : ℝ) := by simp [norm_inv, hw_norm]
              have hw_inv_norm' : ‖w⁻¹‖₊ = (1 : NNReal) := by
                exact NNReal.coe_injective (by simpa using hw_inv_norm)
              change (0 : ENNReal) < ‖w⁻¹‖₊ ∧ ‖w⁻¹‖₊ < (R : ENNReal)
              constructor
              · simp [hw_inv_norm']
              · have : ((1 : NNReal) : ENNReal) < (R : ENNReal) := by exact_mod_cast h1R
                simpa [hw_inv_norm'] using this
            have hw0 : w ≠ 0 :=
              exercise12_ne_zero_of_mem_sphere_zero_of_pos (by norm_num : (0 : ℝ) < 1) hw
            calc
              (1 / w) ^ n * w⁻¹ * ((w⁻¹) * ∑' m : ℤ, a m * (w⁻¹) ^ m)
                = w ^ (-(n + 2 : ℤ)) * ∑' m : ℤ, a m * (w⁻¹) ^ m := by
                    calc
                      (1 / w : ℂ) ^ n * w⁻¹ * ((w⁻¹) * ∑' m : ℤ, a m * (w⁻¹) ^ m)
                        = (1 / w : ℂ) ^ n * (w⁻¹ * (w⁻¹ * ∑' m : ℤ, a m * (w⁻¹) ^ m)) := by
                            rw [mul_assoc]
                      _ = (((1 / w : ℂ) ^ n) * (w⁻¹ * w⁻¹)) *
                            ∑' m : ℤ, a m * (w⁻¹) ^ m := by ring
                      _ = w ^ (-(n + 2 : ℤ)) * ∑' m : ℤ, a m * (w⁻¹) ^ m := by
                          congr 1
                          calc
                            ((1 / w : ℂ) ^ n) * (w⁻¹ * w⁻¹) = (w⁻¹) ^ n * (w⁻¹) ^ (2 : ℕ) := by
                              simp [one_div, pow_two]
                            _ = (w⁻¹) ^ (n + 2 : ℕ) := by rw [← pow_add]
                            _ = ((w ^ (n + 2 : ℕ)) : ℂ)⁻¹ := by rw [inv_pow]
                            _ = w ^ (Int.negSucc (n + 1)) := by rw [zpow_negSucc]
                            _ = w ^ (-(n + 2 : ℤ)) := by
                                congr 1
              _ = w ^ (-(n + 2 : ℤ)) * ∑' m : ℤ, laurentTerm a m (w⁻¹) := by
                    refine congrArg (fun s : ℂ ↦ w ^ (-(n + 2 : ℤ)) * s) ?_
                    refine tsum_congr ?_
                    intro m
                    simp [laurentTerm]
              _ = ∑' m : ℤ, w ^ (-(n + 2 : ℤ)) * laurentTerm a m (w⁻¹) := by
                    rw [tsum_mul_left]
    _ = ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
          ∑' m : ℤ, ∮ w in C(0, 1), w ^ (-(n + 2 : ℤ)) * laurentTerm a m (w⁻¹) := by
            rw [hsumCircle]
    _ = ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
          ∑' m : ℤ,
            if m = Int.negSucc n then (2 * Real.pi * Complex.I : ℂ) * a (Int.negSucc n) else 0 := by
            refine congrArg (fun s : ℂ ↦ ((2 * Real.pi * Complex.I : ℂ)⁻¹) * s) ?_
            refine tsum_congr ?_
            intro m
            exact hterm m
    _ = ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
          ((2 * Real.pi * Complex.I : ℂ) * a (Int.negSucc n)) := by
          rw [tsum_ite_eq]
    _ = a (Int.negSucc n) := by
          have htwo_pi_i_ne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
            simp [Real.pi_ne_zero]
          rw [← mul_assoc, inv_mul_cancel₀ htwo_pi_i_ne, one_mul]

/-- Helper for Exercise 12: inversion preserves the unit circle. -/
lemma exercise12_inv_mem_unit_sphere {w : ℂ} (hw : w ∈ sphere (0 : ℂ) 1) :
    w⁻¹ ∈ sphere (0 : ℂ) 1 := by
  -- Taking norms after inversion keeps radius `1` fixed.
  have hw_norm : ‖w‖ = (1 : ℝ) := by
    simpa using mem_sphere_iff_norm.mp hw
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_inv, hw_norm]
  norm_num

/-- Helper for Exercise 12: when `1 < R`, every point of the unit circle lies in the annulus
`0 < |w| < R`. -/
lemma exercise12_mem_annulus_of_mem_unit_sphere
    {R : NNReal} (h1R : (1 : NNReal) < R) {w : ℂ} (hw : w ∈ sphere (0 : ℂ) 1) :
    w ∈ complexOpenAnnulus 0 R := by
  -- The radius-`1` circle is the intermediate Cauchy circle inside the chosen annulus.
  have hw_norm : ‖w‖₊ = (1 : NNReal) := by
    exact NNReal.coe_injective <| by simpa using mem_sphere_iff_norm.mp hw
  change (0 : ENNReal) < ‖w‖₊ ∧ ‖w‖₊ < (R : ENNReal)
  constructor
  · simp [hw_norm]
  · simpa [hw_norm] using (show ((1 : NNReal) : ENNReal) < (R : ENNReal) by exact_mod_cast h1R)

/-- Helper for Exercise 12: on the reciprocal-symmetric kernel
`exp (x (w + w⁻¹) / 2)`, the negative Laurent coefficient equals the matching positive one. -/
lemma exercise12_modified_reciprocal_coeff_relation
    {R : NNReal} {a : ℤ → ℂ} {x : ℂ}
    (ha : IsLaurentSeriesOnAnnulus a 0 R) (h1R : (1 : NNReal) < R)
    (hEq : Set.EqOn (fun w ↦ Complex.exp (x * (w + w⁻¹) / 2))
      (fun w ↦ ∑' m : ℤ, a m * w ^ m) (complexOpenAnnulus 0 R))
    (n : ℕ) :
    a (Int.negSucc n) = a ((n + 1 : ℕ) : ℤ) := by
  calc
    a (Int.negSucc n)
      = ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
          ∮ w in C(0, 1),
            (1 / w) ^ n * w⁻¹ * ((w⁻¹) * ∑' m : ℤ, a m * (w⁻¹) ^ m) := by
              symm
              exact exercise12_laurent_neg_coeff_eq_unit_circle_reciprocal_coeff ha h1R n
    _ = ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
          ∮ w in C(0, 1), (∑' m : ℤ, a m * w ^ m) / w ^ (n + 2) := by
            refine congrArg (fun s : ℂ ↦ ((2 * Real.pi * Complex.I : ℂ)⁻¹) * s) ?_
            refine circleIntegral.integral_congr (by norm_num : (0 : ℝ) ≤ 1) ?_
            intro w hw
            have hwAnn : w ∈ complexOpenAnnulus 0 R :=
              exercise12_mem_annulus_of_mem_unit_sphere h1R hw
            have hwInvAnn : w⁻¹ ∈ complexOpenAnnulus 0 R :=
              exercise12_mem_annulus_of_mem_unit_sphere h1R (exercise12_inv_mem_unit_sphere hw)
            calc
              (1 / w) ^ n * w⁻¹ * ((w⁻¹) * ∑' m : ℤ, a m * (w⁻¹) ^ m)
                = (1 / w) ^ n * w⁻¹ *
                    ((w⁻¹) * Complex.exp (x * (w + w⁻¹) / 2)) := by
                      congr 2
                      calc
                        ∑' m : ℤ, a m * (w⁻¹) ^ m
                          = Complex.exp (x * (w⁻¹ + (w⁻¹)⁻¹) / 2) := by
                              symm
                              exact hEq hwInvAnn
                        _ = Complex.exp (x * (w + w⁻¹) / 2) := by simp [add_comm]
              _ = Complex.exp (x * (w + w⁻¹) / 2) / w ^ (n + 2) := by
                    calc
                      (1 / w) ^ n * w⁻¹ * ((w⁻¹) * Complex.exp (x * (w + w⁻¹) / 2))
                        = Complex.exp (x * (w + w⁻¹) / 2) *
                            ((1 / w) ^ n * (w⁻¹ * w⁻¹)) := by ring
                      _ = Complex.exp (x * (w + w⁻¹) / 2) *
                            ((w⁻¹) ^ n * (w⁻¹) ^ (2 : ℕ)) := by
                              simp [one_div, pow_two]
                      _ = Complex.exp (x * (w + w⁻¹) / 2) * (w⁻¹) ^ (n + 2) := by
                              rw [← pow_add]
                      _ = Complex.exp (x * (w + w⁻¹) / 2) * (w ^ (n + 2 : ℕ))⁻¹ := by
                              rw [inv_pow]
                      _ = Complex.exp (x * (w + w⁻¹) / 2) / w ^ (n + 2) := by
                              rfl
              _ = (∑' m : ℤ, a m * w ^ m) / w ^ (n + 2) := by
                    simpa using congrArg (fun u : ℂ ↦ u / w ^ (n + 2)) (hEq hwAnn)
    _ = a ((n + 1 : ℕ) : ℤ) := by
          exact exercise12_laurent_nonneg_coeff_eq_unit_circle_coeff ha h1R (n + 1)

/-- Helper for Exercise 12: negating the argument turns the Bessel kernel into the Laurent series
with coefficients multiplied by `(-1)^m`. -/
lemma exercise12_negated_bessel_annulus_eqOn
    {R : NNReal} {a : ℤ → ℂ} {x : ℂ}
    (hEq : Set.EqOn (fun w ↦ Complex.exp (x * (w - w⁻¹) / 2))
      (fun w ↦ ∑' m : ℤ, a m * w ^ m) (complexOpenAnnulus 0 R)) :
    Set.EqOn (fun w ↦ Complex.exp (-x * (w - w⁻¹) / 2))
      (fun w ↦ ∑' m : ℤ, ((-1 : ℂ) ^ m * a m) * w ^ m) (complexOpenAnnulus 0 R) := by
  intro w hw
  have hnegw : -w ∈ complexOpenAnnulus 0 R := by
    simpa [complexOpenAnnulus] using hw
  calc
    Complex.exp (-x * (w - w⁻¹) / 2)
      = Complex.exp (x * (-w - (-w)⁻¹) / 2) := by
          congr 1
          ring_nf
    _ = ∑' m : ℤ, a m * (-w) ^ m := hEq hnegw
    _ = ∑' m : ℤ, ((-1 : ℂ) ^ m * a m) * w ^ m := by
          refine tsum_congr ?_
          intro m
          calc
            a m * (-w) ^ m = a m * (((-1 : ℂ) * w) ^ m) := by simp
            _ = a m * (((-1 : ℂ) ^ m) * w ^ m) := by rw [mul_zpow]
            _ = ((-1 : ℂ) ^ m * a m) * w ^ m := by ring

/-- Helper for Exercise 12: for the Bessel kernel, the negative Laurent coefficient differs from
the positive one by the source sign factor `(-1)^(n+1)`. -/
lemma exercise12_bessel_reciprocal_coeff_relation
    {R : NNReal} {a : ℤ → ℂ} {x : ℂ}
    (ha : IsLaurentSeriesOnAnnulus a 0 R) (h1R : (1 : NNReal) < R)
    (hEq : Set.EqOn (fun w ↦ Complex.exp (x * (w - w⁻¹) / 2))
      (fun w ↦ ∑' m : ℤ, a m * w ^ m) (complexOpenAnnulus 0 R))
    (n : ℕ) :
    a (Int.negSucc n) = (-1 : ℂ) ^ (n + 1) * a ((n + 1 : ℕ) : ℤ) := by
  let b : ℤ → ℂ := fun m ↦ (-1 : ℂ) ^ m * a m
  have hb : IsLaurentSeriesOnAnnulus b 0 R :=
    exercise12_neg_laurentSeriesOnAnnulus (ρ := R) ha
  have hEqNeg :
      Set.EqOn (fun w ↦ Complex.exp (-x * (w - w⁻¹) / 2))
        (fun w ↦ ∑' m : ℤ, b m * w ^ m) (complexOpenAnnulus 0 R) := by
    simpa [b] using exercise12_negated_bessel_annulus_eqOn (R := R) (a := a) (x := x) hEq
  calc
    a (Int.negSucc n)
      = ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
          ∮ w in C(0, 1),
            (1 / w) ^ n * w⁻¹ * ((w⁻¹) * ∑' m : ℤ, a m * (w⁻¹) ^ m) := by
              symm
              exact exercise12_laurent_neg_coeff_eq_unit_circle_reciprocal_coeff ha h1R n
    _ = ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
          ∮ w in C(0, 1), (∑' m : ℤ, b m * w ^ m) / w ^ (n + 2) := by
            refine congrArg (fun s : ℂ ↦ ((2 * Real.pi * Complex.I : ℂ)⁻¹) * s) ?_
            refine circleIntegral.integral_congr (by norm_num : (0 : ℝ) ≤ 1) ?_
            intro w hw
            have hwInvAnn : w⁻¹ ∈ complexOpenAnnulus 0 R :=
              exercise12_mem_annulus_of_mem_unit_sphere h1R (exercise12_inv_mem_unit_sphere hw)
            have hwAnn : w ∈ complexOpenAnnulus 0 R :=
              exercise12_mem_annulus_of_mem_unit_sphere h1R hw
            calc
              (1 / w) ^ n * w⁻¹ * ((w⁻¹) * ∑' m : ℤ, a m * (w⁻¹) ^ m)
                = (1 / w) ^ n * w⁻¹ *
                    ((w⁻¹) * Complex.exp (-x * (w - w⁻¹) / 2)) := by
                      congr 2
                      calc
                        ∑' m : ℤ, a m * (w⁻¹) ^ m
                          = Complex.exp (x * (w⁻¹ - (w⁻¹)⁻¹) / 2) := by
                              symm
                              exact hEq hwInvAnn
                        _ = Complex.exp (-x * (w - w⁻¹) / 2) := by
                              congr 1
                              simp [sub_eq_add_neg, div_eq_mul_inv, inv_inv]
                              ring_nf
              _ = Complex.exp (-x * (w - w⁻¹) / 2) / w ^ (n + 2) := by
                    calc
                      (1 / w) ^ n * w⁻¹ * ((w⁻¹) * Complex.exp (-x * (w - w⁻¹) / 2))
                        = Complex.exp (-x * (w - w⁻¹) / 2) *
                            ((1 / w) ^ n * (w⁻¹ * w⁻¹)) := by ring
                      _ = Complex.exp (-x * (w - w⁻¹) / 2) *
                            ((w⁻¹) ^ n * (w⁻¹) ^ (2 : ℕ)) := by
                              simp [one_div, pow_two]
                      _ = Complex.exp (-x * (w - w⁻¹) / 2) * (w⁻¹) ^ (n + 2) := by
                              rw [← pow_add]
                      _ = Complex.exp (-x * (w - w⁻¹) / 2) * (w ^ (n + 2 : ℕ))⁻¹ := by
                              rw [inv_pow]
                      _ = Complex.exp (-x * (w - w⁻¹) / 2) / w ^ (n + 2) := by
                              rfl
              _ = (∑' m : ℤ, b m * w ^ m) / w ^ (n + 2) := by
                    simpa using congrArg (fun u : ℂ ↦ u / w ^ (n + 2)) (hEqNeg hwAnn)
    _ = b ((n + 1 : ℕ) : ℤ) := by
          exact exercise12_laurent_nonneg_coeff_eq_unit_circle_coeff hb h1R (n + 1)
    _ = (-1 : ℂ) ^ (n + 1) * a ((n + 1 : ℕ) : ℤ) := by
          dsimp [b]
          have hcast : ((n : ℤ) + 1) = (((n + 1 : ℕ) : ℤ)) := by norm_num
          rw [hcast, zpow_natCast]

/-- Exercise 12 (1): on the punctured plane, the Laurent expansion of
`exp (x (z + z⁻¹) / 2)` is expressed by the modified Bessel functions `I_n(x)`. -/
theorem exercise12_modified_bessel_generating_function
    (x z : ℂ) (hz : z ≠ 0) :
    Complex.exp (x * (z + z⁻¹) / 2) =
      I_[0] x +
        ∑' n : ℕ,
          I_[n + 1] x *
            (z ^ (((n + 1 : ℕ) : ℤ)) + z ^ (-(((n + 1 : ℕ) : ℤ)))) := by
  let R : NNReal := max 2 (‖z‖₊ + 1)
  have h1R : (1 : NNReal) < R := by
    dsimp [R]
    calc
      (1 : NNReal) < 2 := by norm_num
      _ ≤ max 2 (‖z‖₊ + 1) := le_max_left _ _
  have hzAnn : z ∈ complexOpenAnnulus 0 R := by
    change (0 : ENNReal) < ‖z‖₊ ∧ ‖z‖₊ < (R : ENNReal)
    have hzltR : ‖z‖₊ < R := by
      dsimp [R]
      exact lt_of_lt_of_le (lt_add_of_pos_right ‖z‖₊ zero_lt_one) (le_max_right _ _)
    constructor
    · exact_mod_cast norm_pos_iff.mpr hz
    · exact_mod_cast hzltR
  have hanalytic :
      AnalyticOnNhd ℂ (fun w : ℂ ↦ Complex.exp (x * (w + w⁻¹) / 2))
        (complexOpenAnnulus 0 R) := by
    intro w hw
    have hw0 : w ≠ 0 := exercise12_ne_zero_of_mem_complexOpenAnnulus_zero hw
    simpa using
      (show AnalyticAt ℂ (fun u : ℂ ↦ Complex.exp (x * (u + u⁻¹) / 2)) w by
        fun_prop)
  rcases hanalytic.hasLaurentExpansionOnAnnulus with ⟨a, ha, hEq⟩
  have hcoeff_nonneg (m : ℕ) : a (m : ℤ) = I_[m] x := by
    calc
      a (m : ℤ)
        = ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
            ∮ w in C(0, 1), (∑' k : ℤ, a k * w ^ k) / w ^ (m + 1) := by
              symm
              exact exercise12_laurent_nonneg_coeff_eq_unit_circle_coeff ha h1R m
      _ = ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
            ∮ w in C(0, 1), Complex.exp (x * (w + w⁻¹) / 2) / w ^ (m + 1) := by
              refine congrArg (fun s : ℂ ↦ ((2 * Real.pi * Complex.I : ℂ)⁻¹) * s) ?_
              refine circleIntegral.integral_congr (by norm_num : (0 : ℝ) ≤ 1) ?_
              intro w hw
              have hwAnn : w ∈ complexOpenAnnulus 0 R :=
                exercise12_mem_annulus_of_mem_unit_sphere h1R hw
              simpa using (congrArg (fun u : ℂ ↦ u / w ^ (m + 1)) (hEq hwAnn)).symm
      _ = I_[m] x := by
            symm
            exact modifiedBesselI_eq_unit_circle_coeff m x
  have hcoeff_neg (m : ℕ) : a (Int.negSucc m) = I_[m + 1] x := by
    rw [exercise12_modified_reciprocal_coeff_relation ha h1R hEq]
    exact hcoeff_nonneg (m + 1)
  have hsplit :
      Complex.exp (x * (z + z⁻¹) / 2) =
        (∑' n : ℕ, a (n : ℤ) * z ^ n) + ∑' n : ℕ, a (Int.negSucc n) * z ^ (Int.negSucc n) := by
    calc
      Complex.exp (x * (z + z⁻¹) / 2) = ∑' m : ℤ, a m * z ^ m := hEq hzAnn
      _ = (∑' n : ℕ, a (n : ℤ) * z ^ n) + ∑' n : ℕ, a (Int.negSucc n) * z ^ (Int.negSucc n) := by
            simpa using
              (laurent_split_eqOn_annulus (a := a) (ρ₂ := 0) (ρ₁ := R)
                (f := fun w ↦ ∑' m : ℤ, a m * w ^ m) ha (by
                  intro w hw
                  rfl) hzAnn)
  have hnonneg_tail_summable :
      Summable (fun n : ℕ ↦ I_[n + 1] x * z ^ (((n + 1 : ℕ) : ℤ))) := by
    let source : ℕ → ℂ := fun n ↦ a (n : ℤ) * z ^ n
    have hsource : Summable source := by
      simpa [source] using laurent_nonneg_part_summable ha hzAnn
    have htail : Summable (fun n : ℕ ↦ source (n + 1)) := by
      simpa [source] using hsource.comp_injective Nat.succ_injective
    refine htail.congr ?_
    intro n
    rw [show source (n + 1) = a ((n + 1 : ℕ) : ℤ) * z ^ (n + 1) by rfl]
    rw [hcoeff_nonneg (n + 1), ← zpow_natCast]
  have hneg_summable :
      Summable (fun n : ℕ ↦ I_[n + 1] x * z ^ (-(((n + 1 : ℕ) : ℤ)))) := by
    refine (laurent_neg_part_summable ha hzAnn).congr ?_
    intro n
    rw [hcoeff_neg n]
    simp [Int.negSucc_eq]
  have hnonneg :
      (∑' n : ℕ, a (n : ℤ) * z ^ n) =
        I_[0] x + ∑' n : ℕ, I_[n + 1] x * z ^ (((n + 1 : ℕ) : ℤ)) := by
    calc
      (∑' n : ℕ, a (n : ℤ) * z ^ n)
        = a (0 : ℤ) * z ^ (0 : ℕ) + ∑' n : ℕ, a ((n + 1 : ℕ) : ℤ) * z ^ (n + 1) := by
            simpa using ((laurent_nonneg_part_summable ha hzAnn).sum_add_tsum_nat_add 1).symm
      _ = I_[0] x + ∑' n : ℕ, I_[n + 1] x * z ^ (((n + 1 : ℕ) : ℤ)) := by
            have h0 : a (0 : ℤ) = I_[0] x := by simpa using hcoeff_nonneg 0
            rw [h0]
            simp only [pow_zero, mul_one, Nat.cast_add, Nat.cast_one, add_right_inj]
            exact tsum_congr (fun n : ℕ ↦ by
              rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by omega]
              rw [hcoeff_nonneg (n + 1), ← zpow_natCast])
  have hneg :
      (∑' n : ℕ, a (Int.negSucc n) * z ^ (Int.negSucc n)) =
        ∑' n : ℕ, I_[n + 1] x * z ^ (-(((n + 1 : ℕ) : ℤ))) := by
    refine tsum_congr ?_
    intro n
    rw [hcoeff_neg n]
    simp [Int.negSucc_eq]
  calc
    Complex.exp (x * (z + z⁻¹) / 2)
      = (∑' n : ℕ, a (n : ℤ) * z ^ n) + ∑' n : ℕ, a (Int.negSucc n) * z ^ (Int.negSucc n) :=
          hsplit
    _ = (I_[0] x + ∑' n : ℕ, I_[n + 1] x * z ^ (((n + 1 : ℕ) : ℤ))) +
          ∑' n : ℕ, I_[n + 1] x * z ^ (-(((n + 1 : ℕ) : ℤ))) := by
            rw [hnonneg, hneg]
    _ = I_[0] x +
          ((∑' n : ℕ, I_[n + 1] x * z ^ (((n + 1 : ℕ) : ℤ))) +
            ∑' n : ℕ, I_[n + 1] x * z ^ (-(((n + 1 : ℕ) : ℤ)))) := by
            ring
    _ = I_[0] x +
          ∑' n : ℕ,
            (I_[n + 1] x * z ^ (((n + 1 : ℕ) : ℤ)) +
              I_[n + 1] x * z ^ (-(((n + 1 : ℕ) : ℤ)))) := by
            exact
              congrArg (fun s : ℂ ↦ I_[0] x + s)
                (hnonneg_tail_summable.tsum_add hneg_summable).symm
    _ = I_[0] x +
          ∑' n : ℕ,
            I_[n + 1] x *
              (z ^ (((n + 1 : ℕ) : ℤ)) + z ^ (-(((n + 1 : ℕ) : ℤ)))) := by
            congr 1
            refine tsum_congr ?_
            intro n
            rw [mul_add]

/-- Exercise 12 (2): on the punctured plane, the Laurent expansion of
`exp (x (z - z⁻¹) / 2)` is expressed by the Bessel functions `J_n(x)`. -/
theorem exercise12_bessel_generating_function
    (x z : ℂ) (hz : z ≠ 0) :
    Complex.exp (x * (z - z⁻¹) / 2) =
      J_[0] x +
        ∑' n : ℕ,
          J_[n + 1] x *
            (z ^ (((n + 1 : ℕ) : ℤ)) +
              (-1 : ℂ) ^ (n + 1) * z ^ (-(((n + 1 : ℕ) : ℤ)))) := by
  let R : NNReal := max 2 (‖z‖₊ + 1)
  have h1R : (1 : NNReal) < R := by
    dsimp [R]
    calc
      (1 : NNReal) < 2 := by norm_num
      _ ≤ max 2 (‖z‖₊ + 1) := le_max_left _ _
  have hzAnn : z ∈ complexOpenAnnulus 0 R := by
    change (0 : ENNReal) < ‖z‖₊ ∧ ‖z‖₊ < (R : ENNReal)
    have hzltR : ‖z‖₊ < R := by
      dsimp [R]
      exact lt_of_lt_of_le (lt_add_of_pos_right ‖z‖₊ zero_lt_one) (le_max_right _ _)
    constructor
    · exact_mod_cast norm_pos_iff.mpr hz
    · exact_mod_cast hzltR
  have hanalytic :
      AnalyticOnNhd ℂ (fun w : ℂ ↦ Complex.exp (x * (w - w⁻¹) / 2))
        (complexOpenAnnulus 0 R) := by
    intro w hw
    have hw0 : w ≠ 0 := exercise12_ne_zero_of_mem_complexOpenAnnulus_zero hw
    simpa using
      (show AnalyticAt ℂ (fun u : ℂ ↦ Complex.exp (x * (u - u⁻¹) / 2)) w by
        fun_prop)
  rcases hanalytic.hasLaurentExpansionOnAnnulus with ⟨a, ha, hEq⟩
  have hcoeff_nonneg (m : ℕ) : a (m : ℤ) = J_[m] x := by
    calc
      a (m : ℤ)
        = ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
            ∮ w in C(0, 1), (∑' k : ℤ, a k * w ^ k) / w ^ (m + 1) := by
              symm
              exact exercise12_laurent_nonneg_coeff_eq_unit_circle_coeff ha h1R m
      _ = ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
            ∮ w in C(0, 1), Complex.exp (x * (w - w⁻¹) / 2) / w ^ (m + 1) := by
              refine congrArg (fun s : ℂ ↦ ((2 * Real.pi * Complex.I : ℂ)⁻¹) * s) ?_
              refine circleIntegral.integral_congr (by norm_num : (0 : ℝ) ≤ 1) ?_
              intro w hw
              have hwAnn : w ∈ complexOpenAnnulus 0 R :=
                exercise12_mem_annulus_of_mem_unit_sphere h1R hw
              simpa using (congrArg (fun u : ℂ ↦ u / w ^ (m + 1)) (hEq hwAnn)).symm
      _ = J_[m] x := by
            symm
            exact besselJ_eq_unit_circle_coeff m x
  have hcoeff_neg (m : ℕ) :
      a (Int.negSucc m) = (-1 : ℂ) ^ (m + 1) * J_[m + 1] x := by
    rw [exercise12_bessel_reciprocal_coeff_relation ha h1R hEq]
    rw [hcoeff_nonneg (m + 1)]
  have hsplit :
      Complex.exp (x * (z - z⁻¹) / 2) =
        (∑' n : ℕ, a (n : ℤ) * z ^ n) + ∑' n : ℕ, a (Int.negSucc n) * z ^ (Int.negSucc n) := by
    calc
      Complex.exp (x * (z - z⁻¹) / 2) = ∑' m : ℤ, a m * z ^ m := hEq hzAnn
      _ = (∑' n : ℕ, a (n : ℤ) * z ^ n) + ∑' n : ℕ, a (Int.negSucc n) * z ^ (Int.negSucc n) := by
            simpa using
              (laurent_split_eqOn_annulus (a := a) (ρ₂ := 0) (ρ₁ := R)
                (f := fun w ↦ ∑' m : ℤ, a m * w ^ m) ha (by
                  intro w hw
                  rfl) hzAnn)
  have hnonneg_tail_summable :
      Summable (fun n : ℕ ↦ J_[n + 1] x * z ^ (((n + 1 : ℕ) : ℤ))) := by
    let source : ℕ → ℂ := fun n ↦ a (n : ℤ) * z ^ n
    have hsource : Summable source := by
      simpa [source] using laurent_nonneg_part_summable ha hzAnn
    have htail : Summable (fun n : ℕ ↦ source (n + 1)) := by
      simpa [source] using hsource.comp_injective Nat.succ_injective
    refine htail.congr ?_
    intro n
    rw [show source (n + 1) = a ((n + 1 : ℕ) : ℤ) * z ^ (n + 1) by rfl]
    rw [hcoeff_nonneg (n + 1), ← zpow_natCast]
  have hneg_summable :
      Summable (fun n : ℕ ↦ J_[n + 1] x * (((-1 : ℂ) ^ (n + 1)) * z ^ (-(((n + 1 : ℕ) : ℤ))))) := by
    refine (laurent_neg_part_summable ha hzAnn).congr ?_
    intro n
    rw [hcoeff_neg n]
    simp [Int.negSucc_eq, mul_left_comm, mul_comm]
  have hnonneg :
      (∑' n : ℕ, a (n : ℤ) * z ^ n) =
        J_[0] x + ∑' n : ℕ, J_[n + 1] x * z ^ (((n + 1 : ℕ) : ℤ)) := by
    calc
      (∑' n : ℕ, a (n : ℤ) * z ^ n)
        = a (0 : ℤ) * z ^ (0 : ℕ) + ∑' n : ℕ, a ((n + 1 : ℕ) : ℤ) * z ^ (n + 1) := by
            simpa using ((laurent_nonneg_part_summable ha hzAnn).sum_add_tsum_nat_add 1).symm
      _ = J_[0] x + ∑' n : ℕ, J_[n + 1] x * z ^ (((n + 1 : ℕ) : ℤ)) := by
            have h0 : a (0 : ℤ) = J_[0] x := by simpa using hcoeff_nonneg 0
            rw [h0]
            simp only [pow_zero, mul_one, Nat.cast_add, Nat.cast_one, add_right_inj]
            exact tsum_congr (fun n : ℕ ↦ by
              rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by omega]
              rw [hcoeff_nonneg (n + 1), ← zpow_natCast])
  have hneg :
      (∑' n : ℕ, a (Int.negSucc n) * z ^ (Int.negSucc n)) =
        ∑' n : ℕ, J_[n + 1] x * (((-1 : ℂ) ^ (n + 1)) * z ^ (-(((n + 1 : ℕ) : ℤ)))) := by
    refine tsum_congr ?_
    intro n
    rw [hcoeff_neg n]
    simp [Int.negSucc_eq, mul_left_comm, mul_comm]
  calc
    Complex.exp (x * (z - z⁻¹) / 2)
      = (∑' n : ℕ, a (n : ℤ) * z ^ n) + ∑' n : ℕ, a (Int.negSucc n) * z ^ (Int.negSucc n) :=
          hsplit
    _ = (J_[0] x + ∑' n : ℕ, J_[n + 1] x * z ^ (((n + 1 : ℕ) : ℤ))) +
          ∑' n : ℕ, J_[n + 1] x * (((-1 : ℂ) ^ (n + 1)) * z ^ (-(((n + 1 : ℕ) : ℤ)))) := by
            rw [hnonneg, hneg]
    _ = J_[0] x +
          ((∑' n : ℕ, J_[n + 1] x * z ^ (((n + 1 : ℕ) : ℤ))) +
            ∑' n : ℕ, J_[n + 1] x * (((-1 : ℂ) ^ (n + 1)) * z ^ (-(((n + 1 : ℕ) : ℤ))))) := by
            ring
    _ = J_[0] x +
          ∑' n : ℕ,
            (J_[n + 1] x * z ^ (((n + 1 : ℕ) : ℤ)) +
              J_[n + 1] x * (((-1 : ℂ) ^ (n + 1)) * z ^ (-(((n + 1 : ℕ) : ℤ))))) := by
            exact
              congrArg (fun s : ℂ ↦ J_[0] x + s)
                (hnonneg_tail_summable.tsum_add hneg_summable).symm
    _ = J_[0] x +
          ∑' n : ℕ,
            J_[n + 1] x *
              (z ^ (((n + 1 : ℕ) : ℤ)) +
                (-1 : ℂ) ^ (n + 1) * z ^ (-(((n + 1 : ℕ) : ℤ)))) := by
            congr 1
            refine tsum_congr ?_
            intro n
            rw [mul_add]

/-- Exercise 12 (3): the unit-circle coefficient extraction for `(z^2 + ε)^m / z^(m+n+1)` in the
matching-parity case, with the canonical `dz`-normalization by `2 π i`. -/
theorem exercise12_circle_integral_binomial_coeff
    (ε : ℂ) (m n p : ℕ) (h : m = n + 2 * p) :
    ((2 * Real.pi * Complex.I : ℂ)⁻¹) * ∮ z in C(0, 1), ((z ^ 2 + ε) ^ m) / z ^ (m + n + 1) =
      ε ^ p * (Nat.factorial (n + 2 * p) : ℂ) /
        ((Nat.factorial p : ℂ) * (Nat.factorial (n + p) : ℂ)) := by
  subst h
  -- Route correction: compute the normalized contour integral by a finite Laurent expansion and
  -- isolate the unique `z⁻¹` summand rather than trying to evaluate the quotient directly.
  let q : ℕ := n + 2 * p
  let term : ℕ → ℂ → ℂ := fun k z ↦
    ((Nat.choose q k : ℂ) * ε ^ (q - k)) *
      z ^ (((2 * k : ℕ) : ℤ) - ((q + n + 1 : ℕ) : ℤ))
  let sumTerm : ℂ → ℂ := fun z ↦ ∑ k ∈ Finset.range (q + 1), term k z
  have hrewrite :
      ((2 * Real.pi * Complex.I : ℂ)⁻¹) * ∮ z in C(0, 1), ((z ^ 2 + ε) ^ q) / z ^ (q + n + 1) =
        ((2 * Real.pi * Complex.I : ℂ)⁻¹) * ∮ z in C(0, 1), sumTerm z := by
    -- First rewrite the quotient as a finite Laurent sum on the unit circle.
    refine congrArg (fun w : ℂ ↦ ((2 * Real.pi * Complex.I : ℂ)⁻¹) * w) ?_
    refine circleIntegral.integral_congr (by norm_num : (0 : ℝ) ≤ 1) ?_
    intro z hz
    exact exercise12_binomial_div_eq_laurent_sum ε z (exercise12_ne_zero_of_mem_unit_sphere hz) q n
  have hsum :
      ((2 * Real.pi * Complex.I : ℂ)⁻¹) * ∮ z in C(0, 1), sumTerm z =
        ∑ k ∈ Finset.range (q + 1),
          ((2 * Real.pi * Complex.I : ℂ)⁻¹) * ∮ z in C(0, 1), term k z := by
    -- Circle integration commutes with the finite Laurent sum term-by-term.
    change ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
        (∮ z in C(0, 1), ∑ k ∈ Finset.range (q + 1), term k z) =
      ∑ k ∈ Finset.range (q + 1),
        ((2 * Real.pi * Complex.I : ℂ)⁻¹) * ∮ z in C(0, 1), term k z
    rw [circleIntegral.integral_fun_sum]
    · rw [Finset.mul_sum]
    · intro k hk
      exact exercise12_circleIntegrable_const_mul_zpow _ _
  have hterm :
      ∀ k ∈ Finset.range (q + 1),
        ((2 * Real.pi * Complex.I : ℂ)⁻¹) * ∮ z in C(0, 1), term k z =
          if k = n + p then (Nat.choose q k : ℂ) * ε ^ (q - k) else 0 := by
    intro k hk
    -- The residue survives exactly when the Laurent exponent equals `-1`, i.e. `k = n + p`.
    have hk_exp :
        (((2 * k : ℕ) : ℤ) - ((q + n + 1 : ℕ) : ℤ)) = -1 ↔ k = n + p := by
      constructor
      · intro hres
        dsimp [q] at hres
        omega
      · intro hk_eq
        subst hk_eq
        dsimp [q]
        omega
    rw [exercise12_normalized_circleIntegral_const_mul_zpow]
    by_cases hk_eq : k = n + p
    · rw [if_pos hk_eq, if_pos (hk_exp.mpr hk_eq)]
    · rw [if_neg hk_eq]
      have hneq_exp : (((2 * k : ℕ) : ℤ) - ((q + n + 1 : ℕ) : ℤ)) ≠ -1 := by
        intro hres
        exact hk_eq (hk_exp.mp hres)
      rw [if_neg hneq_exp]
  calc
    ((2 * Real.pi * Complex.I : ℂ)⁻¹) * ∮ z in C(0, 1), ((z ^ 2 + ε) ^ q) / z ^ (q + n + 1)
      = ∑ k ∈ Finset.range (q + 1),
          ((2 * Real.pi * Complex.I : ℂ)⁻¹) * ∮ z in C(0, 1), term k z := by
            rw [hrewrite, hsum]
    _ = (Nat.choose q (n + p) : ℂ) * ε ^ (q - (n + p)) := by
          -- Only the unique residue index `k = n + p` contributes to the finite sum.
          rw [Finset.sum_eq_single (n + p)]
          · rw [hterm _ (by
              dsimp [q]
              simp
              omega)]
            simp
          · intro k hk hkne
            rw [hterm k hk, if_neg hkne]
          · intro hnotmem
            exfalso
            apply hnotmem
            dsimp [q]
            simp
            omega
    _ = ε ^ p * (Nat.factorial (n + 2 * p) : ℂ) /
          ((Nat.factorial p : ℂ) * (Nat.factorial (n + p) : ℂ)) := by
          -- The surviving coefficient is the binomial coefficient `choose (n+2p) (n+p)`.
          dsimp [q]
          have hle : n + p ≤ n + 2 * p := by omega
          have hsub : n + 2 * p - (n + p) = p := by omega
          have hchoose :
              (Nat.choose (n + 2 * p) (n + p) : ℂ) =
                (Nat.factorial (n + 2 * p) : ℂ) /
                  ((Nat.factorial (n + p) : ℂ) * (Nat.factorial p : ℂ)) := by
            simpa [hsub] using (Nat.cast_choose ℂ hle)
          rw [hchoose]
          rw [hsub]
          ring

/-- Exercise 12 (4): the same unit-circle coefficient extraction vanishes when `m - n` is not a
nonnegative even integer, again with the canonical `dz`-normalization by `2 π i`. -/
theorem exercise12_circle_integral_binomial_coeff_eq_zero
    (ε : ℂ) (m n : ℕ)
    (hmn : ∀ p : ℕ, m ≠ n + 2 * p) :
    ((2 * Real.pi * Complex.I : ℂ)⁻¹) * ∮ z in C(0, 1), ((z ^ 2 + ε) ^ m) / z ^ (m + n + 1) = 0 :=
      by
  -- Route correction: expand the quotient into Laurent monomials and show that every potential
  -- residue index would contradict the assumption that `m` is not of the form `n + 2p`.
  let term : ℕ → ℂ → ℂ := fun k z ↦
    ((Nat.choose m k : ℂ) * ε ^ (m - k)) *
      z ^ (((2 * k : ℕ) : ℤ) - ((m + n + 1 : ℕ) : ℤ))
  let sumTerm : ℂ → ℂ := fun z ↦ ∑ k ∈ Finset.range (m + 1), term k z
  have hrewrite :
      ((2 * Real.pi * Complex.I : ℂ)⁻¹) * ∮ z in C(0, 1), ((z ^ 2 + ε) ^ m) / z ^ (m + n + 1) =
        ((2 * Real.pi * Complex.I : ℂ)⁻¹) * ∮ z in C(0, 1), sumTerm z := by
    -- Rewrite the integrand as the finite Laurent expansion valid away from the origin.
    refine congrArg (fun w : ℂ ↦ ((2 * Real.pi * Complex.I : ℂ)⁻¹) * w) ?_
    refine circleIntegral.integral_congr (by norm_num : (0 : ℝ) ≤ 1) ?_
    intro z hz
    exact exercise12_binomial_div_eq_laurent_sum ε z (exercise12_ne_zero_of_mem_unit_sphere hz) m n
  have hsum :
      ((2 * Real.pi * Complex.I : ℂ)⁻¹) * ∮ z in C(0, 1), sumTerm z =
        ∑ k ∈ Finset.range (m + 1),
          ((2 * Real.pi * Complex.I : ℂ)⁻¹) * ∮ z in C(0, 1), term k z := by
    -- The finite Laurent sum is integrated termwise.
    change ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
        (∮ z in C(0, 1), ∑ k ∈ Finset.range (m + 1), term k z) =
      ∑ k ∈ Finset.range (m + 1),
        ((2 * Real.pi * Complex.I : ℂ)⁻¹) * ∮ z in C(0, 1), term k z
    rw [circleIntegral.integral_fun_sum]
    · rw [Finset.mul_sum]
    · intro k hk
      exact exercise12_circleIntegrable_const_mul_zpow _ _
  have hterm_zero :
      ∀ k ∈ Finset.range (m + 1),
        ((2 * Real.pi * Complex.I : ℂ)⁻¹) * ∮ z in C(0, 1), term k z = 0 := by
    intro k hk
    rw [exercise12_normalized_circleIntegral_const_mul_zpow]
    by_cases hres : (((2 * k : ℕ) : ℤ) - ((m + n + 1 : ℕ) : ℤ)) = -1
    · -- Any residue index would force `m = n + 2 * (m - k)`, contradicting `hmn`.
      exfalso
      have hk_le : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hm_eq : m = n + 2 * (m - k) := by
        omega
      exact hmn (m - k) hm_eq
    · rw [if_neg hres]
  calc
    ((2 * Real.pi * Complex.I : ℂ)⁻¹) * ∮ z in C(0, 1), ((z ^ 2 + ε) ^ m) / z ^ (m + n + 1)
      = ∑ k ∈ Finset.range (m + 1),
          ((2 * Real.pi * Complex.I : ℂ)⁻¹) * ∮ z in C(0, 1), term k z := by
            rw [hrewrite, hsum]
    _ = 0 := by
          refine Finset.sum_eq_zero ?_
          intro k hk
          exact hterm_zero k hk

/-- Helper for Exercise 12: on the punctured plane, the exponential contour integrand is exactly
the Taylor family obtained by expanding the exponential in the source proof and keeping the fixed
`z ^ (n + 1)` denominator outside the sum. -/
lemma exercise12_exp_binomial_family_hasSum
    (ε x z : ℂ) (n : ℕ) (hz : z ≠ 0) :
    HasSum
      (fun m : ℕ =>
        ((x / 2) ^ m / (Nat.factorial m : ℂ)) *
          (((z ^ 2 + ε) ^ m) / z ^ (m + n + 1)))
      (Complex.exp (x * (z + ε * z⁻¹) / 2) / z ^ (n + 1)) := by
  have hquot : (z ^ 2 + ε) / z = z + ε * z⁻¹ := by
    -- Collapse the punctured-plane algebra to the single quotient used in the Taylor family.
    field_simp [hz]
  have hrewrite :
      x * (z + ε * z⁻¹) / 2 = (x / 2) * ((z ^ 2 + ε) / z) := by
    -- Rewrite the phase first, then pull the scalar `1 / 2` into the left factor.
    rw [← hquot]
    ring
  -- Expand the exponential at the normalized quotient, then rewrite each term into the textbook
  -- binomial-family shape with denominator `z ^ (m + n + 1)`.
  convert
      (NormedSpace.expSeries_div_hasSum_exp ((x / 2) * ((z ^ 2 + ε) / z))).mul_right
        ((z ^ (n + 1))⁻¹) using 1
  · ext m
    simp [mul_pow, pow_add, add_assoc, div_eq_mul_inv]
    ring
  · simp [Complex.exp_eq_exp_ℂ, hrewrite, div_eq_mul_inv]

/-- Helper for Exercise 12: multiplying the `n = 0` contour Taylor family by `z` removes the
residual `1 / z`, so the governing Laurent exponent becomes exactly `2 * k - m`. -/
lemma exercise12_exp_binomial_family_hasSum_base
    (ε x z : ℂ) (hz : z ≠ 0) :
    HasSum
      (fun m : ℕ =>
        ((x / 2) ^ m / (Nat.factorial m : ℂ)) *
          (((z ^ 2 + ε) ^ m) / z ^ m))
      (Complex.exp (x * (z + ε * z⁻¹) / 2)) := by
  -- Route correction: use the already-proved `n = 0` family, then clear the final factor `z⁻¹`
  -- once so every later Laurent monomial is indexed by `2 * k - m`.
  convert (exercise12_exp_binomial_family_hasSum ε x z 0 hz).mul_left z using 1
  · ext m
    have hzpowm : z ^ m ≠ 0 := pow_ne_zero _ hz
    have hzpowm1 : z ^ (m + 1) ≠ 0 := pow_ne_zero _ hz
    -- Clear the single extra denominator factor by multiplying through with `z`.
    field_simp [hz, hzpowm, hzpowm1]
    ring_nf
  · -- The limit simplifies because `z / z = 1` away from the origin.
    field_simp [hz]
    simp

/-- Helper for Exercise 12: multiplying the normalized finite Laurent expansion by `z` rewrites the
exponent from `2 * k - (m + 1)` to the source-proof invariant `2 * k - m`. -/
lemma exercise12_binomial_div_eq_laurent_sum_base
    (ε z : ℂ) (hz : z ≠ 0) (m : ℕ) :
    ((z ^ 2 + ε) ^ m) / z ^ m =
      ∑ k ∈ Finset.range (m + 1),
        ((Nat.choose m k : ℂ) * ε ^ (m - k)) *
          z ^ (((2 * k : ℕ) : ℤ) - ((m : ℕ) : ℤ)) := by
  have hbase := exercise12_binomial_div_eq_laurent_sum ε z hz m 0
  have hmul := congrArg (fun w : ℂ ↦ z * w) hbase
  -- Multiply once by `z` to shift every Laurent monomial exponent up by one.
  calc
    ((z ^ 2 + ε) ^ m) / z ^ m
      = z * (((z ^ 2 + ε) ^ m) / z ^ (m + 1)) := by
          have hzpowm : z ^ m ≠ 0 := pow_ne_zero _ hz
          have hzpowm1 : z ^ (m + 1) ≠ 0 := pow_ne_zero _ hz
          field_simp [hz, hzpowm, hzpowm1]
          ring
    _ = z *
          (∑ k ∈ Finset.range (m + 1),
            ((Nat.choose m k : ℂ) * ε ^ (m - k)) *
              z ^ (((2 * k : ℕ) : ℤ) - ((m + 1 : ℕ) : ℤ))) := by
            simpa using hmul
    _ = ∑ k ∈ Finset.range (m + 1),
          z * (((Nat.choose m k : ℂ) * ε ^ (m - k)) *
            z ^ (((2 * k : ℕ) : ℤ) - ((m + 1 : ℕ) : ℤ))) := by
            rw [Finset.mul_sum]
    _ = ∑ k ∈ Finset.range (m + 1),
          ((Nat.choose m k : ℂ) * ε ^ (m - k)) *
            z ^ (((2 * k : ℕ) : ℤ) - ((m : ℕ) : ℤ)) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            -- Combine the outer `z` with the shifted Laurent monomial into one `zpow`.
            calc
              z * (((Nat.choose m k : ℂ) * ε ^ (m - k)) *
                  z ^ (((2 * k : ℕ) : ℤ) - ((m + 1 : ℕ) : ℤ)))
                = ((Nat.choose m k : ℂ) * ε ^ (m - k)) *
                    (z * z ^ (((2 * k : ℕ) : ℤ) - ((m + 1 : ℕ) : ℤ))) := by ring
              _ = ((Nat.choose m k : ℂ) * ε ^ (m - k)) *
                    z ^ (((2 * k : ℕ) : ℤ) - ((m : ℕ) : ℤ)) := by
                    congr 1
                    calc
                      z * z ^ (((2 * k : ℕ) : ℤ) - ((m + 1 : ℕ) : ℤ))
                        = z ^ (1 : ℤ) *
                            z ^ (((2 * k : ℕ) : ℤ) - ((m + 1 : ℕ) : ℤ)) := by simp
                      _ = z ^ ((1 : ℤ) + (((2 * k : ℕ) : ℤ) - ((m + 1 : ℕ) : ℤ))) := by
                            rw [zpow_add₀ hz]
                      _ = z ^ (((2 * k : ℕ) : ℤ) - ((m : ℕ) : ℤ)) := by
                            congr 1
                            omega

/-- Helper for Exercise 12: each Taylor/binomial summand of the signed exponential contour family
is continuous on the unit circle. -/
lemma exercise12_signed_taylor_term_continuousOn
    (ε x : ℂ) (n m : ℕ) :
    ContinuousOn
      (fun z : ℂ =>
        ((x / 2) ^ m / (Nat.factorial m : ℂ)) *
          (((z ^ 2 + ε) ^ m) / z ^ (m + n + 1)))
      (sphere (0 : ℂ) (1 : ℝ)) := by
  -- The denominator never vanishes on `|z| = 1`, so the quotient is continuous termwise.
  have hnum :
      ContinuousOn (fun z : ℂ ↦ (z ^ 2 + ε) ^ m) (sphere (0 : ℂ) (1 : ℝ)) := by
    fun_prop
  have hden :
      ContinuousOn (fun z : ℂ ↦ z ^ (m + n + 1)) (sphere (0 : ℂ) (1 : ℝ)) := by
    fun_prop
  refine continuousOn_const.mul (hnum.div hden ?_)
  intro z hz
  exact pow_ne_zero _ (exercise12_ne_zero_of_mem_unit_sphere hz)

/-- Helper for Exercise 12: on the unit circle, the signed Taylor/binomial contour summands are
uniformly dominated by the standard exponential majorant `‖x‖^m / m!`. -/
lemma exercise12_signed_taylor_term_norm_bound
    (ε x : ℂ) (n m : ℕ) (hε : ε = 1 ∨ ε = -1) :
    ∀ z ∈ sphere (0 : ℂ) (1 : ℝ),
      ‖((x / 2) ^ m / (Nat.factorial m : ℂ)) *
          (((z ^ 2 + ε) ^ m) / z ^ (m + n + 1))‖ ≤
        ‖x‖ ^ m / (Nat.factorial m : ℝ) := by
  intro z hz
  have hz_norm : ‖z‖ = (1 : ℝ) := by
    simpa using mem_sphere_iff_norm.mp hz
  have hzpow_norm : ‖z ^ (m + n + 1)‖ = (1 : ℝ) := by
    simp [norm_pow, hz_norm]
  have hzsq_norm : ‖z ^ 2‖ = (1 : ℝ) := by
    simp [norm_pow, hz_norm]
  have hε_norm : ‖ε‖ = (1 : ℝ) := by
    rcases hε with rfl | rfl <;> simp
  have hsum_bound : ‖z ^ 2 + ε‖ ≤ (2 : ℝ) := by
    calc
      ‖z ^ 2 + ε‖ ≤ ‖z ^ 2‖ + ‖ε‖ := norm_add_le _ _
      _ = (2 : ℝ) := by rw [hzsq_norm, hε_norm]; norm_num
  have hpow_bound : ‖(z ^ 2 + ε) ^ m‖ ≤ (2 : ℝ) ^ m := by
    simpa [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) hsum_bound m
  calc
    ‖((x / 2) ^ m / (Nat.factorial m : ℂ)) * (((z ^ 2 + ε) ^ m) / z ^ (m + n + 1))‖
      = ‖(x / 2) ^ m / (Nat.factorial m : ℂ)‖ *
          ‖((z ^ 2 + ε) ^ m) / z ^ (m + n + 1)‖ := by
            simp
    _ ≤ ‖(x / 2) ^ m / (Nat.factorial m : ℂ)‖ * (2 : ℝ) ^ m := by
          gcongr
          calc
            ‖((z ^ 2 + ε) ^ m) / z ^ (m + n + 1)‖
              = ‖(z ^ 2 + ε) ^ m‖ / ‖z ^ (m + n + 1)‖ := by
                  rw [norm_div]
            _ = ‖(z ^ 2 + ε) ^ m‖ := by rw [hzpow_norm, div_one]
            _ ≤ (2 : ℝ) ^ m := hpow_bound
    _ = (((‖x‖ / 2) ^ m) / (Nat.factorial m : ℝ)) * (2 : ℝ) ^ m := by
          simp [norm_pow]
    _ = (((‖x‖ / 2) ^ m) * (2 : ℝ) ^ m) / (Nat.factorial m : ℝ) := by
          rw [div_eq_mul_inv]
          ring
    _ = (((‖x‖ / 2) * 2) ^ m) / (Nat.factorial m : ℝ) := by
          rw [← mul_pow]
    _ = ‖x‖ ^ m / (Nat.factorial m : ℝ) := by
          have htwo : (2 : ℝ) ≠ 0 := by norm_num
          have hmul : (‖x‖ / 2) * 2 = ‖x‖ := by
            field_simp [htwo]
          simp [hmul]

/-- Helper for Exercise 12: the signed Taylor/binomial contour family can be integrated termwise
around the unit circle after the standard `2 π i` normalization. -/
lemma exercise12_signed_circle_integral_tsum_hasSum
    (ε x : ℂ) (n : ℕ) (hε : ε = 1 ∨ ε = -1) :
    HasSum
      (fun m : ℕ =>
        ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
          ∮ z in C(0, 1),
            ((x / 2) ^ m / (Nat.factorial m : ℂ)) *
              (((z ^ 2 + ε) ^ m) / z ^ (m + n + 1)))
      (((2 * Real.pi * Complex.I : ℂ)⁻¹) *
        ∮ z in C(0, 1),
          ∑' m : ℕ,
            ((x / 2) ^ m / (Nat.factorial m : ℂ)) *
              (((z ^ 2 + ε) ^ m) / z ^ (m + n + 1))) := by
  let F : ℕ → ℂ → ℂ := fun m z ↦
    ((x / 2) ^ m / (Nat.factorial m : ℂ)) *
      (((z ^ 2 + ε) ^ m) / z ^ (m + n + 1))
  let u : ℕ → ℝ := fun m ↦ ‖x‖ ^ m / (Nat.factorial m : ℝ)
  have hu : Summable u := by
    simpa [u] using Real.summable_pow_div_factorial ‖x‖
  have hsum_uniform :
      SummableUniformlyOn F (sphere (0 : ℂ) (1 : ℝ)) := by
    -- The unit-circle majorant is the usual exponential majorant, so the contour family is
    -- uniformly summable there.
    exact
      (HasSumUniformlyOn.of_norm_le_summable hu
        (fun m z hz ↦ by
          simpa [F, u] using
            exercise12_signed_taylor_term_norm_bound ε x n m hε z hz)).summableUniformlyOn
  have hcont :
      ∀ m, ContinuousOn (F m) (sphere (0 : ℂ) (1 : ℝ)) := by
    -- Each fixed Taylor/binomial summand is continuous on the unit circle.
    intro m
    simpa [F] using exercise12_signed_taylor_term_continuousOn ε x n m
  have hsum_int :
      HasSum (fun m : ℕ ↦ ∮ z in C(0, 1), F m z)
        (∮ z in C(0, 1), ∑' m : ℕ, F m z) := by
    -- Uniform convergence allows termwise circle integration.
    rw [HasSum]
    convert
      (hsum_uniform.hasSumUniformlyOn.tendstoUniformlyOn.tendsto_circleIntegral_of_continuousOn
        (c := (0 : ℂ)) (R := (1 : ℝ)) (by norm_num)
        (Filter.Eventually.of_forall (fun s ↦ by
          -- Finite partial sums preserve continuity on the circle.
          refine Finset.induction_on s ?_ ?_
          · simpa using (continuousOn_const : ContinuousOn (fun _ : ℂ ↦ (0 : ℂ)) _)
          · intro m s hm hs
            simpa [Finset.sum_insert, hm] using (hcont m).add hs))) using 1
    ext s
    symm
    exact circleIntegral.integral_fun_sum fun m _ ↦ (hcont m).circleIntegrable (by norm_num)
  -- Multiply the termwise-integrated `HasSum` by the normalization scalar.
  simpa [F] using hsum_int.mul_left ((2 * Real.pi * Complex.I : ℂ)⁻¹)

/-- Helper for Exercise 12: after the standard `2 π i` normalization, the signed Taylor/binomial
contour family commutes with the unit-circle `tsum`. -/
lemma exercise12_signed_circle_integral_tsum_interchange
    (ε x : ℂ) (n : ℕ) (hε : ε = 1 ∨ ε = -1) :
    ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
        ∮ z in C(0, 1),
          ∑' m : ℕ,
            ((x / 2) ^ m / (Nat.factorial m : ℂ)) *
              (((z ^ 2 + ε) ^ m) / z ^ (m + n + 1)) =
      ∑' m : ℕ,
        ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
          ∮ z in C(0, 1),
            ((x / 2) ^ m / (Nat.factorial m : ℂ)) *
              (((z ^ 2 + ε) ^ m) / z ^ (m + n + 1)) := by
  -- This is the scalar-normalized form of the termwise circle-integration `HasSum`.
  exact (exercise12_signed_circle_integral_tsum_hasSum ε x n hε).tsum_eq.symm

/-- Helper for Exercise 12: the normalized unit-circle coefficient of the signed exponential
kernel is the corresponding signed Bessel power series. -/
lemma exercise12_signed_unit_circle_coeff_tsum
    (ε x : ℂ) (n : ℕ) (hε : ε = 1 ∨ ε = -1) :
    ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
        ∮ z in C(0, 1), Complex.exp (x * (z + ε * z⁻¹) / 2) / z ^ (n + 1) =
      ∑' p : ℕ,
        (ε ^ p * x ^ (n + 2 * p)) /
          ((2 : ℂ) ^ (n + 2 * p) * (Nat.factorial p : ℂ) *
            (Nat.factorial (n + p) : ℂ)) := by
  let A : ℕ → ℂ := fun m ↦
    ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
      ∮ z in C(0, 1),
        ((x / 2) ^ m / (Nat.factorial m : ℂ)) *
          (((z ^ 2 + ε) ^ m) / z ^ (m + n + 1))
  let coeff : ℕ → ℂ := fun p ↦
    (ε ^ p * x ^ (n + 2 * p)) /
      ((2 : ℂ) ^ (n + 2 * p) * (Nat.factorial p : ℂ) *
        (Nat.factorial (n + p) : ℂ))
  have hrewrite :
      ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
          ∮ z in C(0, 1), Complex.exp (x * (z + ε * z⁻¹) / 2) / z ^ (n + 1) =
        ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
          ∮ z in C(0, 1),
            ∑' m : ℕ,
              ((x / 2) ^ m / (Nat.factorial m : ℂ)) *
                (((z ^ 2 + ε) ^ m) / z ^ (m + n + 1)) := by
    -- Replace the exponential integrand on the unit circle by the summed Taylor/binomial family.
    refine congrArg (fun w : ℂ ↦ ((2 * Real.pi * Complex.I : ℂ)⁻¹) * w) ?_
    refine circleIntegral.integral_congr (by norm_num : (0 : ℝ) ≤ 1) ?_
    intro z hz
    symm
    exact
      (exercise12_exp_binomial_family_hasSum ε x z n
        (exercise12_ne_zero_of_mem_unit_sphere hz)).tsum_eq
  have hA_hasSum :
      HasSum A
        (((2 * Real.pi * Complex.I : ℂ)⁻¹) *
          ∮ z in C(0, 1), Complex.exp (x * (z + ε * z⁻¹) / 2) / z ^ (n + 1)) := by
    -- After rewriting the integrand, the contour/series interchange gives the desired coefficient
    -- series on the unit circle.
    rw [hrewrite]
    exact exercise12_signed_circle_integral_tsum_hasSum ε x n hε
  have hA_even (p : ℕ) : A (n + 2 * p) = coeff p := by
    -- In the matching-parity case, the binomial residue formula leaves exactly the `p`th signed
    -- Bessel coefficient.
    have hcoeff_int :
        ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
            ∮ z in C(0, 1), ((z ^ 2 + ε) ^ (n + 2 * p)) / z ^ ((n + 2 * p) + n + 1) =
          ε ^ p * (Nat.factorial (n + 2 * p) : ℂ) /
            ((Nat.factorial p : ℂ) * (Nat.factorial (n + p) : ℂ)) := by
      simpa using exercise12_circle_integral_binomial_coeff ε (n + 2 * p) n p rfl
    have hfactorial_ne :
        (Nat.factorial (n + 2 * p) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (n + 2 * p)
    calc
      A (n + 2 * p)
        = ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
            (((x / 2) ^ (n + 2 * p) / (Nat.factorial (n + 2 * p) : ℂ)) *
              ∮ z in C(0, 1), ((z ^ 2 + ε) ^ (n + 2 * p)) / z ^ ((n + 2 * p) + n + 1)) := by
              simp [A, circleIntegral.integral_const_mul]
      _ = ((x / 2) ^ (n + 2 * p) / (Nat.factorial (n + 2 * p) : ℂ)) *
            (((2 * Real.pi * Complex.I : ℂ)⁻¹) *
              ∮ z in C(0, 1), ((z ^ 2 + ε) ^ (n + 2 * p)) / z ^ ((n + 2 * p) + n + 1)) := by
              ring
      _ = ((x / 2) ^ (n + 2 * p) / (Nat.factorial (n + 2 * p) : ℂ)) *
            (ε ^ p * (Nat.factorial (n + 2 * p) : ℂ) /
              ((Nat.factorial p : ℂ) * (Nat.factorial (n + p) : ℂ))) := by
              rw [hcoeff_int]
      _ = coeff p := by
              have htwo : (2 : ℂ) ≠ 0 := by norm_num
              dsimp [coeff]
              rw [div_pow]
              field_simp [hfactorial_ne, htwo]
  have hA_odd (m : ℕ) (hm : ∀ p : ℕ, m ≠ n + 2 * p) : A m = 0 := by
    -- Away from the matching parity, the residue theorem gives zero.
    have hzero_int :
        ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
            ∮ z in C(0, 1), ((z ^ 2 + ε) ^ m) / z ^ (m + n + 1) = 0 := by
      exact exercise12_circle_integral_binomial_coeff_eq_zero ε m n hm
    calc
      A m
        = ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
            (((x / 2) ^ m / (Nat.factorial m : ℂ)) *
              ∮ z in C(0, 1), ((z ^ 2 + ε) ^ m) / z ^ (m + n + 1)) := by
              simp [A, circleIntegral.integral_const_mul]
      _ = ((x / 2) ^ m / (Nat.factorial m : ℂ)) *
            (((2 * Real.pi * Complex.I : ℂ)⁻¹) *
              ∮ z in C(0, 1), ((z ^ 2 + ε) ^ m) / z ^ (m + n + 1)) := by
              ring
      _ = 0 := by rw [hzero_int, mul_zero]
  have hA_summable : Summable A := hA_hasSum.summable
  have hprefix_zero : ∑ i ∈ Finset.range n, A i = 0 := by
    -- No index below `n` can have the required parity shape `n + 2p`.
    refine Finset.sum_eq_zero ?_
    intro m hm
    exact hA_odd m (fun p hp ↦ by
      have hm_lt : m < n := Finset.mem_range.mp hm
      omega)
  have hshift :
      ∑' m : ℕ, A m = ∑' q : ℕ, A (q + n) := by
    -- Strip off the vanishing initial segment so only the shifted tail remains.
    have hsum_shift := hA_summable.sum_add_tsum_nat_add n
    rw [hprefix_zero, zero_add] at hsum_shift
    exact hsum_shift.symm
  have htail_summable : Summable (fun q : ℕ ↦ A (q + n)) := by
    exact hA_summable.comp_injective (fun a b hab ↦ by omega)
  have hprod_summable :
      Summable (fun qr : ℕ × Fin 2 ↦ A (((Nat.divModEquiv 2).symm qr) + n)) := by
    simpa [Function.comp] using ((Nat.divModEquiv 2).symm.summable_iff).2 htail_summable
  have hsplit :
      ∑' q : ℕ, A (q + n) =
        ∑' p : ℕ, ∑' r : Fin 2, A (((Nat.divModEquiv 2).symm (p, r)) + n) := by
    -- Split the shifted tail into even and odd parity classes by `Nat.divModEquiv 2`.
    calc
      ∑' q : ℕ, A (q + n)
        = ∑' qr : ℕ × Fin 2, A (((Nat.divModEquiv 2).symm qr) + n) := by
            simpa using ((Nat.divModEquiv 2).symm.tsum_eq (fun q : ℕ ↦ A (q + n))).symm
      _ = ∑' p : ℕ, ∑' r : Fin 2, A (((Nat.divModEquiv 2).symm (p, r)) + n) := by
            simpa using hprod_summable.tsum_prod
  have hparity (p : ℕ) :
      (∑' r : Fin 2, A (((Nat.divModEquiv 2).symm (p, r)) + n)) = coeff p := by
    -- The even branch contributes `coeff p`, while the odd branch vanishes.
    have hzero :
        A (((Nat.divModEquiv 2).symm (p, (1 : Fin 2))) + n) = 0 := by
      refine hA_odd _ (fun q hq ↦ ?_)
      have hodd :
          ((Nat.divModEquiv 2).symm (p, (1 : Fin 2))) + n = n + (2 * p + 1) := by
        simp [Nat.divModEquiv]
        omega
      rw [hodd] at hq
      omega
    have heven :
        A (((Nat.divModEquiv 2).symm (p, (0 : Fin 2))) + n) = coeff p := by
      have heq :
          ((Nat.divModEquiv 2).symm (p, (0 : Fin 2))) + n = n + 2 * p := by
        simp [Nat.divModEquiv]
        omega
      rw [heq]
      exact hA_even p
    calc
      (∑' r : Fin 2, A (((Nat.divModEquiv 2).symm (p, r)) + n))
        = A (((Nat.divModEquiv 2).symm (p, (0 : Fin 2))) + n) +
            A (((Nat.divModEquiv 2).symm (p, (1 : Fin 2))) + n) := by
              rw [tsum_fintype]
              simp
      _ = coeff p + 0 := by rw [heven, hzero]
      _ = coeff p := by simp
  -- Assemble the contour coefficient identity: rewrite by the Taylor family, split by parity,
  -- and evaluate the surviving even branch with the residue formula.
  calc
    ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
        ∮ z in C(0, 1), Complex.exp (x * (z + ε * z⁻¹) / 2) / z ^ (n + 1)
      = ∑' m : ℕ, A m := hA_hasSum.tsum_eq.symm
    _ = ∑' q : ℕ, A (q + n) := hshift
    _ = ∑' p : ℕ, ∑' r : Fin 2, A (((Nat.divModEquiv 2).symm (p, r)) + n) := hsplit
    _ = ∑' p : ℕ, coeff p := by
          refine tsum_congr hparity
    _ = ∑' p : ℕ,
          (ε ^ p * x ^ (n + 2 * p)) /
            ((2 : ℂ) ^ (n + 2 * p) * (Nat.factorial p : ℂ) *
              (Nat.factorial (n + p) : ℂ)) := by
          rfl

/-- Exercise 12 (5): as a function of the complex parameter `x`, `I_n(x)` has the standard
modified-Bessel power-series expansion. -/
theorem modifiedBesselI_tsum
    (n : ℕ) (x : ℂ) :
    I_[n] x =
      ∑' p : ℕ,
        x ^ (n + 2 * p) /
          ((2 : ℂ) ^ (n + 2 * p) * (Nat.factorial p : ℂ) *
            (Nat.factorial (n + p) : ℂ)) := by
  -- Specialize the signed contour-series computation to `ε = 1`, then use the established
  -- unit-circle coefficient formula for `I_n`.
  calc
    I_[n] x
      = ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
          ∮ z in C(0, 1), Complex.exp (x * (z + z⁻¹) / 2) / z ^ (n + 1) := by
            exact modifiedBesselI_eq_unit_circle_coeff n x
    _ = ∑' p : ℕ,
          ((1 : ℂ) ^ p * x ^ (n + 2 * p)) /
            ((2 : ℂ) ^ (n + 2 * p) * (Nat.factorial p : ℂ) *
              (Nat.factorial (n + p) : ℂ)) := by
            simpa using
              exercise12_signed_unit_circle_coeff_tsum (ε := (1 : ℂ)) x n (Or.inl rfl)
    _ = ∑' p : ℕ,
          x ^ (n + 2 * p) /
            ((2 : ℂ) ^ (n + 2 * p) * (Nat.factorial p : ℂ) *
              (Nat.factorial (n + p) : ℂ)) := by
            simp

/-- Exercise 12 (6): as a function of the complex parameter `x`, `J_n(x)` has the standard Bessel
power-series expansion. -/
theorem besselJ_tsum
    (n : ℕ) (x : ℂ) :
    J_[n] x =
      ∑' p : ℕ,
        ((-1 : ℂ) ^ p * x ^ (n + 2 * p)) /
          ((2 : ℂ) ^ (n + 2 * p) * (Nat.factorial p : ℂ) *
            (Nat.factorial (n + p) : ℂ)) := by
  -- Specialize the same signed contour-series computation to `ε = -1`, then rewrite
  -- `z + (-1) * z⁻¹` to the textbook kernel `z - z⁻¹`.
  calc
    J_[n] x
      = ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
          ∮ z in C(0, 1), Complex.exp (x * (z - z⁻¹) / 2) / z ^ (n + 1) := by
            exact besselJ_eq_unit_circle_coeff n x
    _ = ((2 * Real.pi * Complex.I : ℂ)⁻¹) *
          ∮ z in C(0, 1), Complex.exp (x * (z + (-1 : ℂ) * z⁻¹) / 2) / z ^ (n + 1) := by
            congr 2
            ext z
            congr 1
            ring
    _ = ∑' p : ℕ,
          (((-1 : ℂ) : ℂ) ^ p * x ^ (n + 2 * p)) /
            ((2 : ℂ) ^ (n + 2 * p) * (Nat.factorial p : ℂ) *
              (Nat.factorial (n + p) : ℂ)) := by
            simpa using
              exercise12_signed_unit_circle_coeff_tsum (ε := (-1 : ℂ)) x n (Or.inr rfl)
