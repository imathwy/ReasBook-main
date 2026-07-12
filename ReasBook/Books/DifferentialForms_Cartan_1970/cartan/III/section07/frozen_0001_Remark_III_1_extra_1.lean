import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open FormalMultilinearSeries
open MeasureTheory
open scoped Interval Real

/- Domain-style sampling:
- `source-facing`: the two coefficient formulas in this file.
- `core/canonical`: the boundary circle as `Metric.sphere (0 : ℂ) r`.
- `bridge/view`: the `circleMap 0 r θ` parametrization used only inside the Fourier integral. -/

namespace HasFPowerSeriesOnBall

/-- Helper for Cartan section07 frozen_0001_Remark_III_1_extra_1 (Remark III.1-extra-1): on every
smaller circle, the original power-series witness matches the canonical Cauchy power series. -/
theorem eq_cauchyPowerSeries_of_lt_radius
    {ρ r : NNReal} {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HasFPowerSeriesOnBall f p 0 ρ) (hr₀ : 0 < r) (hr : r < ρ) :
    p = cauchyPowerSeries f 0 (r : ℝ) := by
  -- Restrict differentiability to the smaller closed disc so the canonical Cauchy series applies.
  have hdiff : DifferentiableOn ℂ f (Metric.ball 0 (ρ : ℝ)) := by
    simpa [Metric.eball_coe] using hf.differentiableOn
  have hcauchy : HasFPowerSeriesOnBall f (cauchyPowerSeries f 0 (r : ℝ)) 0 r := by
    exact DifferentiableOn.hasFPowerSeriesOnBall
      (hdiff.mono <|
        Metric.closedBall_subset_ball (show (r : ℝ) < (ρ : ℝ) by exact_mod_cast hr))
      (show 0 < (r : ℝ) by exact_mod_cast hr₀)
  -- Power-series expansions at the center are unique.
  exact hf.hasFPowerSeriesAt.eq_formalMultilinearSeries hcauchy.hasFPowerSeriesAt

end HasFPowerSeriesOnBall

/-- Helper for Cartan section07 frozen_0001_Remark_III_1_extra_1 (Remark III.1-extra-1): the
Cauchy-integral integrand on the circle rewrites to the Fourier integrand
`i e^{-inθ} f(re^{iθ})`. -/
lemma circleMapCauchyIntegrand_eq
    {f : ℂ → ℂ} {r : ℝ} {n : ℕ} (hr : r ≠ 0) :
    (fun θ : ℝ ↦
      deriv (circleMap 0 r) θ *
        (((r : ℂ) / circleMap 0 r θ) ^ n * ((circleMap 0 r θ)⁻¹ * f (circleMap 0 r θ)))) =
      fun θ : ℝ ↦
        Complex.I * (Complex.exp (-(n : ℂ) * θ * Complex.I) * f (circleMap 0 r θ)) := by
  -- Rewrite the circle quotient into a unit-circle term and simplify the derivative factor.
  funext θ
  have hcircle : circleMap 0 r θ ≠ 0 := circleMap_ne_center hr
  have hdiv : (r : ℂ) / circleMap 0 r θ = circleMap 0 1 (-θ) := by
    calc
      (r : ℂ) / circleMap 0 r θ = circleMap 0 r 0 / circleMap 0 r θ := by
        simp [circleMap_zero]
      _ = circleMap 0 (r / r) (0 - θ) := by
        rw [circleMap_zero_div]
      _ = circleMap 0 1 (-θ) := by
        simp [hr]
  calc
    deriv (circleMap 0 r) θ *
        (((r : ℂ) / circleMap 0 r θ) ^ n * ((circleMap 0 r θ)⁻¹ * f (circleMap 0 r θ))) =
        Complex.I *
          ((((r : ℂ) / circleMap 0 r θ) ^ n) * f (circleMap 0 r θ)) := by
          rw [deriv_circleMap]
          calc
            circleMap 0 r θ * Complex.I *
                (((r : ℂ) / circleMap 0 r θ) ^ n *
                  ((circleMap 0 r θ)⁻¹ * f (circleMap 0 r θ))) =
                Complex.I *
                  (circleMap 0 r θ *
                    (((r : ℂ) / circleMap 0 r θ) ^ n *
                      ((circleMap 0 r θ)⁻¹ * f (circleMap 0 r θ)))) := by
                  ac_rfl
            _ = Complex.I *
                ((((r : ℂ) / circleMap 0 r θ) ^ n) * f (circleMap 0 r θ)) := by
                  congr 1
                  calc
                    circleMap 0 r θ *
                        (((r : ℂ) / circleMap 0 r θ) ^ n *
                          ((circleMap 0 r θ)⁻¹ * f (circleMap 0 r θ))) =
                        (circleMap 0 r θ * (circleMap 0 r θ)⁻¹) *
                          (f (circleMap 0 r θ) * ((r : ℂ) / circleMap 0 r θ) ^ n) := by
                        ac_rfl
                    _ = f (circleMap 0 r θ) * ((r : ℂ) / circleMap 0 r θ) ^ n := by
                      simp [hcircle]
                    _ = (((r : ℂ) / circleMap 0 r θ) ^ n) * f (circleMap 0 r θ) := by
                      ac_rfl
    _ = Complex.I * (Complex.exp (-(n : ℂ) * θ * Complex.I) * f (circleMap 0 r θ)) := by
      rw [hdiv, circleMap_zero_pow, circleMap_zero]
      simp [mul_comm]

/-- Helper for Cartan section07 frozen_0001_Remark_III_1_extra_1 (Remark III.1-extra-1): the
nonzero Fourier modes integrate to zero on `[0, 2π]`. -/
lemma integral_exp_neg_nat_succ_mul_I_eq_zero (n : ℕ) :
    ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      Complex.exp (-(((n + 1 : ℕ) : ℂ) * θ * Complex.I)) = 0 := by
  -- Reduce to the standard integral of `exp (c * θ)` with a nonzero frequency `c`.
  let c : ℂ := -(((n + 1 : ℕ) : ℂ) * Complex.I)
  have hn : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hc : c ≠ 0 := by
    dsimp [c]
    exact neg_ne_zero.mpr (mul_ne_zero hn Complex.I_ne_zero)
  have hrewrite :
      (fun θ : ℝ ↦ Complex.exp (-(((n + 1 : ℕ) : ℂ) * θ * Complex.I))) =
        fun θ : ℝ ↦ Complex.exp (c * θ) := by
    funext θ
    simp [c, mul_left_comm, mul_comm]
  have hperiod : Complex.exp (c * (2 * Real.pi)) = 1 := by
    have hrewriteMul :
        c * (2 * Real.pi) = -(((n + 1 : ℕ) : ℂ) * (2 * Real.pi * Complex.I)) := by
      dsimp [c]
      ring
    calc
      Complex.exp (c * (2 * Real.pi)) =
          Complex.exp (-(((n + 1 : ℕ) : ℂ) * (2 * Real.pi * Complex.I))) := by
            rw [hrewriteMul]
      _ = (Complex.exp (((n + 1 : ℕ) : ℂ) * (2 * Real.pi * Complex.I)))⁻¹ := by
            simp [Complex.exp_neg]
      _ = 1 := by
            simpa using Complex.exp_nat_mul_two_pi_mul_I (n + 1)
  rw [hrewrite, integral_exp_mul_complex hc]
  simp [hperiod]

-- Proof sketch: use the convergent power-series expansion on the circle `|z| = r`, integrate the
-- series termwise over `θ ∈ [0, 2π]`, and use Fourier orthogonality to isolate the `n`-th term.
/-- Cartan section07 frozen_0001_Remark_III_1_extra_1 (Remark III.1-extra-1): if `f` is
represented on the disc `|z| < ρ` by the scalar power series `∑ aₙ z^n`, then for every
`0 ≤ r < ρ` the coefficient `aₙ` satisfies the Fourier-type integral formula
`aₙ r^n = (2π)⁻¹ ∫₀^{2π} e^{-inθ} f(r e^{iθ}) dθ`. -/
theorem taylor_coefficient_mul_pow_eq_circleFourierIntegral
    {f : ℂ → ℂ} {a : ℕ → ℂ} {ρ r : ℝ} (n : ℕ)
    (hf : HasFPowerSeriesOnBall f (ofScalars ℂ a) 0 (ENNReal.ofReal ρ))
    (hr₀ : 0 ≤ r) (hr : r < ρ) :
    a n * (r : ℂ) ^ n =
      (1 / (2 * Real.pi : ℂ)) *
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
          Complex.exp (-(n : ℂ) * θ * Complex.I) * f (circleMap 0 r θ) := by
  rcases lt_or_eq_of_le hr₀ with hr₀ | rfl
  · -- On a positive-radius circle, rewrite through the canonical Cauchy power series.
    have hρ : 0 ≤ ρ := by
      linarith
    let ρNN : NNReal := ⟨ρ, hρ⟩
    let rNN : NNReal := ⟨r, hr₀.le⟩
    have hρENN : ENNReal.ofReal ρ = (ρNN : ENNReal) := by
      dsimp [ρNN]
      rw [ENNReal.ofReal_eq_coe_nnreal hρ]
      rfl
    have hfNN : HasFPowerSeriesOnBall f (ofScalars ℂ a) 0 ρNN := by
      simpa [hρENN] using hf
    have hrNN : rNN < ρNN := by
      exact_mod_cast hr
    have hpeq : ofScalars ℂ a = cauchyPowerSeries f 0 r := by
      simpa [rNN] using
        (HasFPowerSeriesOnBall.eq_cauchyPowerSeries_of_lt_radius
          (f := f) (p := ofScalars ℂ a) (ρ := ρNN) (r := rNN) hfNN
          (by simpa [rNN]) hrNN)
    calc
      a n * (r : ℂ) ^ n = (ofScalars ℂ a).coeff n * (r : ℂ) ^ n := by
        simp [FormalMultilinearSeries.coeff_ofScalars]
      _ = cauchyPowerSeries f 0 r n (fun _ ↦ (r : ℂ)) := by
        rw [hpeq]
        rw [mul_comm]
        rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff]
        simp [smul_eq_mul]
      _ = (1 / (2 * Real.pi : ℂ)) *
          ∫ θ in (0 : ℝ)..(2 * Real.pi),
            Complex.exp (-(n : ℂ) * θ * Complex.I) * f (circleMap 0 r θ) := by
          rw [cauchyPowerSeries_apply, circleIntegral]
          simp only [sub_zero, smul_eq_mul]
          have hr' : r ≠ 0 := by positivity
          have hIntegral :
              ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
                deriv (circleMap 0 r) θ *
                  (((r : ℂ) / circleMap 0 r θ) ^ n *
                    ((circleMap 0 r θ)⁻¹ * f (circleMap 0 r θ))) =
                ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
                  Complex.I *
                    (Complex.exp (-(n : ℂ) * θ * Complex.I) * f (circleMap 0 r θ)) := by
            -- Rewrite the Cauchy kernel into the Fourier kernel before extracting the constant.
            congr with θ
            exact congrFun (circleMapCauchyIntegrand_eq (f := f) (n := n) hr') θ
          -- Normalize the Cauchy kernel into the Fourier kernel from the textbook formula.
          rw [hIntegral, intervalIntegral.integral_const_mul]
          field_simp [Real.two_pi_pos.ne', Complex.I_ne_zero]
  · -- At radius zero, the constant Fourier mode survives and the higher modes vanish.
    cases n with
    | zero =>
        rw [pow_zero, mul_one]
        conv in ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), _ =>
          simp [circleMap]
        field_simp [Real.pi_ne_zero]
        simpa [FormalMultilinearSeries.coeff_ofScalars] using hf.coeff_zero 1
    | succ n =>
        conv in ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), _ =>
          simp [circleMap]
        have hInt' :
            ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
              Complex.exp ((-1 + -((n : ℕ) : ℂ)) * θ * Complex.I) = 0 := by
          have hfun :
              (fun θ : ℝ ↦ Complex.exp ((-1 + -((n : ℕ) : ℂ)) * θ * Complex.I)) =
                fun θ : ℝ ↦ Complex.exp (-(((n + 1 : ℕ) : ℂ) * θ * Complex.I)) := by
            funext θ
            congr 1
            calc
              (-1 + -((n : ℕ) : ℂ)) * θ * Complex.I = -(↑n * ↑θ * Complex.I) - ↑θ * Complex.I := by
                ring
              _ = -((↑n + 1) * ↑θ * Complex.I) := by
                ring
              _ = -(((n + 1 : ℕ) : ℂ) * ↑θ * Complex.I) := by
                norm_num
          simpa [hfun] using integral_exp_neg_nat_succ_mul_I_eq_zero n
        rw [hInt']
        simp

-- Proof sketch: take norms in
-- `taylor_coefficient_mul_pow_eq_circleFourierIntegral`, bound the integrand by `M` on the circle,
-- and divide the resulting estimate by `r^n`.
/-- For Cartan section07 frozen_0001_Remark_III_1_extra_1 (Remark III.1-extra-1), any uniform
bound of `‖f z‖` on the boundary circle `|z| = r` yields the corresponding Cauchy inequality for
the coefficients of the Taylor expansion. -/
theorem norm_taylor_coefficient_le_of_circle_bound
    {f : ℂ → ℂ} {a : ℕ → ℂ} {ρ r M : ℝ} (n : ℕ)
    (hf : HasFPowerSeriesOnBall f (ofScalars ℂ a) 0 (ENNReal.ofReal ρ))
    (hr₀ : 0 < r) (hr : r < ρ)
    (hM : ∀ z ∈ Metric.sphere (0 : ℂ) r, ‖f z‖ ≤ M) :
    ‖a n‖ ≤ M / r ^ n := by
  have hρ : 0 ≤ ρ := by
    linarith
  let ρNN : NNReal := ⟨ρ, hρ⟩
  let rNN : NNReal := ⟨r, hr₀.le⟩
  have hρENN : ENNReal.ofReal ρ = (ρNN : ENNReal) := by
    dsimp [ρNN]
    rw [ENNReal.ofReal_eq_coe_nnreal hρ]
    rfl
  have hfNN : HasFPowerSeriesOnBall f (ofScalars ℂ a) 0 ρNN := by
    simpa [hρENN] using hf
  have hrNN : rNN < ρNN := by
    exact_mod_cast hr
  have hpeq : ofScalars ℂ a = cauchyPowerSeries f 0 r := by
    simpa [rNN] using
      (HasFPowerSeriesOnBall.eq_cauchyPowerSeries_of_lt_radius
        (f := f) (p := ofScalars ℂ a) (ρ := ρNN) (r := rNN) hfNN
        (by simpa [rNN]) hrNN)
  -- Restrict the analytic function to the boundary circle to make the norm integral available.
  have hcont : Continuous fun θ : ℝ ↦ f (circleMap 0 r θ) := by
    have hdiff : DifferentiableOn ℂ f (Metric.closedBall 0 r) := by
      have hdiffρ : DifferentiableOn ℂ f (Metric.ball 0 ρ) := by
        simpa [Metric.eball_coe] using hf.differentiableOn
      exact hdiffρ.mono <|
        Metric.closedBall_subset_ball (show (r : ℝ) < ρ by simpa using hr)
    exact
      hdiff.continuousOn.comp_continuous (continuous_circleMap 0 r) fun θ ↦
        circleMap_mem_closedBall 0 hr₀.le θ
  have hnormInt :
      IntervalIntegrable (fun θ : ℝ ↦ ‖f (circleMap 0 r θ)‖) MeasureTheory.volume 0
        (2 * Real.pi) :=
    hcont.norm.intervalIntegrable 0 (2 * Real.pi)
  have hMInt : IntervalIntegrable (fun _ : ℝ ↦ M) MeasureTheory.volume 0 (2 * Real.pi) :=
    Continuous.intervalIntegrable continuous_const 0 (2 * Real.pi)
  have hInt_le :
      ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), ‖f (circleMap 0 r θ)‖ ≤
        ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), M := by
    exact intervalIntegral.integral_mono_on Real.two_pi_pos.le hnormInt hMInt fun θ _ ↦
      hM _ (circleMap_mem_sphere 0 hr₀.le θ)
  -- Apply the standard Cauchy estimate to the canonical Cauchy power series and translate back.
  calc
    ‖a n‖ = ‖(ofScalars ℂ a).coeff n‖ := by
      simp [FormalMultilinearSeries.coeff_ofScalars]
    _ = ‖(cauchyPowerSeries f 0 r).coeff n‖ := by
      rw [hpeq]
    _ = ‖cauchyPowerSeries f 0 r n‖ := by
      simp
    _ ≤ ((2 * Real.pi)⁻¹ *
          ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), ‖f (circleMap 0 r θ)‖) * r⁻¹ ^ n := by
        simpa [abs_of_pos hr₀] using norm_cauchyPowerSeries_le f 0 r n
    _ ≤ ((2 * Real.pi)⁻¹ * ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), M) * r⁻¹ ^ n := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hInt_le (by positivity))
          (by positivity)
    _ = M / r ^ n := by
        rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul,
          ← mul_assoc ((2 * Real.pi)⁻¹) (2 * Real.pi) M, inv_mul_cancel₀ Real.two_pi_pos.ne',
          one_mul, div_eq_mul_inv, inv_pow]
