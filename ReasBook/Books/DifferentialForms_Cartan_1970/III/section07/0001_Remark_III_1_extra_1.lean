import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open scoped Interval Real
open Complex FormalMultilinearSeries
open MeasureTheory

/- Domain-style sampling:
- `source-facing`: the Fourier coefficient identity and the resulting Cauchy inequality below.
- `core/canonical`: `HasFPowerSeriesOnBall`, `cauchyPowerSeries`, `cauchyPowerSeries_apply`,
  and `norm_cauchyPowerSeries_le`.
- `derived API`: uniqueness of power-series coefficients via
  `HasFPowerSeriesAt.eq_formalMultilinearSeries`.
- `bridge/view`: the `circleMap 0 r θ` parametrization used in the textbook boundary integral. -/

variable {ρ r : NNReal} {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}

namespace HasFPowerSeriesOnBall

/-- If `f` is represented on the disc of radius `ρ` by the formal multilinear series `p`, then on
every smaller circle the same coefficients are recovered by the canonical Cauchy-integral power
series. This is the comparison bridge from a source-facing power-series witness to the canonical
`cauchyPowerSeries` owner. -/
theorem eq_cauchyPowerSeries_of_lt_radius
    (hf : HasFPowerSeriesOnBall f p 0 ρ) (hr0 : 0 < r) (hr : r < ρ) :
    p = cauchyPowerSeries f 0 (r : ℝ) := by
  have hdiff : DifferentiableOn ℂ f (Metric.ball 0 (ρ : ℝ)) := by
    simpa [Metric.eball_coe] using hf.differentiableOn
  have hcauchy : HasFPowerSeriesOnBall f (cauchyPowerSeries f 0 (r : ℝ)) 0 r := by
    exact DifferentiableOn.hasFPowerSeriesOnBall
      (hdiff.mono <|
        Metric.closedBall_subset_ball (show (r : ℝ) < (ρ : ℝ) by exact_mod_cast hr))
      (show 0 < (r : ℝ) by exact_mod_cast hr0)
  exact hf.hasFPowerSeriesAt.eq_formalMultilinearSeries hcauchy.hasFPowerSeriesAt

end HasFPowerSeriesOnBall

/-- Remark III.1-extra-1 (1): if `f` admits a power-series expansion on a disc centered at `0`,
then each coefficient is the corresponding Fourier coefficient of the boundary value
`θ ↦ f (r * exp (θ I))` on every smaller circle. -/
theorem taylor_coeff_mul_pow_eq_circle_fourier_integral
    (n : ℕ) (hf : HasFPowerSeriesOnBall f p 0 ρ) (hr : r < ρ) :
    p.coeff n * (r : ℂ) ^ n =
      (1 / (2 * π : ℂ)) * ∫ θ in (0 : ℝ)..(2 * π),
        exp (-(n : ℂ) * θ * I) * f (circleMap 0 (r : ℝ) θ) := by
  rcases lt_or_eq_of_le r.2 with hr0 | hr_eq
  · have hpeq := hf.eq_cauchyPowerSeries_of_lt_radius hr0 hr
    calc
      p.coeff n * (r : ℂ) ^ n = (cauchyPowerSeries f 0 (r : ℝ) n fun _ ↦ (r : ℂ)) := by
        rw [hpeq]
        rw [mul_comm]
        rw [apply_eq_pow_smul_coeff]
        simp [smul_eq_mul]
      _ = (1 / (2 * π : ℂ)) * ∫ θ in (0 : ℝ)..(2 * π),
          exp (-(n : ℂ) * θ * I) * f (circleMap 0 (r : ℝ) θ) := by
        rw [cauchyPowerSeries_apply, circleIntegral]
        simp only [sub_zero, smul_eq_mul]
        have hr' : (r : ℝ) ≠ 0 := by positivity
        have hIntegrand :
            (fun θ : ℝ ↦
              deriv (circleMap 0 (r : ℝ)) θ *
                (((r : ℂ) / circleMap 0 (r : ℝ) θ) ^ n *
                  ((circleMap 0 (r : ℝ) θ)⁻¹ * f (circleMap 0 (r : ℝ) θ)))) =
              fun θ : ℝ ↦ I * (exp (-(n : ℂ) * θ * I) * f (circleMap 0 (r : ℝ) θ)) := by
          funext θ
          have hcircle : circleMap 0 (r : ℝ) θ ≠ 0 := circleMap_ne_center hr'
          have hdiv :
              (r : ℂ) / circleMap 0 (r : ℝ) θ = circleMap 0 1 (-θ) := by
            calc
              (r : ℂ) / circleMap 0 (r : ℝ) θ
                  = circleMap 0 (r : ℝ) 0 / circleMap 0 (r : ℝ) θ := by
                    simp [circleMap_zero]
              _ = circleMap 0 ((r : ℝ) / (r : ℝ)) (0 - θ) := by
                    rw [circleMap_zero_div]
              _ = circleMap 0 1 (-θ) := by
                    simp [hr']
          calc
            deriv (circleMap 0 (r : ℝ)) θ *
                (((r : ℂ) / circleMap 0 (r : ℝ) θ) ^ n *
                  ((circleMap 0 (r : ℝ) θ)⁻¹ * f (circleMap 0 (r : ℝ) θ)))
                = I * ((((r : ℂ) / circleMap 0 (r : ℝ) θ) ^ n) * f (circleMap 0 (r : ℝ) θ)) := by
                    rw [deriv_circleMap]
                    calc
                      circleMap 0 (r : ℝ) θ * I *
                          (((r : ℂ) / circleMap 0 (r : ℝ) θ) ^ n *
                            ((circleMap 0 (r : ℝ) θ)⁻¹ * f (circleMap 0 (r : ℝ) θ)))
                          =
                          I *
                            (circleMap 0 (r : ℝ) θ *
                              (((r : ℂ) / circleMap 0 (r : ℝ) θ) ^ n *
                                ((circleMap 0 (r : ℝ) θ)⁻¹ * f (circleMap 0 (r : ℝ) θ)))) := by
                            ac_rfl
                      _ =
                          I * ((((r : ℂ) / circleMap 0 (r : ℝ) θ) ^ n) *
                            f (circleMap 0 (r : ℝ) θ)) := by
                            congr 1
                            calc
                              circleMap 0 (r : ℝ) θ *
                                  (((r : ℂ) / circleMap 0 (r : ℝ) θ) ^ n *
                                    ((circleMap 0 (r : ℝ) θ)⁻¹ * f (circleMap 0 (r : ℝ) θ)))
                                  =
                                  (circleMap 0 (r : ℝ) θ * (circleMap 0 (r : ℝ) θ)⁻¹) *
                                    (f (circleMap 0 (r : ℝ) θ) *
                                      ((r : ℂ) / circleMap 0 (r : ℝ) θ) ^ n) := by
                                    ac_rfl
                              _ = f (circleMap 0 (r : ℝ) θ) *
                                    ((r : ℂ) / circleMap 0 (r : ℝ) θ) ^ n := by
                                    simp [hcircle]
                              _ = (((r : ℂ) / circleMap 0 (r : ℝ) θ) ^ n) *
                                    f (circleMap 0 (r : ℝ) θ) := by
                                    ac_rfl
            _ = I * (exp (-(n : ℂ) * θ * I) * f (circleMap 0 (r : ℝ) θ)) := by
                  rw [hdiv, circleMap_zero_pow, circleMap_zero]
                  simp [mul_comm]
        conv in ∫ θ : ℝ in 0..2 * π, _ => rw [hIntegrand]
        rw [intervalIntegral.integral_const_mul]
        field_simp [Real.two_pi_pos.ne', Complex.I_ne_zero]
  · have hr_eq_zero : r = 0 := by
      simpa using hr_eq.symm
    subst hr_eq_zero
    cases n with
    | zero =>
        rw [pow_zero, mul_one]
        change p 0 1 = _
        rw [hf.coeff_zero 1]
        conv in ∫ θ : ℝ in 0..2 * π, _ => simp [circleMap]
        field_simp [Real.pi_ne_zero]
    | succ n =>
        have hInt :
            ∫ θ : ℝ in 0..2 * π, exp (-(((n + 1 : ℕ) : ℂ) * θ * I)) = 0 := by
          let c : ℂ := -(((n + 1 : ℕ) : ℂ) * I)
          have hn : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
          have hc : c ≠ 0 := by
            dsimp [c]
            exact neg_ne_zero.mpr (mul_ne_zero hn Complex.I_ne_zero)
          have hrewrite :
              (fun θ : ℝ ↦ exp (-((((n + 1 : ℕ) : ℂ)) * θ * I))) = fun θ : ℝ ↦ exp (c * θ) := by
            funext θ
            simp [c, mul_left_comm, mul_comm]
          have hperiod : exp (c * (2 * π)) = 1 := by
            dsimp [c]
            rw [show -((((n + 1 : ℕ) : ℂ)) * I) * (2 * π) =
                -(((n + 1 : ℕ) : ℂ) * (2 * π * I)) by ring]
            simpa [Complex.exp_neg] using Complex.exp_nat_mul_two_pi_mul_I (n + 1)
          rw [hrewrite, integral_exp_mul_complex hc]
          simp [hperiod]
        conv in ∫ θ : ℝ in 0..2 * π, _ => simp [circleMap]
        have hInt' :
            ∫ θ : ℝ in 0..2 * π, exp ((-1 + -((n : ℕ) : ℂ)) * θ * I) = 0 := by
          have hfun :
              (fun θ : ℝ ↦ exp ((-1 + -((n : ℕ) : ℂ)) * θ * I)) =
                fun θ : ℝ ↦ exp (-(((n + 1 : ℕ) : ℂ) * θ * I)) := by
            funext θ
            congr 1
            calc
              (-1 + -((n : ℕ) : ℂ)) * θ * I = -(↑n * ↑θ * I) - ↑θ * I := by ring
              _ = -((↑n + 1) * ↑θ * I) := by ring
              _ = -(((n + 1 : ℕ) : ℂ) * ↑θ * I) := by norm_num
          simpa [hfun] using hInt
        rw [hInt']
        simp

/-- Remark III.1-extra-1 (2): Cauchy's inequalities for the coefficients of a power-series
expansion on a disc, assuming a uniform bound on the corresponding boundary circle. -/
theorem norm_taylor_coeff_le_div_pow_of_bound_on_circle
    (n : ℕ) (hf : HasFPowerSeriesOnBall f p 0 ρ) (hr0 : 0 < r) (hr : r < ρ) {M : ℝ}
    (hM : ∀ z ∈ Metric.sphere (0 : ℂ) (r : ℝ), ‖f z‖ ≤ M) :
    ‖p.coeff n‖ ≤ M / (r : ℝ) ^ n := by
  have hpeq := hf.eq_cauchyPowerSeries_of_lt_radius hr0 hr
  have hcont : Continuous fun θ : ℝ ↦ f (circleMap 0 (r : ℝ) θ) := by
    have hdiff : DifferentiableOn ℂ f (Metric.closedBall 0 (r : ℝ)) := by
      have hdiffρ : DifferentiableOn ℂ f (Metric.ball 0 (ρ : ℝ)) := by
        simpa [Metric.eball_coe] using hf.differentiableOn
      exact
        hdiffρ.mono <|
          Metric.closedBall_subset_ball (show (r : ℝ) < (ρ : ℝ) by exact_mod_cast hr)
    exact
      hdiff.continuousOn.comp_continuous (continuous_circleMap 0 (r : ℝ)) fun θ ↦
        circleMap_mem_closedBall 0 (show 0 ≤ (r : ℝ) by exact_mod_cast hr0.le) θ
  have hnormInt :
      IntervalIntegrable (fun θ : ℝ ↦ ‖f (circleMap 0 (r : ℝ) θ)‖) volume 0 (2 * π) :=
    hcont.norm.intervalIntegrable 0 (2 * π)
  have hMInt : IntervalIntegrable (fun _ : ℝ ↦ M) volume 0 (2 * π) :=
    Continuous.intervalIntegrable continuous_const 0 (2 * π)
  have hInt_le : ∫ θ : ℝ in 0..2 * π, ‖f (circleMap 0 (r : ℝ) θ)‖ ≤ ∫ θ : ℝ in 0..2 * π, M := by
    exact intervalIntegral.integral_mono_on Real.two_pi_pos.le hnormInt hMInt fun θ _ ↦
      hM _ (circleMap_mem_sphere 0 (show 0 ≤ (r : ℝ) by exact_mod_cast hr0.le) θ)
  calc
    ‖p.coeff n‖ = ‖(cauchyPowerSeries f 0 (r : ℝ)).coeff n‖ := by simp [hpeq]
    _ = ‖cauchyPowerSeries f 0 (r : ℝ) n‖ := by
      simp
    _ ≤ ((2 * π)⁻¹ * ∫ θ : ℝ in 0..2 * π, ‖f (circleMap 0 (r : ℝ) θ)‖) * (r : ℝ)⁻¹ ^ n := by
      simpa [abs_of_pos (show 0 < (r : ℝ) by exact_mod_cast hr0)] using
        norm_cauchyPowerSeries_le f 0 (r : ℝ) n
    _ ≤ ((2 * π)⁻¹ * ∫ θ : ℝ in 0..2 * π, M) * (r : ℝ)⁻¹ ^ n := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hInt_le (by positivity))
        (by positivity)
    _ = M / (r : ℝ) ^ n := by
      rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul,
        ← mul_assoc ((2 * π)⁻¹) (2 * π) M, inv_mul_cancel₀ Real.two_pi_pos.ne', one_mul,
        div_eq_mul_inv, inv_pow]
