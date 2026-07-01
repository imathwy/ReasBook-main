import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open FormalMultilinearSeries

/- Domain-style sampling:
- `source-facing`: the two coefficient formulas in this file.
- `core/canonical`: the boundary circle as `Metric.sphere (0 : ℂ) r`.
- `bridge/view`: the `circleMap 0 r θ` parametrization used only inside the Fourier integral. -/

-- Proof sketch: use the convergent power-series expansion on the circle `|z| = r`, integrate the
-- series termwise over `θ ∈ [0, 2π]`, and use Fourier orthogonality to isolate the `n`-th term.
/-- Remark III.1-extra-1: if `f` is represented on the disc `|z| < ρ` by the scalar power series
`∑ aₙ z^n`, then for every `0 ≤ r < ρ` the coefficient `aₙ` satisfies the Fourier-type integral
formula `aₙ r^n = (2π)⁻¹ ∫₀^{2π} e^{-inθ} f(r e^{iθ}) dθ`. -/
theorem taylor_coefficient_mul_pow_eq_circleFourierIntegral
    {f : ℂ → ℂ} {a : ℕ → ℂ} {ρ r : ℝ} (n : ℕ)
    (hf : HasFPowerSeriesOnBall f (ofScalars ℂ a) 0 (ENNReal.ofReal ρ))
    (hr₀ : 0 ≤ r) (hr : r < ρ) :
    a n * (r : ℂ) ^ n =
      (1 / (2 * Real.pi : ℂ)) *
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
          Complex.exp (-(n : ℂ) * θ * Complex.I) * f (circleMap 0 r θ) := sorry

-- Proof sketch: take norms in
-- `taylor_coefficient_mul_pow_eq_circleFourierIntegral`, bound the integrand by `M` on the circle,
-- and divide the resulting estimate by `r^n`.
/-- Any uniform bound of `‖f z‖` on the boundary circle `|z| = r` yields the corresponding Cauchy
inequality for the coefficients of the Taylor expansion. -/
theorem norm_taylor_coefficient_le_of_circle_bound
    {f : ℂ → ℂ} {a : ℕ → ℂ} {ρ r M : ℝ} (n : ℕ)
    (hf : HasFPowerSeriesOnBall f (ofScalars ℂ a) 0 (ENNReal.ofReal ρ))
    (hr₀ : 0 < r) (hr : r < ρ)
    (hM : ∀ z ∈ Metric.sphere (0 : ℂ) r, ‖f z‖ ≤ M) :
    ‖a n‖ ≤ M / r ^ n := sorry
