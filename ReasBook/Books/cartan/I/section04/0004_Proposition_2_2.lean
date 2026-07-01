import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open FormalMultilinearSeries

universe u

variable {𝕜 : Type u}

-- Proof sketch: specialize `HasFPowerSeriesOnBall.changeOrigin` to an origin-centered scalar power
-- series `ofScalars 𝕜 a`; the resulting recentered series is `(ofScalars 𝕜 a).changeOrigin x₀`,
-- and its guaranteed convergence radius is `ρ - ‖x₀‖`.
/-- Proposition 2.2: if `S` is represented on the ball of radius `ρ` around `0` by the scalar
power series `∑ aₙ Xⁿ`, then for every new center `x₀` with `‖x₀‖ < ρ`, the recentered scalar
power series converges on the ball of radius `ρ - ‖x₀‖` around `x₀` and still represents `S`. -/
theorem scalar_hasFPowerSeriesOnBall_changeOrigin
    [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {S : 𝕜 → 𝕜} {a : ℕ → 𝕜} {ρ : ℝ} {x₀ : 𝕜}
    (hS : HasFPowerSeriesOnBall S (ofScalars 𝕜 a) 0 (ENNReal.ofReal ρ))
    (hx₀ : ‖x₀‖ < ρ) :
    HasFPowerSeriesOnBall S ((ofScalars 𝕜 a).changeOrigin x₀) x₀
      (ENNReal.ofReal (ρ - ‖x₀‖)) := by
  have hx₀' : (‖x₀‖₊ : ENNReal) < ENNReal.ofReal ρ := by
    exact ENNReal.coe_lt_ofReal.2 hx₀
  simpa [ENNReal.ofReal_sub ρ (norm_nonneg x₀), Real.toNNReal_of_nonneg (norm_nonneg x₀)] using
    hS.changeOrigin hx₀'

-- Proof sketch: apply `HasFPowerSeriesOnBall.factorial_smul` to the recentered series from
-- `scalar_hasFPowerSeriesOnBall_changeOrigin` with the diagonal vector `(1, ..., 1)`, then rewrite
-- the resulting scalar multilinear coefficient as `.coeff`.
/-- Helper for Proposition 2.2: the coefficients of the recentered scalar series are the
normalized iterated derivatives of `S` at the new center. -/
theorem scalar_changeOrigin_coeff_eq_iteratedDeriv_div_factorial
    [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [CharZero 𝕜]
    {S : 𝕜 → 𝕜} {a : ℕ → 𝕜} {ρ : ℝ} {x₀ : 𝕜}
    (hS : HasFPowerSeriesOnBall S (ofScalars 𝕜 a) 0 (ENNReal.ofReal ρ))
    (hx₀ : ‖x₀‖ < ρ) (n : ℕ) :
    ((ofScalars 𝕜 a).changeOrigin x₀).coeff n = iteratedDeriv n S x₀ / n.factorial := by
  have hchangeBall := scalar_hasFPowerSeriesOnBall_changeOrigin hS hx₀
  have hTaylor :
      HasFPowerSeriesAt S
        (ofScalars 𝕜 (fun m ↦ iteratedDeriv m S x₀ / m.factorial)) x₀ :=
    hchangeBall.analyticAt.hasFPowerSeriesAt
  have hseries :
      (ofScalars 𝕜 a).changeOrigin x₀ =
        ofScalars 𝕜 (fun m ↦ iteratedDeriv m S x₀ / m.factorial) :=
    hchangeBall.hasFPowerSeriesAt.eq_formalMultilinearSeries hTaylor
  simpa [coeff_ofScalars] using congrArg (fun p ↦ p.coeff n) hseries

-- Proof sketch: the previous theorem gives a convergent scalar power series for `S` around `x₀`
-- on the ball of radius `ρ - ‖x₀‖`; evaluate its sum at `x - x₀` and rewrite the coefficients
-- using `scalar_changeOrigin_coeff_eq_iteratedDeriv_div_factorial`.
/-- Helper for Proposition 2.2: the recentered Taylor series of `S` about `x₀` is the usual
series with coefficients `S⁽ⁿ⁾(x₀) / n!` on the ball `‖x - x₀‖ < ρ - ‖x₀‖`. -/
theorem scalar_taylor_expansion_eq_tsum_iteratedDeriv
    [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [CharZero 𝕜]
    {S : 𝕜 → 𝕜} {a : ℕ → 𝕜} {ρ : ℝ} {x₀ x : 𝕜}
    (hS : HasFPowerSeriesOnBall S (ofScalars 𝕜 a) 0 (ENNReal.ofReal ρ))
    (hx₀ : ‖x₀‖ < ρ)
    (hx : ‖x - x₀‖ < ρ - ‖x₀‖) :
    S x = ∑' n : ℕ, (iteratedDeriv n S x₀ / n.factorial) * (x - x₀) ^ n := by
  have hchange : HasFPowerSeriesOnBall S ((ofScalars 𝕜 a).changeOrigin x₀) x₀
      (ENNReal.ofReal (ρ - ‖x₀‖)) :=
    scalar_hasFPowerSeriesOnBall_changeOrigin hS hx₀
  have hx' : x ∈ Metric.eball x₀ (ENNReal.ofReal (ρ - ‖x₀‖)) := by
    simpa [Metric.mem_eball, dist_eq_norm] using hx
  refine (hchange.hasSum_sub hx').tsum_eq.symm.trans ?_
  refine tsum_congr fun n ↦ ?_
  rw [apply_eq_pow_smul_coeff, scalar_changeOrigin_coeff_eq_iteratedDeriv_div_factorial hS hx₀]
  simp [smul_eq_mul, mul_comm]
