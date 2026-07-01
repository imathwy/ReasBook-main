import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open FormalMultilinearSeries
open scoped ENNReal

/-- Theorem 3: a function holomorphic on the open disc `|z| < ρ` admits a scalar power series
expansion about `0` whose radius of convergence is at least `ρ`, equivalently a scalar formal power
series on that ball representing `f`. -/
-- Proof sketch: first obtain analyticity of `f` at each point of the open disc from complex
-- differentiability. Then construct the coefficients by the Cauchy integral formula on smaller
-- circles and use uniqueness of scalar power series expansions to show that these local expansions
-- glue to one series centered at `0` with radius at least `ρ`.
theorem holomorphic_on_disc_has_power_series_expansion
    {f : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) ρ)) :
    ∃ a : ℕ → ℂ, HasFPowerSeriesOnBall f (ofScalars ℂ a) 0 (ENNReal.ofReal ρ) := by
  let a : ℕ → ℂ := fun n ↦ iteratedDeriv n f 0 / n.factorial
  have hsub : ∀ {r : ℝ}, 0 < r → r < ρ →
      HasFPowerSeriesOnBall f (ofScalars ℂ a) 0 (ENNReal.ofReal r) := by
    intro r hr₀ hrρ
    let R : NNReal := Real.toNNReal r
    have hR : 0 < R := by
      simp [R, hr₀]
    have hsubset : Metric.closedBall (0 : ℂ) R ⊆ Metric.ball (0 : ℂ) ρ := by
      simpa [R, Real.toNNReal_of_nonneg hr₀.le] using
        (Metric.closedBall_subset_ball hrρ : Metric.closedBall (0 : ℂ) r ⊆ Metric.ball (0 : ℂ) ρ)
    have hp : HasFPowerSeriesOnBall f (cauchyPowerSeries f 0 R) 0 R :=
      (hf.mono hsubset).hasFPowerSeriesOnBall hR
    have hseries : cauchyPowerSeries f 0 R = ofScalars ℂ a := by
      funext n
      calc
        cauchyPowerSeries f 0 R n =
            ContinuousMultilinearMap.mkPiRing ℂ (Fin n)
              (cauchyPowerSeries f 0 R n (fun _ ↦ (1 : ℂ))) := by
          symm
          exact ContinuousMultilinearMap.mkPiRing_apply_one_eq_self _
        _ = ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (a n) := by
          congr 1
          have hfact := hp.factorial_smul (1 : ℂ) n
          rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Finset.prod_const_one, one_smul,
            nsmul_eq_mul] at hfact
          have hne : (n.factorial : ℂ) ≠ 0 := by
            exact_mod_cast n.factorial_ne_zero
          have hfact' := congrArg (fun z : ℂ ↦ ((n.factorial : ℂ)⁻¹) * z) hfact
          simpa [a, div_eq_mul_inv, hne, mul_assoc, mul_comm] using hfact'
        _ = ofScalars ℂ a n := by
          ext
          simp [FormalMultilinearSeries.ofScalars, ContinuousMultilinearMap.mkPiRing_apply,
            ContinuousMultilinearMap.mkPiAlgebraFin_apply, mul_comm]
    have hRenn : (R : ENNReal) = ENNReal.ofReal r := by
      rw [show R = Real.toNNReal r by rfl, ENNReal.ofReal_eq_coe_nnreal,
        Real.toNNReal_of_nonneg hr₀.le]
    simpa [hRenn, hseries] using hp
  refine ⟨a, ?_⟩
  refine
    { r_le := ENNReal.le_of_forall_pos_nnreal_lt fun r hr₀ hrρ ↦ ?_
      r_pos := ENNReal.ofReal_pos.2 hρ
      hasSum := ?_ }
  · have hsub' :
        HasFPowerSeriesOnBall f (ofScalars ℂ a) 0 (ENNReal.ofReal (r : ℝ)) :=
      hsub (by exact_mod_cast hr₀) (by simpa using hrρ)
    simpa using hsub'.r_le
  · intro y hy
    rcases exists_between (by simpa [mem_eball_zero_iff] using hy) with ⟨r, hyr, hrρ⟩
    exact
      (hsub (show 0 < r by exact lt_of_le_of_lt (norm_nonneg y) hyr) hrρ).hasSum
        (by simpa [mem_eball_zero_iff] using hyr)
