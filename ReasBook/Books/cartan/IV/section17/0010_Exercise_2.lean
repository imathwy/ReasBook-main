import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology

-- Domain sampling note: the primary domain here is holomorphic and meromorphic circle-average
-- formulas on discs. In this chapter the source-facing owner for holomorphicity on open sets is
-- `DifferentiableOn ℂ`, while the circle-mean and integrability owners are `Real.circleAverage`
-- and `CircleIntegrable`. The relevant chapter/mathlib declarations inspected before refining were
-- `DifferentiableOn.analyticOnNhd`,
-- `AnalyticOnNhd.circleAverage_log_norm_of_ne_zero`,
-- `circleIntegrable_log_norm_sub_const`,
-- `circleAverage_log_norm_sub_const_of_mem_closedBall`,
-- and `MeromorphicOn.circleAverage_log_norm`.

/-- Exercise 2 (1): for a holomorphic function on `|z| < R` with no zeros on `|z| ≤ r`, the mean
value of `log |g|` on the circle of radius `r`, namely `Real.circleAverage (Real.log ‖g ·‖) 0 r`,
equals `log |g(0)|`. -/
theorem log_norm_at_zero_eq_circle_average_of_zero_free
    {R r : ℝ} {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) R))
    (hr_nonneg : 0 ≤ r) (hrR : r < R)
    (hzero : ∀ z ∈ Metric.closedBall (0 : ℂ) r, g z ≠ 0) :
    Real.circleAverage (Real.log ‖g ·‖) (0 : ℂ) r = Real.log ‖g 0‖ := by
  have hg_ball : AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) R) := by
    exact hg.analyticOnNhd Metric.isOpen_ball
  have hg' : AnalyticOnNhd ℂ g (Metric.closedBall (0 : ℂ) |r|) := by
    simpa [abs_of_nonneg hr_nonneg] using hg_ball.mono (Metric.closedBall_subset_ball hrR)
  have hzero' : ∀ z ∈ Metric.closedBall (0 : ℂ) |r|, g z ≠ 0 := by
    simpa [abs_of_nonneg hr_nonneg] using hzero
  simpa [abs_of_nonneg hr_nonneg] using
    hg'.circleAverage_log_norm_of_ne_zero hzero'

/- Exercise 2 (2): this is the direct specialization of the canonical circle-integrability owner
`circleIntegrable_log_norm_sub_const` to `a = circleMap 0 r t` and `c = 0`. -/
recall circleIntegrable_log_norm_sub_const

/-- Exercise 2 (3): the circle average of the logarithmic chord kernel on `|z| = r` equals
`log r`. -/
theorem circleAverage_circle_log_chord_eq
    {r t : ℝ} :
    Real.circleAverage (Real.log ‖· - circleMap 0 r t‖) (0 : ℂ) r = Real.log r := by
  have hmem : circleMap 0 r t ∈ Metric.closedBall (0 : ℂ) |r| := by
    simp [Metric.mem_closedBall, norm_circleMap_zero]
  simpa using
    (show Real.circleAverage (Real.log ‖· - circleMap 0 r t‖) (0 : ℂ) r = Real.log r from
      circleAverage_log_norm_sub_const_of_mem_closedBall hmem)

/-- Exercise 2 (4): for a meromorphic function on `|z| < R`, the boundary integral of `log |f|`
over the circle `|z| = r` is convergent whenever `0 ≤ r < R`. -/
theorem meromorphic_circleIntegrable_log_norm_on_inner_circle
    {R r : ℝ} {f : ℂ → ℂ}
    (hf : MeromorphicOn f (Metric.ball (0 : ℂ) R))
    (hr : 0 ≤ r) (hrR : r < R) :
    CircleIntegrable (Real.log ‖f ·‖) (0 : ℂ) r := by
  have hf' : MeromorphicOn f (Metric.sphere (0 : ℂ) r) := fun z hz ↦
    hf z (Metric.sphere_subset_ball hrR hz)
  exact hf'.circleIntegrable_log_norm_of_nonneg hr

/-- Exercise 2 (5): canonical Jensen formula at the origin for a meromorphic function on `|z| < R`,
written using the divisor on the closed disc and the meromorphic trailing coefficient at `0`. This
is the mathlib-facing version of the textbook formula involving the zeros, poles, and the leading
Laurent coefficient. -/
theorem jensen_formula_at_zero
    {R r : ℝ} {f : ℂ → ℂ}
    (hf : MeromorphicOn f (Metric.ball (0 : ℂ) R))
    (hr : 0 < r) (hrR : r < R) :
    Real.circleAverage (Real.log ‖f ·‖) (0 : ℂ) r =
      ∑ᶠ u, MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) r) u * Real.log (r * ‖u‖⁻¹)
        + MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) r) (0 : ℂ) * Real.log r
        + Real.log ‖meromorphicTrailingCoeffAt f (0 : ℂ)‖ := by
  have hclosedBall : Metric.closedBall (0 : ℂ) |r| = Metric.closedBall (0 : ℂ) r := by
    simp [abs_of_pos hr]
  have hf' : MeromorphicOn f (Metric.closedBall (0 : ℂ) |r|) := by
    intro z hz
    have hz' : z ∈ Metric.closedBall (0 : ℂ) r := by
      simpa [abs_of_pos hr] using hz
    exact hf z (Metric.closedBall_subset_ball hrR hz')
  rw [← hclosedBall]
  simpa [norm_neg] using
    (show Real.circleAverage (Real.log ‖f ·‖) (0 : ℂ) r =
        ∑ᶠ u,
          MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) |r|) u * Real.log (r * ‖(0 : ℂ) - u‖⁻¹)
          + MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) |r|) (0 : ℂ) * Real.log r
          + Real.log ‖meromorphicTrailingCoeffAt f (0 : ℂ)‖ from
      MeromorphicOn.circleAverage_log_norm hr.ne' hf')
