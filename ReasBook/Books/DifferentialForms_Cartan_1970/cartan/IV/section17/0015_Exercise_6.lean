import Mathlib
import DifferentialForms_Cartan_1970.IV.section17.«0014_Exercise_5»

-- Domain sampling note: in this chapter, holomorphic-on-open-set statements use the source-facing
-- owner `DifferentiableOn ℂ`, Exercise 4 provides the bridge
-- `differentiableOn_norm_rpow_isSubharmonicOn`, and Exercise 5 owns the canonical
-- `IsSubharmonicOn` circle-average continuity/monotonicity API.

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology

noncomputable section

/-- Exercise 6 (1): if `f` is holomorphic on the disc `|z| < R` and `α ≥ 0`, then
`r ↦ I_α(r)`, where in mathlib
`I_α(r) = (2π)⁻¹ ∫_0^{2π} |f (r * exp (θ I))|^α dθ`,
is `r ↦ Real.circleAverage (fun z ↦ Real.rpow ‖f z‖ α) 0 r`,
is continuous on `0 ≤ r < R`. -/
theorem circle_power_average_continuousOn
    {f : ℂ → ℂ} {R α : ℝ}
    (hα : 0 ≤ α) (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) R)) :
    ContinuousOn (fun r : ℝ ↦ Real.circleAverage (fun z ↦ Real.rpow ‖f z‖ α) 0 r)
      (Set.Ico (0 : ℝ) R) := by
  exact isSubharmonicOn_ball_circleAverage_continuous
    (differentiableOn_norm_rpow_isSubharmonicOn Metric.isOpen_ball hf hα)

/-- Exercise 6 (2): if `f` is holomorphic on the disc `|z| < R` and `α ≥ 0`, then
`r ↦ I_α(r)`, where in mathlib
`I_α(r) = (2π)⁻¹ ∫_0^{2π} |f (r * exp (θ I))|^α dθ`,
is `r ↦ Real.circleAverage (fun z ↦ Real.rpow ‖f z‖ α) 0 r`,
is monotone increasing in the broad sense on `0 ≤ r < R`. -/
theorem circle_power_average_monotoneOn
    {f : ℂ → ℂ} {R α : ℝ}
    (hα : 0 ≤ α) (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) R)) :
    MonotoneOn (fun r : ℝ ↦ Real.circleAverage (fun z ↦ Real.rpow ‖f z‖ α) 0 r)
      (Set.Ico (0 : ℝ) R) := by
  exact isSubharmonicOn_ball_circleAverage_monotone
    (differentiableOn_norm_rpow_isSubharmonicOn Metric.isOpen_ball hf hα)
