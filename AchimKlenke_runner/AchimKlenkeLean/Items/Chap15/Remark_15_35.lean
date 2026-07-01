import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped Topology

-- Proof sketch: compare the difference quotient of `charFun μ` at `0` with the truncated first
-- moment on `[-x, x]`, split the complement into tail contributions, and use the quoted
-- asymptotic criterion for the existence of the first derivative of a characteristic function.
/-- Remark 15.35: for a real probability law `μ`, the characteristic function is differentiable at
`0` with derivative `(m : ℂ) * Complex.I` if and only if the tail term
`x * μ.real {y | x < |y|}` tends to `0` and the truncated first moments on `[-x, x]` converge
to `m`. -/
theorem hasDerivAt_charFun_zero_iff_tendsto_tail_and_truncated_mean
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (m : ℝ) :
    HasDerivAt (charFun μ) ((m : ℂ) * Complex.I) 0 ↔
      Tendsto (fun x ↦ x * μ.real {y : ℝ | x < |y|}) atTop (𝓝 0) ∧
        Tendsto (fun x ↦ ∫ y in Set.Icc (-x) x, y ∂μ) atTop (𝓝 m) := sorry
