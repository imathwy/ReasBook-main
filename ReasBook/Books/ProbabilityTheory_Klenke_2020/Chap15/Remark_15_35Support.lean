import Mathlib
import ProbabilityTheory_Klenke_2020.Chap02.Definition_2_14

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

namespace Remark1535Support

/-- Helper for Remark 15.35: the characteristic-function differentiability criterion is equivalent
to the Feller tail condition together with convergence of the textbook truncated first moments. -/
theorem hasDerivAtCharFunZeroIffTendstoTailAndTruncatedMean
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (m : ℝ) :
    HasDerivAt (charFun μ) ((m : ℂ) * Complex.I) 0 ↔
      Tendsto (fun x ↦ x * μ.real {y : ℝ | x < |y|}) atTop (𝓝 0) ∧
        Tendsto (fun x ↦ ∫ y in Set.Icc (-x) x, y ∂μ) atTop (𝓝 m) := by
  sorry

end Remark1535Support
