import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap16.Exercise_16_1_2

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

noncomputable section

namespace MeasureTheory.ProbabilityMeasure

/-- The textbook density `x ↦ (1 - cos x) / (π x^2)`. -/
noncomputable def cosineDensity (x : ℝ) : ℝ :=
  (1 - Real.cos x) / (Real.pi * x ^ 2)

/-- The measure on `ℝ` with density `x ↦ (1 - cos x) / (π x^2)` with respect to Lebesgue
measure. -/
noncomputable def cosineDensityMeasure : Measure ℝ :=
  volume.withDensity (fun x ↦ ENNReal.ofReal (cosineDensity x))

/-- The density measure `cosineDensityMeasure` has total mass `1`. -/
instance cosineDensityMeasure_isProbabilityMeasure :
    IsProbabilityMeasure cosineDensityMeasure := sorry

/-- The probability distribution on `ℝ` with density `x ↦ (1 - cos x) / (π x^2)`. -/
noncomputable def cosineDensityProbabilityMeasure : ProbabilityMeasure ℝ :=
  ⟨cosineDensityMeasure, inferInstance⟩

-- Proof sketch: compute the Fourier transform of `cosineDensityMeasure`; it is the triangular
-- function `t ↦ max (1 - |t|) 0`, which vanishes at `t = 1`.
/-- The characteristic function of `cosineDensityProbabilityMeasure` vanishes at `t = 1`. -/
theorem charFun_cosineDensityProbabilityMeasure_one :
    charFun (cosineDensityProbabilityMeasure : Measure ℝ) (1 : ℝ) = 0 := sorry

-- Proof sketch: if the law were infinitely divisible, then the owner-level nonvanishing theorem
-- `charFun_ne_zero_of_isInfinitelyDivisible` from Exercise 16.1.2 would force its characteristic
-- function to be
-- nonzero at every real argument, contradicting `charFun_cosineDensityProbabilityMeasure_one`.
/-- Exercise 16.2.2: the probability distribution on `ℝ` with density
`x ↦ (1 - cos x) / (π x^2)` is not infinitely divisible. -/
theorem cosineDensityProbabilityMeasure_not_isInfinitelyDivisible :
    ¬ IsInfinitelyDivisible cosineDensityProbabilityMeasure := by
  intro hμ
  exact (charFun_ne_zero_of_isInfinitelyDivisible hμ 1)
    charFun_cosineDensityProbabilityMeasure_one

end MeasureTheory.ProbabilityMeasure
