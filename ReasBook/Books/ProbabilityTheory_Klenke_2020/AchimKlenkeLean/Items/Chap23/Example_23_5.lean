import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap23.Example_23_10
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap23.Theorem_23_1

-- Declarations for this item will be appended below by the statement pipeline.

namespace ProbabilityTheory

open MeasureTheory
open Set

-- `bridge/view` layer: on `(-1, 1)`, the optimizer of the Legendre transform for the symmetric
-- `{-1, 1}` law is `t = Real.artanh z`, so the variational problem reduces to the textbook
-- stationary value `z * artanh z - log (cosh (artanh z))`.
private theorem rademacher_legendreCgfRateFunction_eq_stationaryValue {z : ℝ}
    (hz : z ∈ Ioo (-1) 1) :
    legendreCgfRateFunction id
      (((1 / 2 : ENNReal) • Measure.dirac (-1 : ℝ)) +
        ((1 / 2 : ENNReal) • Measure.dirac (1 : ℝ))) z =
      ((z * Real.artanh z - Real.log (Real.cosh (Real.artanh z)) : ℝ) : EReal) :=
  sorry

-- Proof sketch: rewrite `Real.artanh z` using `Real.artanh_eq_half_log` on `[-1, 1]`, rewrite
-- `Real.cosh (Real.artanh z)` using `Real.cosh_artanh`, and simplify the resulting logarithms and
-- algebraic expression to the Bernoulli Cramér branch `bernoulliCramerRateFunction z`, whose
-- defining formula is the entropy expression from Remark 23.2.
private theorem rademacher_stationaryValue_eq_bernoulliCramerRateFunction {z : ℝ}
    (hz : z ∈ Ioo (-1) 1) :
    ((z * Real.artanh z - Real.log (Real.cosh (Real.artanh z)) : ℝ) : EReal) =
      bernoulliCramerRateFunction z :=
  sorry

/-- Example 23.5: for the symmetric `{-1, 1}`-valued law and `z ∈ (-1, 1)`, the Legendre transform
of the cumulant-generating function agrees with the chapter's Rademacher Cramér rate function. -/
theorem legendreCgfRateFunction_id_rademacherMeasure_eq_rademacherCramerRateFunction {z : ℝ}
    (hz : z ∈ Ioo (-1) 1) :
    legendreCgfRateFunction id
      (((1 / 2 : ENNReal) • Measure.dirac (-1 : ℝ)) +
        ((1 / 2 : ENNReal) • Measure.dirac (1 : ℝ))) z =
      rademacherCramerRateFunction z := by
  have hzabs : |z| < 1 := by
    simpa [mem_Ioo, abs_lt] using hz
  rw [rademacher_legendreCgfRateFunction_eq_stationaryValue hz]
  rw [rademacher_stationaryValue_eq_bernoulliCramerRateFunction hz]
  rw [rademacherCramerRateFunction_of_abs_le_one hzabs.le]

end ProbabilityTheory
