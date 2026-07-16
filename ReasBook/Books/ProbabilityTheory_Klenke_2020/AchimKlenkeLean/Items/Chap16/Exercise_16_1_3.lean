import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap16.Theorem_16_14

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped MeasureTheory

noncomputable section

namespace MeasureTheory.ProbabilityMeasure

-- Proof sketch: use the subordinator Lévy--Khinchin representation from Theorem 16.14 to split
-- the law into the deterministic drift part `α` and a jump contribution supported in `[0, ∞)`.
-- Show first that every interval `[0, x)` with `x < α` has zero mass, and then prove that any
-- `x > α` receives positive mass by isolating the event that the jump part is sufficiently small.
/-- Exercise 16.1.3 in owner-abstraction form: the drift parameter is the essential infimum of
the identity map under the law `μ`. -/
theorem HasSubordinatorLevyKhinchinRepresentation.drift_eq_essInf
    {μ : ProbabilityMeasure NNReal} {α : NNReal} {ν : Measure NNReal}
    (hrep : HasSubordinatorLevyKhinchinRepresentation μ α ν) :
    α = essInf id (μ : Measure NNReal) := sorry

/-- Exercise 16.1.3: under a Lévy--Khinchin representation on `[0, ∞)`, the drift parameter `α`
is the supremum of the null initial intervals `[0, x)` of the law `μ`. On `NNReal`, `[0, x)` is
represented by `Set.Iio x`. -/
theorem HasSubordinatorLevyKhinchinRepresentation.drift_eq_sSup_null_initial_interval
    {μ : ProbabilityMeasure NNReal} {α : NNReal} {ν : Measure NNReal}
    (hrep : HasSubordinatorLevyKhinchinRepresentation μ α ν) :
    α = sSup {x : NNReal | (μ : Measure NNReal) (Set.Iio x) = 0} := by
  simpa [essInf_eq_sSup] using hrep.drift_eq_essInf

end MeasureTheory.ProbabilityMeasure
