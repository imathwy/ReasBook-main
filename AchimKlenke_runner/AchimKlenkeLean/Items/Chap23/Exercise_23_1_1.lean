import Mathlib
import AchimKlenkeLean.Items.Chap23.Theorem_23_11

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory

noncomputable section

/-- The normalizing constant
`c = ∫ exp (-|x|) / (1 + |x|^3) dx`
appearing in Exercise 23.1.1. -/
noncomputable def exercise2311NormalizationConstant : ℝ :=
  ∫ x : ℝ, Real.exp (-|x|) / (1 + |x| ^ (3 : ℕ)) ∂volume

/-- The textbook density
`x ↦ c⁻¹ exp (-|x|) / (1 + |x|^3)`
from Exercise 23.1.1. -/
noncomputable def exercise2311Density (x : ℝ) : ℝ :=
  exercise2311NormalizationConstant⁻¹ * Real.exp (-|x|) / (1 + |x| ^ (3 : ℕ))

/-- The probability law on `ℝ` whose density is
`x ↦ c⁻¹ exp (-|x|) / (1 + |x|^3)` with respect to Lebesgue measure. -/
noncomputable def exercise2311Measure : Measure ℝ :=
  volume.withDensity (fun x ↦ ENNReal.ofReal (exercise2311Density x))

-- Proof sketch: the density is nonnegative and integrates to `1` by the choice of the
-- normalizing constant `exercise2311NormalizationConstant`, so the weighted Lebesgue measure is a
-- probability measure.
/-- The law defined by `exercise2311Measure` is a probability measure. -/
theorem exercise2311Measure_isProbabilityMeasure :
    IsProbabilityMeasure exercise2311Measure := sorry

/-- `exercise2311Measure` carries its canonical probability-measure instance. -/
instance : IsProbabilityMeasure exercise2311Measure :=
  exercise2311Measure_isProbabilityMeasure

-- Proof sketch: for this density, the positive tail of `exp (t x)` is controlled by
-- `exp ((t - 1) x) / x^3` and the negative tail by `exp (-(t + 1) x) / x^3`; both are integrable
-- exactly for `t ∈ [-1, 1]`, and the boundary values `t = ±1` remain integrable because
-- `x ↦ x⁻³` is integrable at infinity.
/-- The exponential-integrability domain for the law of Exercise 23.1.1 is exactly `[-1, 1]`. -/
theorem exercise2311_integrableExpSet :
    integrableExpSet id exercise2311Measure = Icc (-1 : ℝ) 1 := sorry

-- Proof sketch: specialize the chapter owner theorem
-- `extendedLogMomentGeneratingFunction_eq_cgf_of_mem_integrableExpSet` to `id` and
-- `exercise2311Measure`.
/-- On its effective domain, the extended logarithmic moment-generating function of
Exercise 23.1.1 agrees with the ordinary cumulant-generating function `cgf`. -/
theorem exercise2311LogMomentGeneratingFunction_eq_cgf_of_mem_integrableExpSet {t : ℝ}
    (ht : t ∈ integrableExpSet id exercise2311Measure) :
    Λ(id; exercise2311Measure) t = (cgf id exercise2311Measure t : EReal) := by
  simpa using
    extendedLogMomentGeneratingFunction_eq_cgf_of_mem_integrableExpSet
      id exercise2311Measure ht

-- Proof sketch: specialize the chapter owner theorem
-- `extendedLogMomentGeneratingFunction_eq_top_of_not_mem_integrableExpSet` to `id` and
-- `exercise2311Measure`.
/-- Outside its effective domain, the extended logarithmic moment-generating function of
Exercise 23.1.1 is `⊤`. -/
theorem exercise2311LogMomentGeneratingFunction_eq_top_of_not_mem_integrableExpSet {t : ℝ}
    (ht : t ∉ integrableExpSet id exercise2311Measure) :
    Λ(id; exercise2311Measure) t = ⊤ := by
  simpa using
    extendedLogMomentGeneratingFunction_eq_top_of_not_mem_integrableExpSet
      id exercise2311Measure ht

-- Proof sketch: the density is even, so replacing `x` by `-x` leaves the law invariant and turns
-- the exponential moment at `t` into the exponential moment at `-t`. Taking logarithms preserves
-- the resulting symmetry.
/-- The logarithmic moment-generating function of Exercise 23.1.1 is even. -/
theorem exercise2311LogMomentGeneratingFunction_neg_eq (t : ℝ) :
    Λ(id; exercise2311Measure) (-t) = Λ(id; exercise2311Measure) t := sorry

-- Proof sketch: because `exercise2311Measure` is a probability measure, the moment-generating
-- function at `t = 0` is `1`; hence its logarithm is `0`.
/-- At the origin, the logarithmic moment-generating function of Exercise 23.1.1 equals `0`. -/
theorem exercise2311LogMomentGeneratingFunction_zero :
    Λ(id; exercise2311Measure) 0 = 0 := sorry

-- Proof sketch: on `[-1, 1]`, identify `Λ` with `cgf id exercise2311Measure` and use the tail
-- bounds above plus dominated convergence to obtain continuity up to the endpoints. Global
-- continuity fails because `Λ (±1)` is finite while `Λ t = ⊤` immediately outside the interval.
/-- Exercise 23.1.1: the logarithmic moment-generating function for the density
`x ↦ c⁻¹ exp (-|x|) / (1 + |x|^3)` is continuous on its effective domain `[-1, 1]`, but it is not
continuous on all of `ℝ` because it jumps to `⊤` outside that interval. -/
theorem exercise2311LogMomentGeneratingFunction_continuity_answer :
    ContinuousOn (Λ(id; exercise2311Measure)) (integrableExpSet id exercise2311Measure) ∧
      ¬ Continuous (Λ(id; exercise2311Measure)) := sorry
