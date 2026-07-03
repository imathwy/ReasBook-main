import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_23_1_1 (from Items/Chap23) -/
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

/-! ### Theorem_23_1 (from Items/Chap23) -/
open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The Rademacher Cramér rate function from Theorem 23.1: it is the Bernoulli Cramér rate on
`[-1, 1]` and `∞` outside that interval. -/
def rademacherCramerRateFunction (x : ℝ) : EReal :=
  if |x| ≤ 1 then (bernoulliCramerRateFunction x : EReal) else ⊤

-- Proof sketch: under `|x| ≤ 1`, the defining `if` takes the finite Bernoulli branch from
-- `Remark 23.2`.
/-- On `[-1, 1]`, the Rademacher Cramér rate function agrees with the Bernoulli Cramér branch from
`Remark 23.2`. -/
theorem rademacherCramerRateFunction_of_abs_le_one {x : ℝ} (hx : |x| ≤ 1) :
    rademacherCramerRateFunction x = bernoulliCramerRateFunction x := by
  simp [rademacherCramerRateFunction, hx]

-- Proof sketch: combine `rademacherCramerRateFunction_of_abs_le_one` with the defining equation of
-- `bernoulliCramerRateFunction` and rewrite the division by `2` into the textbook entropy
-- expression on `[-1,1]`.
/-- On `[-1, 1]`, the rate in Theorem 23.1 is given by the explicit entropy formula from
`Remark 23.2`. -/
theorem rademacher_largeDeviationRate_of_abs_le_one {x : ℝ} (hx : |x| ≤ 1) :
    rademacherCramerRateFunction x =
      ((1 + x) / 2) * Real.log (1 + x) + ((1 - x) / 2) * Real.log (1 - x) := sorry

variable {P : Measure Ω} {X : ℕ → Ω → ℝ}

-- Proof sketch: combine the i.i.d. Rademacher hypotheses with the exact binomial-tail formula for
-- `partialSum X n`, estimate the tail by the maximal binomial coefficient, and then apply
-- Stirling's formula to identify the exponential rate as `rademacherCramerRateFunction`.
/-- Theorem 23.1: for an i.i.d. Rademacher sequence, the upper-tail probabilities of the partial
sums satisfy Cramér's theorem. Using the `0`-based partial sums `partialSum X n = X₀ + ⋯ + Xₙ₋₁`,
the logarithmic asymptotic of `P[Sₙ ≥ x n]` converges in `EReal` to the negative of the
Rademacher Cramér rate function. -/
theorem rademacher_partialSum_largeDeviation_upperTail
    (hX_iid : IsIID X P)
    (hX0_law :
      HasLaw (X 0)
        ((1 / 2 : ENNReal) • Measure.dirac (-1) +
          (1 / 2 : ENNReal) • Measure.dirac 1)
        P)
    {x : ℝ} (hx : 0 ≤ x) :
    Tendsto
      (fun n : ℕ ↦ ENNReal.log (P {ω | x * n ≤ partialSum X n ω}) / n)
      atTop
      (𝓝 (-rademacherCramerRateFunction x)) := sorry

end ProbabilityTheory
