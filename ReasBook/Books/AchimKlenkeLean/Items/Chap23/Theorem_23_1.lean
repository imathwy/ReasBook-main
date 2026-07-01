import Mathlib
import AchimKlenkeLean.Items.Chap02.Definition_2_14
import AchimKlenkeLean.Items.Chap05.Theorem_5_28
import AchimKlenkeLean.Items.Chap23.Remark_23_2

-- Declarations for this item will be appended below by the statement pipeline.

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
