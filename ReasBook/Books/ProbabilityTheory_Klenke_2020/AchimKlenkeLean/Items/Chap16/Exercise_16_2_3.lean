import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap01.Definition_1_59
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap16.Definition_16_20
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap23.Example_23_10

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Filter
open MeasureTheory.ProbabilityMeasure
open scoped MeasureTheory Topology

noncomputable section

universe u

private def exercise1623DistributionFormula (x : ℝ) : ℝ :=
  if 0 < x then 2 * (1 - cdf (gaussianReal (0 : ℝ) 1) (1 / Real.sqrt x)) else 0

private theorem exercise1623DistributionFormula_monotone :
    Monotone exercise1623DistributionFormula := sorry

private theorem exercise1623DistributionFormula_rightContinuous (x : ℝ) :
    ContinuousWithinAt exercise1623DistributionFormula (Set.Ici x) x := sorry

/-- The textbook distribution function `F` from Exercise 16.2.3, viewed as the canonical Chapter 1
distribution-function owner object. -/
def exercise1623DistributionFunction : StieltjesFunction ℝ where
  toFun := exercise1623DistributionFormula
  mono' := exercise1623DistributionFormula_monotone
  right_continuous' := exercise1623DistributionFormula_rightContinuous

/-- The textbook formula for the distribution function in Exercise 16.2.3. -/
@[simp] theorem exercise1623DistributionFunction_apply (x : ℝ) :
    exercise1623DistributionFunction x =
      if 0 < x then 2 * (1 - cdf (gaussianReal (0 : ℝ) 1) (1 / Real.sqrt x)) else 0 := rfl

/-- The textbook function in Exercise 16.2.3 is a distribution function in the Chapter 1 sense. -/
instance : IsDistributionFunction exercise1623DistributionFunction := sorry

-- Proof sketch: unfold `exercise1623DistributionFunction`; on the nonpositive branch the defining
-- `if` returns `0`.
/-- The textbook function `F` vanishes on `(-∞, 0]`. -/
theorem exercise1623DistributionFunction_of_nonpos
    {x : ℝ} (hx : x ≤ 0) :
    exercise1623DistributionFunction x = 0 := sorry

-- Proof sketch: use the hint to identify the law with the positive `1 / 2`-stable law having
-- Laplace transform `λ ↦ exp (-√(2λ))`, then translate strict stability into the displayed
-- convolution-scaling relation.
/-- Exercise 16.2.3 (1): the textbook function
`F(x) = 2 (1 - cdf (gaussianReal 0 1) (x^{-1/2}))` for `x > 0` and `F(x) = 0` for `x ≤ 0`
is the cumulative distribution function of a `1 / 2`-stable probability law on `ℝ`. -/
theorem exists_halfStable_measure_with_exercise1623_distributionFunction
    :
    ∃ μ : ProbabilityMeasure ℝ,
      cdf (μ : Measure ℝ) = exercise1623DistributionFunction ∧
        IsStableWithIndex μ (1 / 2 : ℝ) := sorry

-- Proof sketch: for the positive `1 / 2`-stable law the first moment is infinite, and the
-- classical heavy-tail law of large numbers implies that the Cesàro averages of an i.i.d.
-- sequence with this law fail to converge almost surely.
/-- Exercise 16.2.3 (2): if `μ` has the distribution function from Exercise 16.2.3 and
`X₀, X₁, …` are i.i.d. with law `μ`, then their Cesàro averages diverge almost surely. -/
theorem iid_exercise1623_partialAverage_ae_diverges
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : ProbabilityMeasure ℝ)
    (hμ : cdf (μ : Measure ℝ) = exercise1623DistributionFunction)
    (X : ℕ → Ω → ℝ) (h_indep : iIndepFun X P)
    (h_law : ∀ n : ℕ, HasLaw (X n) (μ : Measure ℝ) P) :
    ∀ᵐ ω ∂P, ¬ ∃ x : ℝ,
      Tendsto (fun n : ℕ+ ↦ partialRealSum X n ω / (n : ℝ)) atTop (nhds x) := sorry
