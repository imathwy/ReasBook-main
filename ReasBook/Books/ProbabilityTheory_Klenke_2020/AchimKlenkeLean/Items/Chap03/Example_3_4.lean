import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap01.Example_1_105

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory unitInterval NNReal

/-- The probability generating series of a measure on `ℕ`, evaluated at a real point `z`. -/
noncomputable def probabilityGeneratingSeries (μ : Measure ℕ) (z : ℝ) : ℝ :=
  ∑' n : ℕ, (μ {n}).toReal * z ^ n

/-- The positive convolution powers of a measure on `ℕ`, indexed so that `1` is the original
measure. -/
noncomputable def measureConvolutionPower (μ : Measure ℕ) (n : ℕ+) : Measure ℕ :=
  (fun ν : Measure ℕ ↦ ν ∗ μ)^[n.natPred] μ

/-- The probability generating function of the binomial law is `(p z + (1 - p))^n`. -/
theorem example_3_4_binomial_pgf (n : ℕ) (p : I) (z : ℝ) :
    probabilityGeneratingSeries (binomial n p) z = (p * z + (1 - p)) ^ n := sorry

/-- Binomial laws with a common success probability are stable under convolution. -/
theorem example_3_4_binomial_conv (m n : ℕ) (p : I) :
    binomial m p ∗ binomial n p = binomial (m + n) p := sorry

/-- The probability generating function of the Poisson law with rate `lam` is
`exp (lam * (z - 1))`. -/
theorem example_3_4_poisson_pgf (lam : ℝ≥0) (z : ℝ) :
    probabilityGeneratingSeries (poissonMeasure lam) z = Real.exp (lam * (z - 1)) := sorry

/-- Poisson laws are stable under convolution, with rates adding. -/
theorem example_3_4_poisson_conv (lam mu : ℝ≥0) :
    poissonMeasure lam ∗ poissonMeasure mu = poissonMeasure (lam + mu) := sorry

/-- The probability generating function of the geometric law is `p / (1 - (1 - p) * z)` on
`[0,1]`. -/
theorem example_3_4_geometric_pgf {p : ℝ} (hp : 0 < p) (hp_le_one : p ≤ 1) {z : ℝ}
    (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    probabilityGeneratingSeries
      (geometricMeasure (⟨p, hp.le, hp_le_one⟩ : unitInterval)) z =
        p / (1 - (1 - p) * z) := sorry

/-- The `n`th positive convolution power of the geometric law has the negative binomial point
masses from the example. -/
theorem example_3_4_geometric_conv_power_apply {p : ℝ} (hp : 0 < p) (hp_le_one : p ≤ 1)
    (n : ℕ+) (k : ℕ) :
    measureConvolutionPower
      (geometricMeasure (⟨p, hp.le, hp_le_one⟩ : unitInterval)) n {k} =
      ENNReal.ofReal (negativeBinomialMass ((n : ℕ) : ℝ) p k) := sorry

-- Proof sketch: apply the closed formulas for the singleton masses of the binomial, Poisson,
-- and geometric laws, compute the corresponding generating series, and use the convolution law
-- for sums of independent `ℕ`-valued random variables.
/-- Example 3.4: Binomial, Poisson, and geometric laws have the generating functions and
convolution identities displayed in the example, with geometric convolution powers given by the
negative binomial mass formula. -/
theorem example_3_4 :
    (∀ (n : ℕ) (p : I) (z : ℝ),
      probabilityGeneratingSeries (binomial n p) z = (p * z + (1 - p)) ^ n) ∧
      (∀ (m n : ℕ) (p : I),
        binomial m p ∗ binomial n p = binomial (m + n) p) ∧
      (∀ (lam : ℝ≥0) (z : ℝ),
        probabilityGeneratingSeries (poissonMeasure lam) z = Real.exp (lam * (z - 1))) ∧
      (∀ lam mu : ℝ≥0,
        poissonMeasure lam ∗ poissonMeasure mu = poissonMeasure (lam + mu)) ∧
      (∀ {p : ℝ} (hp : 0 < p) (hp_le_one : p ≤ 1) {z : ℝ},
        z ∈ Set.Icc (0 : ℝ) 1 →
          probabilityGeneratingSeries
            (geometricMeasure (⟨p, hp.le, hp_le_one⟩ : unitInterval)) z =
            p / (1 - (1 - p) * z)) ∧
      (∀ {p : ℝ} (hp : 0 < p) (hp_le_one : p ≤ 1) (n : ℕ+) (k : ℕ),
        measureConvolutionPower
          (geometricMeasure (⟨p, hp.le, hp_le_one⟩ : unitInterval)) n {k} =
          ENNReal.ofReal (negativeBinomialMass ((n : ℕ) : ℝ) p k)) := by
  refine ⟨example_3_4_binomial_pgf, example_3_4_binomial_conv, example_3_4_poisson_pgf,
    example_3_4_poisson_conv, ?_, example_3_4_geometric_conv_power_apply⟩
  intro p hp hp_le_one z hz
  exact example_3_4_geometric_pgf hp hp_le_one hz
