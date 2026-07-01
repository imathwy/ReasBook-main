import Mathlib
import AchimKlenkeLean.Items.Chap02.Definition_2_32
import AchimKlenkeLean.Items.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

/-- The `n`-fold additive convolution power of a measure on `ℝ`, normalized so that the zeroth
power is the Dirac mass at `0`. -/
noncomputable def compoundPoissonConvolutionPower (ν : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | n + 1 => compoundPoissonConvolutionPower ν n ∗ ν

/-- The successor convolution powers are obtained by convolving once more with the base measure
`ν`. -/
theorem compoundPoissonConvolutionPower_succ (ν : Measure ℝ) (n : ℕ) :
    compoundPoissonConvolutionPower ν (n + 1) =
      compoundPoissonConvolutionPower ν n ∗ ν := rfl

private noncomputable def compoundPoissonMeasureData (ν : Measure ℝ) [IsFiniteMeasure ν] :
    Measure ℝ :=
  Measure.sum fun n ↦
    ENNReal.ofReal (Real.exp (-ν.real Set.univ) / n.factorial) •
      compoundPoissonConvolutionPower ν n

-- Proof sketch: compute the total mass of each term using the convolution-power recursion, then
-- identify the resulting scalar series with the exponential series of total mass `ν(ℝ)`.
private theorem compoundPoissonMeasureData_isProbabilityMeasure
    (ν : Measure ℝ) [IsFiniteMeasure ν] :
    IsProbabilityMeasure (compoundPoissonMeasureData ν) := sorry

/-- Definition 16.3: The compound Poisson distribution with finite intensity measure `ν` is the
probability law on `ℝ` given by the Poisson-weighted series
`e^{-ν(ℝ)} \sum_{n=0}^\infty ν^{*n} / n!`. -/
noncomputable def compoundPoissonMeasure (ν : Measure ℝ) [IsFiniteMeasure ν] :
    ProbabilityMeasure ℝ :=
  ⟨compoundPoissonMeasureData ν, compoundPoissonMeasureData_isProbabilityMeasure ν⟩

/-- The compound Poisson measure is the Poisson-weighted sum of the convolution powers of its
intensity measure. -/
theorem compoundPoissonMeasure_def (ν : Measure ℝ) [IsFiniteMeasure ν] :
    (compoundPoissonMeasure ν : Measure ℝ) =
      Measure.sum fun n ↦
        ENNReal.ofReal (Real.exp (-ν.real Set.univ) / n.factorial) •
          compoundPoissonConvolutionPower ν n := rfl

-- Proof sketch: expand `compoundPoissonMeasure ((Real.toNNReal r) • ν)` with
-- `compoundPoissonMeasure_def`, use the bilinearity of convolution to rewrite the `n`th
-- convolution power of the scaled intensity measure as `r ^ n` times the `n`th convolution power
-- of `ν`, and simplify the total mass of the scaled measure to `r * ν(ℝ)`.
/-- The textbook parameterization by a rate `r` and a jump measure `ν` is the owner
compound-Poisson law for the finite intensity measure `r • ν`. -/
theorem compoundPoissonMeasure_smul_eq (r : ℝ) (hr : 0 ≤ r) (ν : Measure ℝ)
    [IsFiniteMeasure ν] :
    (compoundPoissonMeasure ((Real.toNNReal r) • ν) : Measure ℝ) =
      Measure.sum fun n ↦
        ENNReal.ofReal (Real.exp (-r * ν.real Set.univ) * r ^ n / n.factorial) •
          compoundPoissonConvolutionPower ν n := sorry

-- Proof sketch: expand `compoundPoissonMeasure` as a weighted series, use linearity of the
-- characteristic function on countable measure sums and multiplicativity under convolution, and
-- sum the resulting exponential series.
/-- The characteristic function of the compound Poisson measure is
`exp (∫ (exp (i t x) - 1) dν)`. -/
theorem charFun_compoundPoissonMeasure (ν : Measure ℝ) [IsFiniteMeasure ν] (t : ℝ) :
    charFun (compoundPoissonMeasure ν : Measure ℝ) t =
      Complex.exp (∫ x, (Complex.exp (t * x * Complex.I) - 1) ∂ν) := sorry

-- Proof sketch: compare the characteristic functions of both sides using
-- `charFun_compoundPoissonMeasure`, reduce the exponent for `μ + ν` to the sum of the separate
-- exponents, use uniqueness of characteristic functions for finite measures on `ℝ`, and then
-- pass back to bundled probability measures via extensionality of the underlying measures.
/-- Compound Poisson measures form an additive convolution semigroup in the intensity measure. -/
theorem compoundPoissonMeasure_add (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    compoundPoissonMeasure (μ + ν) = compoundPoissonMeasure μ * compoundPoissonMeasure ν := sorry

-- Proof sketch: for each `n`, apply `compoundPoissonMeasure_add` repeatedly to split the
-- intensity measure into `n + 1` equal parts, yielding an `(n + 1)`-fold convolution root.
/-- Every compound Poisson measure is infinitely divisible. -/
theorem compoundPoissonMeasure_infinitelyDivisible (ν : Measure ℝ) [IsFiniteMeasure ν] :
    ProbabilityMeasure.IsInfinitelyDivisible (compoundPoissonMeasure ν) := sorry
