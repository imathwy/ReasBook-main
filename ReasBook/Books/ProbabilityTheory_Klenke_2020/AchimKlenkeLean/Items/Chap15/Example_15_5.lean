import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

/-- The standard log-normal law on `ℝ`, defined as the image of the standard Gaussian law under
exponentiation. -/
def standardLogNormalMeasure : Measure ℝ :=
  (gaussianReal 0 1).map Real.exp

/-- The density of the standard log-normal law on `ℝ`, extended by `0` on `(-∞, 0]`. -/
def standardLogNormalDensityReal (x : ℝ) : ℝ :=
  if 0 < x then gaussianPDFReal 0 1 (Real.log x) / x else 0

/-- The oscillatory perturbation of the standard log-normal density by the factor
`1 + α sin(2π log x)` for `α ∈ [-1, 1]`. -/
def logNormalPerturbationDensityReal (α : Set.Icc (-1 : ℝ) 1) (x : ℝ) : ℝ :=
  standardLogNormalDensityReal x * (1 + α.1 * Real.sin (2 * Real.pi * Real.log x))

/-- The measure with density `logNormalPerturbationDensityReal α` with respect to Lebesgue
measure. -/
def logNormalPerturbationMeasure (α : Set.Icc (-1 : ℝ) 1) : Measure ℝ :=
  volume.withDensity (fun x ↦ ENNReal.ofReal (logNormalPerturbationDensityReal α x))

-- Proof sketch: apply the one-dimensional change-of-variables formula to the pushforward of the
-- standard Gaussian law under `Real.exp`, which yields the textbook density
-- `x ↦ gaussianPDFReal 0 1 (log x) / x` on `(0, ∞)`.
/-- The standard log-normal law is the image of the standard Gaussian law under exponentiation,
and this image measure has density `standardLogNormalDensityReal` with respect to Lebesgue
measure. -/
theorem standardLogNormalMeasure_eq_withDensity_standardLogNormalDensityReal :
    standardLogNormalMeasure =
      volume.withDensity (fun x ↦ ENNReal.ofReal (standardLogNormalDensityReal x)) := sorry

-- Proof sketch: rewrite the integral using
-- `standardLogNormalMeasure_eq_withDensity_standardLogNormalDensityReal`, so the moment becomes
-- `E[exp(nY)]` for a standard Gaussian `Y`, and then evaluate the Gaussian moment-generating
-- function at `n`.
/-- The `n`th moment of the standard log-normal law equals `exp (n^2 / 2)`. -/
theorem standardLogNormalMeasure_moment (n : ℕ) :
    moment id n standardLogNormalMeasure = Real.exp (((n : ℝ) ^ 2) / 2) := sorry

-- Proof sketch: substitute `y = log x - n` in the integral. After simplifying, the remaining
-- Gaussian-weighted integrand is odd because `sin (2π (y + n)) = sin (2π y)`, so the integral
-- vanishes.
/-- The oscillatory correction term used to build the Stieltjes class has vanishing moments. -/
theorem logNormalOscillatoryMoment_eq_zero (n : ℕ) :
    ∫ x, x ^ n * standardLogNormalDensityReal x * Real.sin (2 * Real.pi * Real.log x) = 0 := sorry

-- Proof sketch: the bound `|α| ≤ 1` implies that the oscillatory factor
-- `1 + α sin (2π log x)` is nonnegative, so `logNormalPerturbationMeasure α` is a probability
-- measure. The moment identity follows by expanding the perturbed density and using
-- `logNormalOscillatoryMoment_eq_zero` to kill the oscillatory contribution.
/-- Example 15.5: for every `α ∈ [-1, 1]`, the perturbed log-normal density defines a probability
measure whose moments agree with those of the standard log-normal law. -/
theorem logNormalPerturbationMeasure_isProbabilityMeasure_and_sameMoments
    (α : Set.Icc (-1 : ℝ) 1) :
    IsProbabilityMeasure (logNormalPerturbationMeasure α) ∧
      ∀ n : ℕ,
        moment id n (logNormalPerturbationMeasure α) =
          moment id n standardLogNormalMeasure := sorry
