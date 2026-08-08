import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory unitInterval

noncomputable section

/- The one-trial binomial PMF is the Bernoulli PMF. -/
recall PMF.binomial_one_eq_bernoulli

/- The expectation of the Bernoulli PMF on `Bool`, pushed forward by `true ↦ 1`, `false ↦ 0`,
is `PMF.bernoulli_expectation`. -/
recall PMF.bernoulli_expectation

-- Proof sketch: identify `Bin(ℝ, n, p)` as the law of a sum of `n` independent Bernoulli
-- variables, then use additivity of expectation and variance for independent summands.
/-- Example 5.9 (2): Item (ii). The binomial law with parameters `n` and `p` has mean `pn` and
variance `p(1-p)n`. -/
theorem binomial_mean_variance (n : ℕ) (p : I) :
    (∫ x, x ∂Bin(ℝ, n, p)) = p * n ∧
      Var[id; Bin(ℝ, n, p)] = p * (1 - p) * n := sorry

-- Proof sketch: compute the mean from the two-point Bernoulli law on `ℝ`, then evaluate the
-- variance either from the centered-square formula or from the identity `Var[X] = E[X²] - E[X]²`.
/-- Example 5.9 (1): Item (i). The Bernoulli law `Ber_p`, viewed as a probability measure on
`ℝ` via the canonical one-trial binomial law `Bin(ℝ, 1, p)`, has mean `p` and variance
`p(1-p)`. -/
theorem bernoulliReal_mean_variance (p : I) :
    (∫ x, x ∂Bin(ℝ, 1, p)) = p ∧
      Var[id; Bin(ℝ, 1, p)] = p * (1 - p) := by
  simpa using binomial_mean_variance 1 p

/- The Gaussian mean formula is `integral_id_gaussianReal`. -/
recall integral_id_gaussianReal

/- The Gaussian variance formula is `variance_id_gaussianReal`. -/
recall variance_id_gaussianReal

-- Proof sketch: this is exactly the pair of canonical Gaussian moment formulas
-- `integral_id_gaussianReal` and `variance_id_gaussianReal`.
/-- Example 5.9 (3): Item (iii). The Gaussian distribution `N_{μ,σ²}` has mean `μ` and variance
`σ²`. -/
theorem gaussianReal_mean_variance (μ σ2 : ℝ) (hσ2 : 0 < σ2) :
    (∫ x, x ∂gaussianReal μ ⟨σ2, hσ2.le⟩) = μ ∧
      Var[id; gaussianReal μ ⟨σ2, hσ2.le⟩] = σ2 := by
  exact ⟨integral_id_gaussianReal, variance_id_gaussianReal⟩

-- Proof sketch: integrate `x` and `(x - 1 / θ)^2` against the exponential density
-- `θ * exp (-θx)` on `[0, ∞)`, or equivalently reduce to the corresponding gamma-moment formulas
-- for shape `1`.
/-- Example 5.9 (4): Item (iv). The exponential distribution with rate `θ > 0` has mean `1 / θ`
and variance `1 / θ²`. -/
theorem expMeasure_mean_variance (θ : ℝ) (hθ : 0 < θ) :
    (∫ x, x ∂expMeasure θ) = 1 / θ ∧
      Var[id; expMeasure θ] = 1 / θ ^ 2 := sorry
