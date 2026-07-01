import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

/-- Exercise 1.5.2: there exists a probability measure on `ℝ × Bool` for which the first
coordinate and the signed first coordinate are both Gaussian random variables, but their pair is
not a two-dimensional Gaussian random variable. -/
-- Proof sketch: take a standard Gaussian variable `Z` together with an independent Rademacher
-- sign `ε`, and set `X = Z` and `Y = εZ`. Then `Y` is again Gaussian, while `(X, Y)` is supported
-- on the two lines `y = x` and `y = -x`, so its joint law is not Gaussian.
theorem exists_gaussian_marginals_without_gaussian_pair :
    ∃ P : ProbabilityMeasure (ℝ × Bool),
      HasGaussianLaw (fun ω : ℝ × Bool ↦ ω.1) (P : Measure (ℝ × Bool)) ∧
      HasGaussianLaw (fun ω ↦ if ω.2 then ω.1 else -ω.1) (P : Measure (ℝ × Bool)) ∧
      ¬ HasGaussianLaw (fun ω ↦ (ω.1, if ω.2 then ω.1 else -ω.1)) (P : Measure (ℝ × Bool)) :=
  sorry
