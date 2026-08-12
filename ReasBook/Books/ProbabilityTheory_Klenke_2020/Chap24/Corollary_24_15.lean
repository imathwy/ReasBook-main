import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- A Poisson point process with intensity `μ`, encoded through the characteristic-function
identity of Theorem 24.14 for stochastic integrals of integrable real test functions. -/
def HasPoissonPointProcessCharacteristicFunction
    (P : ProbabilityMeasure Ω) (X : Ω → Measure E) (μ : Measure E) : Prop :=
  ∀ ⦃f : E → ℝ⦄, Integrable f μ →
    ∀ t : ℝ,
      ∫ ω, Complex.exp ((((t * ∫ x, f x ∂ X ω) : ℝ) : ℂ) * Complex.I) ∂(P : Measure Ω) =
        Complex.exp (∫ x, (Complex.exp ((((t * f x) : ℝ) : ℂ) * Complex.I) - 1) ∂μ)

-- Proof sketch: unfold `HasPoissonPointProcessCharacteristicFunction`; this is exactly the
-- characteristic-function
-- formula from Theorem 24.14 written as a predicate on the random measure `X`.
/-- Unfolding `HasPoissonPointProcessCharacteristicFunction P X μ` gives the
characteristic-function formula for stochastic integrals against the Poisson point process `X`
with intensity `μ`. -/
theorem hasPoissonPointProcessCharacteristicFunction_iff
    (P : ProbabilityMeasure Ω) (X : Ω → Measure E) (μ : Measure E) :
    HasPoissonPointProcessCharacteristicFunction P X μ ↔
      ∀ ⦃f : E → ℝ⦄, Integrable f μ →
        ∀ t : ℝ,
          ∫ ω, Complex.exp ((((t * ∫ x, f x ∂ X ω) : ℝ) : ℂ) * Complex.I) ∂
              (P : Measure Ω) =
            Complex.exp (∫ x, (Complex.exp ((((t * f x) : ℝ) : ℂ) * Complex.I) - 1) ∂μ) := sorry

-- Proof sketch: apply the first-derivative-at-zero formula to the characteristic function from
-- `HasPoissonPointProcessCharacteristicFunction`, interchange differentiation and integration
-- using the `L¹(μ)` bound,
-- and evaluate the derivative of the exponential at `t = 0`.
/-- Corollary 24.15 (1): item (i). If `X` is a Poisson point process with intensity `μ` and
`f ∈ L¹(μ)`, then the expectation of the stochastic integral `∫ f dX` is `∫ f dμ`. -/
theorem poissonPointProcess_integral_expectation_eq
    (P : ProbabilityMeasure Ω) (X : Ω → Measure E) (μ : Measure E) {f : E → ℝ}
    (hX : HasPoissonPointProcessCharacteristicFunction P X μ) (hf : Integrable f μ) :
    ∫ ω, (∫ x, f x ∂ X ω) ∂(P : Measure Ω) = ∫ x, f x ∂μ := sorry

-- Proof sketch: differentiate the characteristic-function identity from
-- `HasPoissonPointProcessCharacteristicFunction`
-- twice at `t = 0`, identify the second moment of `∫ f dX`, and then subtract the square of the
-- mean from clause `(1)` to obtain the variance formula.
/-- Corollary 24.15 (2): item (ii). If `X` is a Poisson point process with intensity `μ` and
`f ∈ L²(μ) ∩ L¹(μ)`, then the variance of `∫ f dX` is `∫ f^2 dμ`. -/
theorem poissonPointProcess_integral_variance_eq
    (P : ProbabilityMeasure Ω) (X : Ω → Measure E) (μ : Measure E) {f : E → ℝ}
    (hX : HasPoissonPointProcessCharacteristicFunction P X μ) (hf_int : Integrable f μ)
    (hf_sq : MemLp f 2 μ) :
    Var[fun ω ↦ ∫ x, f x ∂ X ω; (P : Measure Ω)] = ∫ x, (f x) ^ 2 ∂μ := sorry

end ProbabilityTheory
