import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap16.Remark_16_23
import ProbabilityTheory_Klenke_2020.Items.Chap16.Theorem_16_22
import ProbabilityTheory_Klenke_2020.Items.Chap16.Theorem_16_28

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

namespace MeasureTheory.ProbabilityMeasure

/-- The truncated second-moment function `U(x) = E[min(X^2, x^2)]` attached to a real probability
law `μ`. This is the intrinsic `U` appearing in Theorem 16.29. -/
def truncatedSecondMoment (μ : ProbabilityMeasure ℝ) (x : ℝ) : ℝ :=
  ∫ y, min (y ^ (2 : ℕ)) (x ^ (2 : ℕ)) ∂(μ : Measure ℝ)

/-- A real probability law lies in the domain of attraction of a stable law with index `α` if it
lies in the domain of attraction of some broadly stable probability law with that index. This is
the chapter owner for the stable domain-of-attraction notion used in Theorem 16.29. -/
def IsInDomainOfAttractionOfStableWithIndex (ν : ProbabilityMeasure ℝ) (α : ℝ) : Prop :=
  ∃ μ : ProbabilityMeasure ℝ, ν ∈ domainOfAttraction μ ∧ IsStableInBroadSenseWithIndex μ α

-- Proof sketch: unfold `IsInDomainOfAttractionOfStableWithIndex` and return the stable limiting
-- law appearing in its existential definition.
/-- Any law in the domain of attraction of a stable law with index `α` admits a stable limiting
law of index `α`. -/
theorem IsInDomainOfAttractionOfStableWithIndex.exists_stable_limit
    {ν : ProbabilityMeasure ℝ} {α : ℝ} (hν : IsInDomainOfAttractionOfStableWithIndex ν α) :
    ∃ μ : ProbabilityMeasure ℝ, ν ∈ domainOfAttraction μ ∧ IsStableInBroadSenseWithIndex μ α :=
  hν

/-- The textbook centering sequence in Theorem 16.29, split into the four cases
`α ∈ (0, 1)`, `α = 2` with finite variance and zero mean, `α ∈ (1, 2]`, and `α = 1`. The source's
display `bₙ ≡ 0` in case (i) is interpreted as the centering sequence `dₙ ≡ 0`. -/
def StableDomainAttractionCentering
    (PX : ProbabilityMeasure ℝ) (α : ℝ) (a d : ℕ+ → ℝ) : Prop :=
  (α ∈ Set.Ioo (0 : ℝ) 1 ∧ ∀ n : ℕ+, d n = 0) ∨
    (α = 2 ∧ Integrable (fun x : ℝ ↦ x ^ (2 : ℕ)) (PX : Measure ℝ) ∧
      (∫ x, x ∂(PX : Measure ℝ)) = 0 ∧
      ∀ n : ℕ+, d n = 0) ∨
    (α ∈ Set.Ioc (1 : ℝ) 2 ∧
      ∀ n : ℕ+, d n = (n : ℝ) * ∫ x, x ∂(PX : Measure ℝ)) ∨
    (α = 1 ∧
      ∀ n : ℕ+, d n = (n : ℝ) * a n * ∫ x, Real.sin (x / a n) ∂(PX : Measure ℝ))

/-- The source characteristic exponent from `(16.20)` with one-sided coefficients `c⁺ = C p` and
`c⁻ = C (1 - p)`, together with the centered Gaussian branch for `α = 2`. -/
def stableLimitCharacteristicExponent (α p C : ℝ) (t : ℝ) : ℂ :=
  if α = 2 then
    (((-(C / 2) * t ^ (2 : ℕ) : ℝ) : ℂ))
  else if α = 1 then
    (((-|t| * C * (Real.pi / 2) : ℝ) : ℂ)) +
      ((((-|t| * C * Real.sign t * (2 * p - 1) * Real.log |t| : ℝ) : ℂ)) * Complex.I)
  else
    (((|t| ^ α * stableIntegralI (-α) * (C * Real.cos (Real.pi * α / 2)) : ℝ) : ℂ)) +
      ((((|t| ^ α * stableIntegralI (-α) * (C * (2 * p - 1) *
            Real.sin (Real.pi * α / 2)) : ℝ) : ℂ)) * Complex.I)

-- Proof sketch: start from the source-level stable-domain hypothesis
-- `IsInDomainOfAttractionOfStableWithIndex PX α`, use the conditional positive-tail share limit
-- when `α < 2` to identify `p`, and read the limiting law directly from the source characteristic
-- exponent `(16.20)` with coefficients `c⁺ = C p` and `c⁻ = C (1 - p)`; in the Gaussian branch
-- `α = 2`, this specializes to the centered Gaussian exponent `t ↦ -(C / 2) t²`. The displayed
-- centering sequence `dₙ` is then inserted case by case.
/-- Theorem 16.29: if `P_X` lies in the domain of attraction of an `α`-stable law, if
`C = lim n U(aₙ) / aₙ²` exists in `(0, ∞)` for the intrinsic truncated second moment
`U(x) = E[min(X², x²)]`, and if `μ` has the source characteristic function `(16.20)` with
`c⁺ = C p`, `c⁻ = C (1 - p)` in the branch `α < 2` and the centered Gaussian exponent
`t ↦ -(C / 2) t²` when `α = 2`, then the centered normalized convolution powers of `P_X`
converge weakly to `μ` for the textbook centering sequence `dₙ`. -/
theorem tendsto_centeredNormalizedConvolutionLaw_of_stable_domain_of_attraction
    (PX μ : ProbabilityMeasure ℝ) {α p C : ℝ} (a d : ℕ+ → ℝ)
    (hPX : IsInDomainOfAttractionOfStableWithIndex PX α)
    (hμ :
      ∀ t : ℝ, charFun μ t = Complex.exp (stableLimitCharacteristicExponent α p C t))
    (hp_share : α < 2 →
      Tendsto (fun x : ℝ ↦ rightTail PX x / absTail PX x) atTop (𝓝 p))
    (ha : ∀ n : ℕ+, 0 < a n)
    (hC : Tendsto
      (fun n : ℕ+ ↦
        (n : ℝ) * truncatedSecondMoment PX (a n) / (a n) ^ (2 : ℕ))
      atTop
      (𝓝 C))
    (hC_pos : 0 < C)
    (hd : StableDomainAttractionCentering PX α a d) :
    Tendsto (fun n : ℕ+ ↦ normalizedConvolutionLaw PX a d n) atTop (𝓝 μ) := sorry

end MeasureTheory.ProbabilityMeasure
