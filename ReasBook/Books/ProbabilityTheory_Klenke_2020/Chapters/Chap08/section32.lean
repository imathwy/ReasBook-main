import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_8_32 (from Items/Chap08) -/
open MeasureTheory ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: use `ProbabilityTheory.condDistrib` as the regular conditional distribution of
-- `Z₁` given `Z₁ + Z₂`. The independent Gaussian laws imply that `(Z₁ + Z₂, Z₁)` is jointly
-- Gaussian, compute its mean and covariance, and then identify the disintegration along the first
-- coordinate with the one-dimensional Gaussian law having the textbook conditional mean and
-- conditional variance.
/-- Example 8.32: in kernel form, if `Z₁` and `Z₂` are independent Gaussian random variables with
laws `N(μ₁, σ₁²)` and `N(μ₂, σ₂²)`, then the regular conditional distribution kernel of `Z₁` given
`Z₁ + Z₂` is, for `P.map (Z₁ + Z₂)`-almost every `x`, the Gaussian law
`N(μ₁ + (σ₁² / (σ₁² + σ₂²)) (x - μ₁ - μ₂), (σ₁²σ₂²)/(σ₁² + σ₂²))`. -/
theorem condDistrib_gaussian_left_given_sum_ae_eq
    (P : Measure Ω) {Z1 Z2 : Ω → ℝ} (μ1 μ2 σ1 σ2 : ℝ)
    (hZ1 : HasLaw Z1 (gaussianReal μ1 ⟨σ1 ^ 2, sq_nonneg σ1⟩) P)
    (hZ2 : HasLaw Z2 (gaussianReal μ2 ⟨σ2 ^ 2, sq_nonneg σ2⟩) P)
    (hindep : IndepFun Z1 Z2 P) :
    letI : IsProbabilityMeasure P := hZ1.isProbabilityMeasure
    condDistrib Z1 (Z1 + Z2) P =ᵐ[P.map (Z1 + Z2)]
      fun x ↦
        gaussianReal
          (μ1 + (σ1 ^ 2 / (σ1 ^ 2 + σ2 ^ 2)) * (x - μ1 - μ2))
          ⟨(σ1 ^ 2 * σ2 ^ 2) / (σ1 ^ 2 + σ2 ^ 2), by positivity⟩ := sorry

/-- Pointwise form of `condDistrib_gaussian_left_given_sum_ae_eq`. -/
theorem condDistrib_gaussian_left_given_sum_ae_eq_apply
    (P : Measure Ω) {Z1 Z2 : Ω → ℝ} (μ1 μ2 σ1 σ2 : ℝ)
    (hZ1 : HasLaw Z1 (gaussianReal μ1 ⟨σ1 ^ 2, sq_nonneg σ1⟩) P)
    (hZ2 : HasLaw Z2 (gaussianReal μ2 ⟨σ2 ^ 2, sq_nonneg σ2⟩) P)
    (hindep : IndepFun Z1 Z2 P) :
    letI : IsProbabilityMeasure P := hZ1.isProbabilityMeasure
    ∀ᵐ x ∂P.map (Z1 + Z2),
      condDistrib Z1 (Z1 + Z2) P x =
        gaussianReal
          (μ1 + (σ1 ^ 2 / (σ1 ^ 2 + σ2 ^ 2)) * (x - μ1 - μ2))
          ⟨(σ1 ^ 2 * σ2 ^ 2) / (σ1 ^ 2 + σ2 ^ 2), by positivity⟩ := by
  simpa using condDistrib_gaussian_left_given_sum_ae_eq P μ1 μ2 σ1 σ2 hZ1 hZ2 hindep
