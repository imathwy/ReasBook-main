import Mathlib

open MeasureTheory
open scoped ENNReal FourierTransform

noncomputable section

/-- The inverse-Fourier candidate density attached to the characteristic function of a real
probability measure, built from the canonical owners `MeasureTheory.charFun` and `𝓕⁻`. -/
def charFunInversionDensity (μ : Measure ℝ) : ℝ → ℝ :=
  fun x ↦ Complex.re ((𝓕⁻ fun t : ℝ ↦ charFun μ (-2 * Real.pi * t)) x)

section

variable (μ : Measure ℝ)

-- Proof sketch: first compute the inverse-Fourier density for the Gaussian mollifiers
-- `gaussianReal 0 ε`; then identify the densities of `μ ∗ gaussianReal 0 ε` by Fourier inversion
-- and pass to the limit as `ε → 0`.
/-- Exercise 15.1.6: if a probability measure on `ℝ` has integrable characteristic function, then
it is absolutely continuous with respect to Lebesgue measure, with density given by the inverse
Fourier transform of its characteristic function. -/
theorem probabilityMeasure_eq_withDensity_of_integrable_charFun
    [IsProbabilityMeasure μ] (hφ : Integrable (charFun μ) volume) :
    μ = volume.withDensity (ENNReal.ofReal ∘ charFunInversionDensity μ) := sorry

-- Proof sketch: apply dominated convergence to the oscillatory integral defining
-- `charFunInversionDensity μ`, using the `L¹` majorant `t ↦ ‖charFun μ t‖`.
/-- The inverse-Fourier density attached to an integrable characteristic function is continuous. -/
theorem charFunInversionDensity_continuous
    (hφ : Integrable (charFun μ) volume) :
    Continuous (charFunInversionDensity μ) := sorry

-- Proof sketch: bound the oscillatory integral uniformly by the `L¹` norm of the characteristic
-- function.
/-- The inverse-Fourier density is pointwise bounded by the `L¹` norm of the characteristic
function. -/
theorem norm_charFunInversionDensity_le_integral_norm
    (hφ : Integrable (charFun μ) volume) (x : ℝ) :
    ‖charFunInversionDensity μ x‖ ≤ ∫ t, ‖charFun μ t‖ := sorry

-- Proof sketch: apply `norm_charFunInversionDensity_le_integral_norm` uniformly in `x`.
/-- The inverse-Fourier density attached to an integrable characteristic function is bounded. -/
theorem charFunInversionDensity_bounded
    (hφ : Integrable (charFun μ) volume) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖charFunInversionDensity μ x‖ ≤ C := by
  refine ⟨∫ t, ‖charFun μ t‖, integral_nonneg fun t ↦ norm_nonneg _, fun x ↦ ?_⟩
  exact norm_charFunInversionDensity_le_integral_norm μ hφ x

end
