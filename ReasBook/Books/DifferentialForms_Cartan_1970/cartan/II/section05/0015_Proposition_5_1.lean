import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0001_Definition_II_1_extra_1»
import DifferentialForms_Cartan_1970.II.section05.«0026_Definition_II_1_extra_16»

open scoped unitInterval

noncomputable section

namespace Path

-- Proof sketch: regard `dz / z` as the canonical logarithmic form `indexForm 0`; then Proposition
-- 5.1 is the specialization at `a = 0` of the chapter-level theorem
-- `closedPathIndex_isInteger`, after clearing the normalizing factor `2π i`.
/-- Proposition 5.1: for a closed path in `ℂ` that avoids the origin and along which the
logarithmic form is integrable, the integral of `dz / z` is an integer multiple of `2π i`. -/
theorem curveIntegral_inv_eq_two_pi_I_mul_int
    {z : ℂ} {γ : Path z z} (hγ₀ : ∀ t : I, γ t ≠ 0)
    (hγ_piecewise : γ.IsPiecewiseDifferentiable)
    (hInt : CurveIntegrable (indexForm 0) γ) :
    ∃ n : ℤ,
      ∫ᶜ w in γ, indexForm 0 w =
        ((2 * Real.pi : ℂ) * Complex.I) * (n : ℂ) := by
  let a : {w : ℂ // w ∉ Set.range γ} := ⟨0, by
    rintro ⟨t, ht⟩
    exact hγ₀ t ht⟩
  rcases closedPathIndex_isInteger γ a hγ_piecewise hInt with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  have hindex :
      (∫ᶜ w in γ, indexForm 0 w) / (((2 * Real.pi : ℂ) * Complex.I)) = (n : ℂ) := by
    simpa [closedPathIndex_def, a] using hn
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (div_eq_iff Complex.two_pi_I_ne_zero).1 hindex

/-- Proposition 5.1 in normalized form: for a closed path in `ℂ` that avoids the origin and along
which the logarithmic form is integrable, `(1 / (2 * π * i)) ∫_γ dz / z` is an integer. -/
theorem curveIntegral_inv_div_two_pi_I_eq_int
    {z : ℂ} {γ : Path z z} (hγ₀ : ∀ t : I, γ t ≠ 0)
    (hγ_piecewise : γ.IsPiecewiseDifferentiable)
    (hInt : CurveIntegrable (indexForm 0) γ) :
    ∃ n : ℤ,
      (∫ᶜ w in γ, indexForm 0 w) / (2 * Real.pi * Complex.I : ℂ) = (n : ℂ) := by
  rcases curveIntegral_inv_eq_two_pi_I_mul_int hγ₀ hγ_piecewise hInt with ⟨n, hγ⟩
  refine ⟨n, ?_⟩
  exact (div_eq_iff Complex.two_pi_I_ne_zero).2 <| by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hγ

end Path
