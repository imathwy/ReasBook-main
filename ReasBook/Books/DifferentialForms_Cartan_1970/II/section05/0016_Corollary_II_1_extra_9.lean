import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0001_Definition_II_1_extra_1»
import DifferentialForms_Cartan_1970.II.section05.«0026_Definition_II_1_extra_16»

open scoped unitInterval

noncomputable section

/-- The imaginary part of the totalized logarithmic form `indexForm 0` is the real argument form
coming from the canonical planar-form surface
`(fun w ↦ -w.im / Complex.normSq w) dx + (fun w ↦ w.re / Complex.normSq w) dy`. -/
theorem indexForm_zero_im_eq_argumentForm (z : ℂ) :
    Complex.imCLM.comp ((indexForm 0 z).restrictScalars ℝ) =
    ((fun w ↦ -w.im / Complex.normSq w) dx + (fun w ↦ w.re / Complex.normSq w) dy) z := by
  ext v
  simp [indexForm, div_eq_mul_inv]
  ring

namespace Path

/- Auxiliary bridge: an explicit logarithmic integral formula `∫_γ dz / z = (2π i) n` implies the
corresponding normalized argument-form integral formula. -/
theorem curveIntegral_argument_form_div_two_pi_eq_of_curveIntegral_inv_eq
    {z : ℂ} {γ : Path z z} {n : ℤ}
    (hγ_inv :
      ∫ᶜ w in γ, indexForm 0 w =
        ((2 * Real.pi : ℂ) * Complex.I) * (n : ℂ)) :
    (1 / (2 * Real.pi)) *
        ∫ᶜ w in γ,
          ((fun w ↦ -w.im / Complex.normSq w) dx + (fun w ↦ w.re / Complex.normSq w) dy) w =
      (n : ℝ) := sorry

-- Proof sketch: use the source-facing winding-index owner `HasIndexAt` to recover the canonical
-- logarithmic integral formula `∫_γ dz / z = (2π i) n`, then read its imaginary part through
-- `indexForm_zero_im_eq_argumentForm`.
/-- Corollary II.1-extra-9: if a closed complex path `γ` has winding index `n` about `0`, then
the normalized integral of the corresponding real argument form is `n`. -/
theorem curveIntegral_argument_form_div_two_pi_eq
    {z : ℂ} {γ : Path z z} {n : ℤ} (hγ : γ.HasIndexAt 0 n) :
    (1 / (2 * Real.pi)) *
        ∫ᶜ w in γ,
          ((fun w ↦ -w.im / Complex.normSq w) dx + (fun w ↦ w.re / Complex.normSq w) dy) w =
      (n : ℝ) := by
  have hindex :
      (∫ᶜ w in γ, indexForm 0 w) / (((2 * Real.pi : ℂ) * Complex.I)) = (n : ℂ) := by
    simpa [closedPathIndex_def, closedPathIndexAt_def] using hγ.closedPathIndex_eq
  have hγ_inv :
      ∫ᶜ w in γ, indexForm 0 w = ((2 * Real.pi : ℂ) * Complex.I) * (n : ℂ) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (div_eq_iff Complex.two_pi_I_ne_zero).1 hindex
  exact curveIntegral_argument_form_div_two_pi_eq_of_curveIntegral_inv_eq hγ_inv

end Path
