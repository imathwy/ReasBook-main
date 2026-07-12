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

/-- Helper for Cartan section05 0016_Corollary_II_1_extra_9: the imaginary part of the standard
winding-number normalizing factor `((2 * π) i) n` is exactly `(2 * π) n`. -/
theorem twoPiI_mul_int_im (n : ℤ) :
    Complex.im ((((2 * Real.pi : ℂ) * Complex.I) * (n : ℂ))) = (2 * Real.pi) * (n : ℝ) := by
  -- Expand the `z * I` imaginary-part formula so the complex factor becomes a real scalar.
  simp [mul_comm]

namespace Path

/-- Helper for Cartan section05 0016_Corollary_II_1_extra_9: taking the imaginary part of a
complex-valued real curve integral commutes with integration once the pullback is integrable. -/
theorem curveIntegral_im_comp_eq
    {z : ℂ} {γ : Path z z} {ω : ℂ → ℂ →L[ℝ] ℂ}
    (hInt : CurveIntegrable ω γ) :
    ∫ᶜ w in γ, Complex.imCLM.comp (ω w) = Complex.im (∫ᶜ w in γ, ω w) := by
  -- Rewrite the curve integrals as interval integrals so that `Complex.imCLM` can cross the
  -- Bochner integral by the standard continuous-linear-map commutation theorem.
  rw [curveIntegral_def, curveIntegral_def]
  simpa [CurveIntegrable, curveIntegralFun, Function.comp] using
    Complex.imCLM.intervalIntegral_comp_comm (f := curveIntegralFun ω γ) hInt

/-- Helper for Cartan section05 0016_Corollary_II_1_extra_9: the real argument form is the
imaginary part of the logarithmic form `indexForm 0`, both pointwise and after integration. -/
theorem curveIntegral_argumentForm_eq_im_indexFormIntegral
    {z : ℂ} {γ : Path z z} (hInt : CurveIntegrable (indexForm 0) γ) :
    ∫ᶜ w in γ,
        ((fun w ↦ -w.im / Complex.normSq w) dx + (fun w ↦ w.re / Complex.normSq w) dy) w =
      Complex.im (∫ᶜ w in γ, indexForm 0 w) := by
  have hRestrict : CurveIntegrable (fun w ↦ ((indexForm 0 w).restrictScalars ℝ)) γ := by
    -- Restricting scalars preserves the pullback integrability of the logarithmic form.
    simpa using
      (curveIntegrable_restrictScalars_iff (ω := indexForm 0) (γ := γ) (𝕝 := ℝ)).2 hInt
  -- Rewrite the argument form through `indexForm_zero_im_eq_argumentForm`, then remove the
  -- scalar restriction on the final complex integral.
  calc
    ∫ᶜ w in γ,
        ((fun w ↦ -w.im / Complex.normSq w) dx + (fun w ↦ w.re / Complex.normSq w) dy) w =
      ∫ᶜ w in γ, Complex.imCLM.comp (((indexForm 0 w).restrictScalars ℝ)) := by
        simp_rw [← indexForm_zero_im_eq_argumentForm]
    _ = Complex.im (∫ᶜ w in γ, ((indexForm 0 w).restrictScalars ℝ)) := by
      simpa using
        curveIntegral_im_comp_eq
          (γ := γ) (ω := fun w ↦ ((indexForm 0 w).restrictScalars ℝ)) hRestrict
    _ = Complex.im (∫ᶜ w in γ, indexForm 0 w) := by
      rw [curveIntegral_restrictScalars]

/-- Helper for Cartan section05 0016_Corollary_II_1_extra_9: once the logarithmic form is curve
integrable along `γ`, the explicit identity `∫_γ dz / z = (2π i) n` converts to the normalized
argument-form integral formula by taking imaginary parts. -/
theorem curveIntegral_argument_form_div_two_pi_eq_of_curveIntegral_inv_eq
    {z : ℂ} {γ : Path z z} {n : ℤ}
    (hInt : CurveIntegrable (indexForm 0) γ)
    (hγ_inv :
      ∫ᶜ w in γ, indexForm 0 w =
        ((2 * Real.pi : ℂ) * Complex.I) * (n : ℂ)) :
    (1 / (2 * Real.pi)) *
        ∫ᶜ w in γ,
          ((fun w ↦ -w.im / Complex.normSq w) dx + (fun w ↦ w.re / Complex.normSq w) dy) w =
      (n : ℝ) := by
  -- Rewrite the real argument-form integral as the imaginary part of the logarithmic integral.
  have harg :
      ∫ᶜ w in γ,
          ((fun w ↦ -w.im / Complex.normSq w) dx + (fun w ↦ w.re / Complex.normSq w) dy) w =
        Complex.im (∫ᶜ w in γ, indexForm 0 w) := by
    simpa using curveIntegral_argumentForm_eq_im_indexFormIntegral (γ := γ) hInt
  -- Taking imaginary parts of `(2π i) n` removes the factor `i` and leaves `2π n`.
  have him :
      Complex.im (∫ᶜ w in γ, indexForm 0 w) = (2 * Real.pi) * (n : ℝ) := by
    -- Rewrite by the explicit logarithmic integral formula, then normalize the fixed complex
    -- factor with the dedicated arithmetic helper.
    rw [hγ_inv]
    exact twoPiI_mul_int_im n
  -- Divide the resulting real equality by `2π`.
  have hnorm :
      ∫ᶜ w in γ,
          ((fun w ↦ -w.im / Complex.normSq w) dx + (fun w ↦ w.re / Complex.normSq w) dy) w =
        (2 * Real.pi) * (n : ℝ) :=
    harg.trans him
  calc
    (1 / (2 * Real.pi)) *
        ∫ᶜ w in γ,
          ((fun w ↦ -w.im / Complex.normSq w) dx + (fun w ↦ w.re / Complex.normSq w) dy) w =
      (1 / (2 * Real.pi)) * ((2 * Real.pi) * (n : ℝ)) := by rw [hnorm]
    _ = (n : ℝ) := by
      field_simp [Real.pi_ne_zero]

-- Proof sketch: use the source-facing winding-index owner `HasIndexAt` to recover the canonical
-- logarithmic integral formula `∫_γ dz / z = (2π i) n`, then read its imaginary part through
-- `indexForm_zero_im_eq_argumentForm`.
/-- Cartan section05 0016_Corollary_II_1_extra_9 (Corollary II.1-extra-9): if a closed complex
path `γ` has winding index `n` about `0` and the logarithmic form is curve-integrable along `γ`,
then the normalized integral of the corresponding real argument form is `n`. This keeps the
statement at the piecewise-differentiable/integrable level used by the source integral formula. -/
theorem curveIntegral_argument_form_div_two_pi_eq
    {z : ℂ} {γ : Path z z} {n : ℤ}
    (hγ : γ.HasIndexAt 0 n) (hγ_piecewise : γ.IsPiecewiseDifferentiable)
    (hInt : CurveIntegrable (indexForm 0) γ) :
    (1 / (2 * Real.pi)) *
        ∫ᶜ w in γ,
          ((fun w ↦ -w.im / Complex.normSq w) dx + (fun w ↦ w.re / Complex.normSq w) dy) w =
      (n : ℝ) := by
  have hindex :
      (∫ᶜ w in γ, indexForm 0 w) / (((2 * Real.pi : ℂ) * Complex.I)) = (n : ℂ) := by
    simpa [closedPathIndex_def, closedPathIndexAt_def] using hγ.closedPathIndex_eq hγ_piecewise hInt
  have hγ_inv :
      ∫ᶜ w in γ, indexForm 0 w = ((2 * Real.pi : ℂ) * Complex.I) * (n : ℂ) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (div_eq_iff Complex.two_pi_I_ne_zero).1 hindex
  exact curveIntegral_argument_form_div_two_pi_eq_of_curveIntegral_inv_eq hInt hγ_inv

end Path
