import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Complex
open scoped ComplexConjugate

noncomputable section

/-- The Wirtinger derivative `∂f/∂z`. -/
noncomputable def partialDerivZ (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (fderiv ℝ f z 1 - I * fderiv ℝ f z I) / 2

/-- The conjugate Wirtinger derivative `∂f/∂\bar z`. -/
noncomputable def partialDerivConjZ (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (fderiv ℝ f z 1 + I * fderiv ℝ f z I) / 2

notation "∂z" => partialDerivZ
notation "∂z̄" => partialDerivConjZ

/-- Helper for Notation II.2-extra-2: every real-linear endomorphism of `ℂ` splits into its
`dz` and `d\bar z` coefficients. -/
theorem continuousLinearMap_apply_eq_wirtinger_split
    (L : ℂ →L[ℝ] ℂ) (w : ℂ) :
    L w = ((L 1 - I * L I) / 2) * w + ((L 1 + I * L I) / 2) * conj w := by
  -- Decompose `w` and `conj w` in the real basis `1, I`.
  have hw : w = (w.re : ℝ) • (1 : ℂ) + (w.im : ℝ) • I := by
    apply Complex.ext <;> simp
  have hw_complex : (w.re : ℂ) + (w.im : ℂ) * I = w := by
    apply Complex.ext <;> simp
  have hconj : (w.re : ℂ) - (w.im : ℂ) * I = conj w := by
    apply Complex.ext <;> simp
  -- Route correction: expand both sides in that basis and normalize the coefficients directly.
  calc
    L w = (w.re : ℂ) * L 1 + (w.im : ℂ) * L I := by
      rw [hw, map_add, map_smul, map_smul]
      simp [mul_comm]
    _ =
        ((L 1 - I * L I) / 2) * ((w.re : ℂ) + (w.im : ℂ) * I) +
          ((L 1 + I * L I) / 2) * ((w.re : ℂ) - (w.im : ℂ) * I) := by
      ring_nf
      simp [I_sq, mul_comm, mul_left_comm]
    _ = ((L 1 - I * L I) / 2) * w + ((L 1 + I * L I) / 2) * conj w := by
      rw [hw_complex, hconj]

/-- The real differential of `f` splits into the `dz` and `d\bar z` parts determined by the
Wirtinger derivatives. -/
theorem fderiv_real_apply_eq_partialDerivZ_mul_add_partialDerivConjZ_mul_conj
    {f : ℂ → ℂ} {z w : ℂ} :
    fderiv ℝ f z w = ∂z f z * w + ∂z̄ f z * conj w := by
  -- Apply the structural splitting formula to the real differential.
  simpa [partialDerivZ, partialDerivConjZ] using
    continuousLinearMap_apply_eq_wirtinger_split (L := fderiv ℝ f z) (w := w)

/-- The vanishing of the conjugate Wirtinger derivative is exactly the Cauchy-Riemann relation for
the real derivative. -/
theorem partialDerivConjZ_eq_zero_iff
    {f : ℂ → ℂ} {z : ℂ} :
    ∂z̄ f z = 0 ↔ fderiv ℝ f z I = I • fderiv ℝ f z 1 := by
  constructor
  · intro h
    -- Clear the harmless factor `1/2` to isolate the Cauchy-Riemann numerator.
    have hnum : fderiv ℝ f z 1 + I * fderiv ℝ f z I = 0 := by
      have hmul := congrArg (fun w : ℂ ↦ w * (2 : ℂ)) h
      simpa [partialDerivConjZ, mul_add, add_mul, mul_assoc] using hmul
    -- Multiplying by `-I` turns the numerator relation into the usual Cauchy-Riemann equation.
    have hmul : (-I) * (fderiv ℝ f z 1 + I * fderiv ℝ f z I) = 0 := by
      simpa using congrArg (fun w : ℂ ↦ (-I) * w) hnum
    have hcr : (-I) * fderiv ℝ f z 1 + fderiv ℝ f z I = 0 := by
      ring_nf at hmul ⊢
      simpa [I_sq] using hmul
    have hEq : fderiv ℝ f z I = -((-I) * fderiv ℝ f z 1) :=
      eq_neg_of_add_eq_zero_right hcr
    simpa [smul_eq_mul, mul_assoc] using hEq
  · intro h
    -- Substitute the Cauchy-Riemann relation back into `∂z̄` and simplify.
    rw [smul_eq_mul] at h
    rw [partialDerivConjZ, h]
    have hI : I * (I * fderiv ℝ f z 1) = -(fderiv ℝ f z 1) := by
      calc
        I * (I * fderiv ℝ f z 1) = (I * I) * fderiv ℝ f z 1 := by ring
        _ = -(fderiv ℝ f z 1) := by simp [I_mul_I]
    rw [hI]
    ring

/-- Notation II.2-extra-2: with the Wirtinger operators `∂/∂z` and `∂/∂\bar z`, the holomorphicity
condition (2.4) is the vanishing of the conjugate derivative `∂f/∂\bar z`. -/
theorem differentiableAt_complex_iff_partialDerivConjZ_eq_zero
    {f : ℂ → ℂ} {z : ℂ} :
    DifferentiableAt ℂ f z ↔ DifferentiableAt ℝ f z ∧ ∂z̄ f z = 0 := by
  -- Rewrite the standard Cauchy-Riemann criterion in Wirtinger notation.
  rw [differentiableAt_complex_iff_differentiableAt_real, partialDerivConjZ_eq_zero_iff]
