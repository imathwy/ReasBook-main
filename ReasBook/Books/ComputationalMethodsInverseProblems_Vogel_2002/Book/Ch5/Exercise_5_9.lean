module

public import ComputationalMethodsInverseProblems_Vogel_2002.Book.Ch5.Notation_5_2_1
public import ComputationalMethodsInverseProblems_Vogel_2002.Book.Ch5.Prop_5_6

public section

namespace Matrix

/-- Exercise 5.9. Equations `(5.23)` and `(5.38)` are equivalent formulations of
the periodic-extension discrete convolution identity, via the canonical
normalized `Matrix.dft`/`Matrix.invDFT` and source-facing `Matrix.fft`/`Matrix.ifft`
owners already established in Chapter 5. -/
theorem periodicExtension_discreteConvolution_eq_ifft_mul_fft_iff_invDFT_mul_dft
    (n : ℕ) [NeZero n] (t f : Fin n → ℂ) :
    Matrix.discreteConvolution (DiscreteSignal.periodicExtensionOfNeZero t) f =
        Matrix.ifft n (Matrix.fft n t * Matrix.fft n f) ↔
      ((1 / Real.sqrt n : ℂ) •
          Matrix.discreteConvolution (DiscreteSignal.periodicExtensionOfNeZero t) f) =
        Matrix.invDFT n (Matrix.dft n t * Matrix.dft n f) := by
  constructor <;> intro _
  · simpa using Matrix.periodicExtension_discreteConvolution_eq_invDFT_mul_dft n t f
  · simpa using
      (Matrix.periodicExtension_discreteConvolution_eq_ifft_mul_fft n
        (WithLp.toLp 2 t) (WithLp.toLp 2 f))

end Matrix
