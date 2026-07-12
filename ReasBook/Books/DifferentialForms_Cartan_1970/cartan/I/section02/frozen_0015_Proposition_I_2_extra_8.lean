import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open FormalMultilinearSeries

universe u

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

section CoeffFormula

variable [CompleteSpace 𝕜] [CharZero 𝕜]

/-- Proposition I.2-extra-8: if `f` is represented near `0` by the scalar power series
`∑ n, a n * z ^ n`, then the coefficient `a n` is obtained by evaluating the `n`th derivative of
`f` at `0` and dividing by `n!`. -/
-- Proof sketch: compare the scalar power-series expansion of `f` at `0` with the Taylor expansion
-- given by iterated derivatives, and identify the `n`th coefficient using the uniqueness of the
-- formal power series representing `f` at `0`.
theorem coeff_eq_inv_factorial_mul_iteratedDeriv_zero {f : 𝕜 → 𝕜} {a : ℕ → 𝕜}
    (ha : HasFPowerSeriesAt f (ofScalars 𝕜 a) 0) (n : ℕ) :
    a n = (n.factorial : 𝕜)⁻¹ * iteratedDeriv n f 0 := by
  have hcoeffs : a = fun m ↦ iteratedDeriv m f 0 / m.factorial := by
    apply ofScalars_series_injective 𝕜 𝕜
    exact ha.eq_formalMultilinearSeries ha.analyticAt.hasFPowerSeriesAt
  simpa [div_eq_mul_inv, mul_comm] using congrFun hcoeffs n

end CoeffFormula

/-- Two locally convergent scalar power series expansions of the same function at `0` have the
same coefficient sequence. -/
-- Proof sketch: use uniqueness of one-variable formal power series expansions at a point to show
-- that the two formal multilinear series are equal, then apply injectivity of `ofScalars`.
theorem coeffs_eq_of_hasFPowerSeriesAt_zero {f : 𝕜 → 𝕜} {a b : ℕ → 𝕜}
    (ha : HasFPowerSeriesAt f (ofScalars 𝕜 a) 0)
    (hb : HasFPowerSeriesAt f (ofScalars 𝕜 b) 0) :
    a = b := by
  apply ofScalars_series_injective 𝕜 𝕜
  exact ha.eq_formalMultilinearSeries hb
