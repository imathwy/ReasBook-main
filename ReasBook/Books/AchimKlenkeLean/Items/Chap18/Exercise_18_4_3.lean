import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality

-- Declarations for this item will be appended below by the statement pipeline.

open Real intervalIntegral MeasureTheory

noncomputable section

namespace Polynomial.Chebyshev

/-- The probability measure on `[-1, 1]` with density `(2 / π) * √(1 - x ^ 2)` with respect to
Lebesgue measure, expressed canonically as a reweighting of `measureT`. -/
noncomputable def measureU : Measure ℝ :=
  measureT.withDensity (fun x ↦ ENNReal.ofReal ((2 / π) * (1 - x ^ 2)))

-- Proof sketch: expand `measureU` as a weighted Lebesgue measure and then apply the substitution
-- `x = cos θ` on `[-1, 1]`, using `dx = - sin θ dθ` and `√(1 - cos θ ^ 2) = sin θ` for
-- `θ ∈ [0, π]`.
/-- Integrating against `measureU` is the same as integrating along `x = cos θ` on `[0, π]` with
weight `(2 / π) * sin θ ^ 2`. -/
theorem integral_measureU_eq_integral_cos {f : ℝ → ℝ} :
    ∫ x, f x ∂ measureU = ∫ θ in 0..π, f (cos θ) * ((2 / π) * sin θ ^ 2) := sorry

-- Proof sketch: rewrite the `measureU` integral using `integral_measureU_eq_integral_cos`, then
-- use `U_real_cos` to convert each evaluated Chebyshev polynomial into a sine quotient. The
-- factor `sin θ ^ 2` from the measure cancels the denominators, leaving the normalized sine
-- orthogonality integral on `[0, π]`.
/-- Exercise 18.4.3: the Chebyshev polynomials of the second kind are orthonormal with respect to
the measure `measureU`, equivalently
`∫ x, (U_m x) * (U_n x) dν = 1` when `m = n` and `0` otherwise. -/
theorem integral_eval_U_real_mul_eval_U_real_measureU (m n : ℕ) :
    ∫ x, (U ℝ m).eval x * (U ℝ n).eval x ∂ measureU = if m = n then 1 else 0 := sorry

end Polynomial.Chebyshev
