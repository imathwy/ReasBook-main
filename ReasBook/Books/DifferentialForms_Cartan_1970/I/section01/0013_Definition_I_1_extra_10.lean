import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped PowerSeries
open PowerSeries

universe u

/- Definition I.1-extra-10: the formal derivative of a formal power series is the canonical
power-series derivation `PowerSeries.derivative`; it is written `d⁄dX`, is linear, and satisfies
Leibniz's rule for products. -/
recall PowerSeries.derivative

/- The coefficient formula `coeff n (d⁄dX R S) = coeff (n + 1) S * (n + 1)` is the canonical
coefficientwise description of the formal derivative. -/
recall PowerSeries.coeff_derivative

/-- The formal derivative of a product of formal power series
is the sum of the two Leibniz terms. -/
-- Proof sketch: apply the Leibniz rule for the derivation `PowerSeries.derivative R` and rewrite
-- the scalar actions on `R⟦X⟧` as multiplication.
theorem formal_derivative_mul
    {R : Type u} [CommSemiring R] (S T : R⟦X⟧) :
    d⁄dX R (S * T) = S * d⁄dX R T + T * d⁄dX R S := by
  rw [(PowerSeries.derivative R).leibniz, smul_eq_mul, smul_eq_mul]

/- Over a field, the inverse-rule formula of the text is the existing theorem
`PowerSeries.derivative_inv'`. -/
recall PowerSeries.derivative_inv'

/-- The constant coefficient of the `n`-fold formal derivative is `n!` times the `n`th
coefficient of the original series, i.e. `S⁽ⁿ⁾(0) = n! aₙ` for `S = ∑ aₙ X^n`. -/
-- Proof sketch: induct on `n`; at each step identify the constant coefficient with the zeroth
-- coefficient and apply `PowerSeries.coeff_derivative`, which shifts coefficients by one and
-- multiplies by the next index.
theorem constantCoeff_iterate_derivative_eq_factorial_mul_coeff
    {R : Type u} [CommSemiring R] (S : R⟦X⟧) (n : ℕ) :
    constantCoeff (((d⁄dX R)^[n]) S) = Nat.factorial n * coeff n S := by
  induction n generalizing S with
  | zero =>
      simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      rw [ih (d⁄dX R S), PowerSeries.coeff_derivative]
      simp [Nat.factorial_succ, mul_assoc, mul_comm]
