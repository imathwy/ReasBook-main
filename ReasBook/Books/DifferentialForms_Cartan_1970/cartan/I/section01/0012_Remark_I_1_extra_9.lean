import Mathlib
import DifferentialForms_Cartan_1970.I.section01.«0011_Proposition_5_1»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Polynomial PowerSeries

universe u

variable {K : Type u} [Field K]

/-- Remark I.1-extra-9: a polynomial whose value at `0` is nonzero is a unit in the formal power
series ring `K⟦X⟧`. -/
-- Proof sketch: specialize the chapter's canonical unit criterion for formal power series, then
-- identify the constant coefficient of the coerced polynomial with `Q.eval 0`.
theorem polynomial_isUnit_in_powerSeries_of_eval_zero_ne_zero
    (Q : K[X]) (hQ : Q.eval 0 ≠ 0) :
    IsUnit (Q : K⟦X⟧) := by
  rw [PowerSeries.isUnit_iff_constantCoeff_ne_zero]
  rw [Polynomial.constantCoeff_coe, Polynomial.coeff_zero_eq_eval_zero]
  exact hQ

/-- The quotient `P / Q` with `Q(0) ≠ 0` is represented in `K⟦X⟧` by multiplying the numerator by
the inverse of the denominator. -/
-- Proof sketch: use the field-level cancellation theorem for formal power series after rewriting
-- the constant coefficient of `(Q : K⟦X⟧)` as `Q.eval 0`.
theorem polynomial_powerSeries_quotient_mul_denominator
    (P Q : K[X]) (hQ : Q.eval 0 ≠ 0) :
    ((P : K⟦X⟧) * (Q : K⟦X⟧)⁻¹) * (Q : K⟦X⟧) = (P : K⟦X⟧) := by
  have hQc : PowerSeries.constantCoeff (Q : K⟦X⟧) ≠ 0 := by
    rw [Polynomial.constantCoeff_coe, Polynomial.coeff_zero_eq_eval_zero]
    exact hQ
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ hQc, mul_one]
