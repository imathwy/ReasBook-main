import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Polynomial
open Polynomial

variable {R : Type u} [Semiring R]

/- Definition 1.3.42: for a polynomial `P(X) = a_0 + a_1 X + ... + a_n X^n` in `R[X]`, its
derivative polynomial is the canonical owner `derivative P`. -/
#check (derivative : R[X] →ₗ[R] R[X])

/- The coefficients of the formal derivative polynomial satisfy the expected shifted formula. -/
#check (coeff_derivative :
  ∀ (P : R[X]) (n : ℕ), coeff (derivative P) n = coeff P (n + 1) * (n + 1))
