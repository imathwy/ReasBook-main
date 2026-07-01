import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [Semiring R]

/- Domain-style sampling for polynomial coefficient expansions:
- primary domain: canonical decompositions of a polynomial into coefficient-weighted monomials;
- sampled owner declarations: `Polynomial.as_sum_support_C_mul_X_pow`,
  `Polynomial.as_sum_range`, and `Polynomial.as_sum_range_C_mul_X_pow`;
- owner abstraction: a polynomial `P : R[X]`, with support/range expansions derived from its
  canonical coefficient function.

Primitive data is only the polynomial `P`. The finite-support and finite-range expansion formulas
are derived API already owned by mathlib, so this file should recall the canonical theorem directly
rather than restating a parallel local interface.
-/
/- 9.7.6.1: a polynomial can be written as the sum of its coefficients times powers of the
indeterminate. In Lean this is the canonical expansion by the actual coefficients of `P`,
namely `P = ∑ i = 0^d, coeff_i(P) X^i`. -/
recall Polynomial.as_sum_range_C_mul_X_pow

end
