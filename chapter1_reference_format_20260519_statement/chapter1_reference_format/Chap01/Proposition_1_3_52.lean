import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open MvPolynomial

section

variable {K : Type u} [Field K] [Infinite K] {n : ℕ} (P : MvPolynomial (Fin n) K)

/- Proposition 1.3.52: over an infinite field, a multivariate polynomial in `n` variables is zero
if and only if it evaluates to zero at every point of `K^n`. This is the `q = 0` specialization
of the canonical owner theorem `MvPolynomial.funext_iff`. -/
#check
  (show P = 0 ↔ ∀ x : Fin n → K, eval x P = 0 from MvPolynomial.funext_iff)

end
