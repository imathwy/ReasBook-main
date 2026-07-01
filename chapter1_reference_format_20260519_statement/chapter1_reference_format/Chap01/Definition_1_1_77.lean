import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Definition 1.1.77: for a polynomial `P(X) = ∑ n ∈ ℕ, a_n X^n` in `R[X]`, its degree is the
supremum of the exponents `n` with nonzero coefficient `a_n` when `P ≠ 0`, and `-∞` when `P = 0`;
this is the canonical function `Polynomial.degree`, valued in `WithBot ℕ` so that `⊥` represents
`-∞`. -/
recall Polynomial.degree {R : Type u} [Semiring R] (p : Polynomial R) : WithBot ℕ
