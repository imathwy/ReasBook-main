import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Definition 1.1.78 (1): for a polynomial `P(X) = ∑ n ∈ ℕ, a_n X^n` in `R[X]` with
`deg P = d`, the coefficient `a_d` of the highest-degree term is its leading coefficient; this is
the canonical function `Polynomial.leadingCoeff`. -/
recall Polynomial.leadingCoeff {R : Type u} [Semiring R] (p : Polynomial R) : R

/- Definition 1.1.78 (2): a polynomial is monic when its leading coefficient is `1`; this is the
canonical predicate `Polynomial.Monic`. -/
recall Polynomial.Monic {R : Type u} [Semiring R] (p : Polynomial R) : Prop
