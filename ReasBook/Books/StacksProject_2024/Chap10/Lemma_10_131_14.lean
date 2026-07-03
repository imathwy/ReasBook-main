import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open MvPolynomial

variable (R : Type u) [CommRing R] (n : ℕ)

/- Lemma 10.131.14: if `S = R[x₁, …, xₙ]`, formalized as `MvPolynomial (Fin n) R`, then
`Ω[S⁄R]` is a finite free `S`-module with basis `d x₁, …, d xₙ`. This is exactly the canonical
mathlib basis `KaehlerDifferential.mvPolynomialBasis R (Fin n)`, whose basis vectors are the
universal differentials of the coordinate variables. -/
recall KaehlerDifferential.mvPolynomialBasis

/- Companion recall: the `i`th basis vector is the universal differential `d(X i)`. -/
recall KaehlerDifferential.mvPolynomialBasis_apply

end
