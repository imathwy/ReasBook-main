import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

section IntegerPolynomials

/- Definition 1.3.26: for integer polynomials, irreducibility is the canonical predicate
`Irreducible`; the content `c(P)` is the canonical function `Polynomial.content`, with
`c(0) = 0`; and a polynomial is primitive exactly when it satisfies the canonical predicate
`Polynomial.IsPrimitive`. -/
#check (Polynomial.IsPrimitive : Polynomial ℤ → Prop)

/- The canonical irreducibility predicate on `ℤ[X]`. -/
#check (Irreducible : Polynomial ℤ → Prop)

/- The content of an integer polynomial is the gcd of its coefficients. -/
#check (Polynomial.content : Polynomial ℤ → ℤ)

/- The content of the zero polynomial is zero. -/
#check (Polynomial.content_zero : Polynomial.content (0 : Polynomial ℤ) = 0)

/- Over `ℤ[X]`, a polynomial is primitive exactly when its content is `1`. -/
#check (Polynomial.isPrimitive_iff_content_eq_one :
  ∀ {p : Polynomial ℤ}, p.IsPrimitive ↔ p.content = 1)

end IntegerPolynomials
