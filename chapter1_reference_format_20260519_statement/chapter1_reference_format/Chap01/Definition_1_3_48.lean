import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {R : Type u} [CommSemiring R] {σ : Type v}

/- Definition 1.3.48: for a multivariate polynomial `P`, the degree with respect to the variable
`X i` is the degree of `P` when it is regarded as a polynomial in `X i`; for a monomial with
exponent vector `d : σ →₀ ℕ`, its total degree is the sum of its exponents, namely `d.degree`;
and the degree of `P` itself is the maximum total degree of the monomials appearing in `P`,
recorded by `P.totalDegree`. -/
recall MvPolynomial.degreeOf {R : Type u} {σ : Type v} [CommSemiring R]
    (i : σ) (P : MvPolynomial σ R) : ℕ

/- The total degree of a monomial with exponent vector `d` is encoded by `Finsupp.degree d`. -/
#check (Finsupp.degree : (σ →₀ ℕ) →+ ℕ)

/- The total degree of a multivariate polynomial is the canonical function `MvPolynomial.totalDegree`.
-/
recall MvPolynomial.totalDegree {R : Type u} {σ : Type v} [CommSemiring R]
    (P : MvPolynomial σ R) : ℕ
