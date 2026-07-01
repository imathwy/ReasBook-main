import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/-
Domain-style sampling:
- primary domain: factorization theory for polynomial and multivariable polynomial rings over
  unique factorization domains;
- sampled owner API:
  `Polynomial.uniqueFactorizationMonoid`,
  `MvPolynomial.uniqueFactorizationMonoid`,
  `UniqueFactorizationMonoid.toWfDvdMonoid`,
  `PrincipalIdealRing.to_uniqueFactorizationMonoid`;
- source-facing: the textbook polynomial and finite-variable polynomial UFD statements below;
- core/canonical: the mathlib `UniqueFactorizationMonoid` instances on `Polynomial` and
  `MvPolynomial`;
- bridge/view: the second statement is the `Fin n` and `Field` specialization of the multivariable
  owner instance.

Primitive data are only the base-ring factorization hypotheses. The polynomial UFD structures are
derived API owned upstream, so this file should recall those owner instances directly and not keep
parallel local wrappers.
-/

section Polynomial

variable (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]

/- Lemma 10.120.10: a polynomial ring over a unique factorization domain is again a unique
factorization domain. This is exactly the canonical mathlib instance
`Polynomial.uniqueFactorizationMonoid`. -/
recall Polynomial.uniqueFactorizationMonoid

end Polynomial

section MvPolynomialField

variable (k : Type u) [Field k] (n : ℕ)

/- If `k` is a field, then `k[x_1, \ldots, x_n]`, formalized as `MvPolynomial (Fin n) k`, is a
unique factorization domain. This is the specialization of the canonical mathlib instance
`MvPolynomial.uniqueFactorizationMonoid` to a finite set of variables. -/
recall MvPolynomial.uniqueFactorizationMonoid

end MvPolynomialField
