import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 1.3.28: the integer polynomial ring `ℤ[X]` is a unique factorization domain. Equivalently,
every nonzero nonunit polynomial in `ℤ[X]` factors uniquely up to units and order; after separating
its integer content, the remaining factors may be taken to be primitive irreducible polynomials.
This is the canonical named polynomial-UFD owner specialized to `ℤ`. -/
#check (Polynomial.uniqueFactorizationMonoid : UniqueFactorizationMonoid (Polynomial ℤ))
