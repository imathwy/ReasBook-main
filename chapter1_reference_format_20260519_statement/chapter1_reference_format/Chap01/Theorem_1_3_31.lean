import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable (A : Type u) [CommRing A] [UniqueFactorizationMonoid A]

/- Theorem 1.3.31: if `A` is a unique factorization domain, then the polynomial ring `A[X]` is
again a unique factorization domain. In mathlib this is the named canonical owner
`Polynomial.uniqueFactorizationMonoid`. -/
#check (Polynomial.uniqueFactorizationMonoid : UniqueFactorizationMonoid (Polynomial A))

end
