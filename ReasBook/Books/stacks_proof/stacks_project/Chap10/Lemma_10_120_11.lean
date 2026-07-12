import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]

/- Lemma 10.120.11: a unique factorization domain is normal, i.e. it is integrally closed in
its fraction field. This is exactly the canonical mathlib instance
`UniqueFactorizationMonoid.instIsIntegrallyClosed`. -/
recall UniqueFactorizationMonoid.instIsIntegrallyClosed
