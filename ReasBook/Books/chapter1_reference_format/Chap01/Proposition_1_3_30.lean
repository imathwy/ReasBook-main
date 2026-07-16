import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Proposition 1.3.30: in a unique factorization domain `A`, an element is irreducible if and
only if it is prime. Mathlib states this in the more general setting of a unique factorization
monoid. -/
recall UniqueFactorizationMonoid.irreducible_iff_prime
    {α : Type u} [CommMonoidWithZero α] [UniqueFactorizationMonoid α] {a : α} :
  Irreducible a ↔ Prime a
