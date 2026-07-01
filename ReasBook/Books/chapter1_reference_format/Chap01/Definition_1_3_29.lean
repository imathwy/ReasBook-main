import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Definition 1.3.29: for a commutative ring `R`, the textbook notion of unique factorization
domain is expressed in Lean by the canonical owner property `UniqueFactorizationMonoid R`; the
owner itself is defined at the more general level of commutative monoids with zero. -/
recall UniqueFactorizationMonoid (α : Type u) [CommMonoidWithZero α] : Prop
