import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Definition 1.1.20: a monoid structure on `M` is the canonical `Monoid M` structure, namely a
binary operation on `M` that is associative and has a two-sided unit. -/
recall Monoid (M : Type u) : Type u

/- A commutative monoid structure on `M` is the canonical `CommMonoid M` structure, namely a
monoid structure whose multiplication is commutative. -/
recall CommMonoid (M : Type u) : Type u
