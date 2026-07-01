import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Definition 1.1.112: a division ring structure on `K` is the canonical `DivisionRing K`
structure, namely an additive commutative group together with a multiplication for which the
nonzero elements form a group and which satisfies the distributive laws. -/
recall DivisionRing (K : Type u) : Type u

/- A field structure on `K` is the canonical `Field K` structure, namely a commutative division
ring. -/
recall Field (K : Type u) : Type u
