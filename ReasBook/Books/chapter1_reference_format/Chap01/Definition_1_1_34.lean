import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable (R : Type u) [NonUnitalNonAssocRing R]

/- Definition 1.1.34: for a ring `R`, a subring is an additive subgroup of `(R, +)` that is
closed under multiplication; the standard bundled owner is `NonUnitalSubring R`, which mathlib
defines already in the slightly more general `NonUnitalNonAssocRing` setting. -/
recall NonUnitalSubring (R : Type u) [NonUnitalNonAssocRing R] : Type u

/- The additive-subgroup part of a non-unital subring. -/
#check (NonUnitalSubring.toAddSubgroup : NonUnitalSubring R → AddSubgroup R)

/- The multiplicatively closed part of a non-unital subring. -/
#check (NonUnitalSubring.toNonUnitalSubsemiring : NonUnitalSubring R → NonUnitalSubsemiring R)
