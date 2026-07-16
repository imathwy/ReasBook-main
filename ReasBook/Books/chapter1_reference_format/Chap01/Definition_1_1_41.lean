import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Definition 1.1.41: for a ring `R`, the textbook notion of ideal is the canonical bundled
two-sided ideal `TwoSidedIdeal R`; equivalently, it is a subset of `R` that is an additive
subgroup and absorbs multiplication on both the left and the right. Mathlib defines this owner
already in the slightly more general `NonUnitalNonAssocRing` setting. -/
recall TwoSidedIdeal (R : Type u) [NonUnitalNonAssocRing R] : Type u

/- The primitive constructor `TwoSidedIdeal.mk'` packages exactly the textbook data of an additive
subgroup closed under left and right multiplication into a bundled ideal. -/
#check TwoSidedIdeal.mk'
