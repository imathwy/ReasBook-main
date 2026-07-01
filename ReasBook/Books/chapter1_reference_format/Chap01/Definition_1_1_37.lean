import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable (R : Type u) [Monoid R]

/- Definition 1.1.37: the invertible elements of a unital ring under multiplication are the
canonical bundled units `Units R`; this owner already lives at the more general monoid level and
is written `Rˣ`. -/
recall Units (R : Type u) [Monoid R] : Type u

/- The standard notation for the type of units of `R`. -/
#check Rˣ

/- The canonical group structure on the multiplicative group of units of `R`. -/
#check (inferInstance : Group Rˣ)
