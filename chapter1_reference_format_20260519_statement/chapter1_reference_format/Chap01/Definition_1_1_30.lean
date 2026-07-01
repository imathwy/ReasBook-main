import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable (R : Type u)

/- Definition 1.1.30: in this chapter's convention, a ring on `R` is the canonical
`NonUnitalRing R` structure, namely an additive commutative group together with an associative
multiplication and the distributive laws, but without a distinguished multiplicative identity. -/
recall NonUnitalRing (R : Type u) : Type u

/- A unital ring is the stronger canonical `Ring R` structure. -/
#check Ring R

/- A commutative ring in this chapter's convention is the canonical `NonUnitalCommRing R`
structure, namely a ring whose multiplication is commutative. -/
recall NonUnitalCommRing (R : Type u) : Type u
