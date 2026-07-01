import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {R : Type u} {S : Type v} [Ring R] [Ring S] (φ : R →+* S)

/- Proposition 1.1.44 (1): the image of a ring homomorphism `φ : R →+* S` is the canonical
subring `φ.range` of the target ring `S`. -/
#check φ.range

/- Proposition 1.1.44 (2): the kernel of a ring homomorphism `φ : R →+* S` is the canonical
two-sided ideal `TwoSidedIdeal.ker φ` of the source ring `R`. -/
#check TwoSidedIdeal.ker φ
