import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R]

/- Remark 1.4.47: the earlier textbook definition of prime ideal was limited to the principal ideal
domain setting. For a general commutative ring with unity, prime ideals are described by the
canonical predicate `Ideal.IsPrime : Ideal R → Prop`. -/
#check (Ideal.IsPrime : Ideal R → Prop)

end
