import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Function

section

variable {R : Type u} [CommRing R]
variable {ι : Type v} [Finite ι]

/- Theorem 1.1.102: for a finite family of pairwise coprime ideals in a commutative ring, the
Chinese remainder theorem is the canonical ring equivalence
`Ideal.quotientInfRingEquivPiQuotient`. -/
recall Ideal.quotientInfRingEquivPiQuotient

end
