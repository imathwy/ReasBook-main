import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {R : Type u} [NonUnitalNonAssocRing R]
variable {ι : Type v} {S : Set (TwoSidedIdeal R)} {x : R}
variable (s : Finset ι) (I : ι → TwoSidedIdeal R)

/- Proposition 1.1.45 (1): arbitrary intersections of two-sided ideals are again two-sided ideals;
equivalently, membership in `sInf S` means membership in every ideal in the family `S`. -/
recall TwoSidedIdeal.mem_sInf :
  x ∈ sInf S ↔ ∀ J ∈ S, x ∈ J

/- Proposition 1.1.45 (2): a finite family of two-sided ideals has a canonical supremum `s.sup I`,
which is the finite iterated sum ideal. -/
#check (s.sup I : TwoSidedIdeal R)
