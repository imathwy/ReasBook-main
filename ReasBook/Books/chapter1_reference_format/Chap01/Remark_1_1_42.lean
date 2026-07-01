import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable (R : Type u) [Ring R]

/- Remark 1.1.42: in a unital ring, the textbook's notion of ideal is the standard two-sided ideal
notion. The corresponding one-sided notions are the usual left ideals `Ideal R` and right ideals
`Ideal Rᵐᵒᵖ` of the opposite ring. -/
#check (TwoSidedIdeal R)

/- The canonical left-ideal view of a two-sided ideal is the order hom `TwoSidedIdeal.asIdeal`. -/
#check (TwoSidedIdeal.asIdeal : TwoSidedIdeal R →o Ideal R)

/- The canonical right-ideal view of a two-sided ideal is `TwoSidedIdeal.asIdealOpposite`. -/
#check (TwoSidedIdeal.asIdealOpposite : TwoSidedIdeal R →o Ideal Rᵐᵒᵖ)

/- A two-sided ideal containing `1` is the whole ring, so every proper ideal is a non-unital
subring of the ambient unital ring. -/
#check TwoSidedIdeal.one_mem_iff

variable (A : Type u) [CommRing A]

/- In the commutative case, the left and right absorption conditions coincide, so two-sided ideals
agree with the usual ideals. -/
#check (TwoSidedIdeal.orderIsoIdeal : TwoSidedIdeal A ≃o Ideal A)
