import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {K : Type u} [Field K] {A : Type v} [Ring A] [Algebra K A]

/- Remark 1.4.36 is downstream from the canonical owner `Algebra K A` recalled in
`Definition_1_4_35`: no new algebra structure is introduced here. The associativity mentioned in
the remark is the standard ring multiplication law on the carrier of `A`. -/
#check (mul_assoc : ∀ a b c : A, (a * b) * c = a * (b * c))

end

section

variable {K : Type u} [Field K] {A : Type v} [CommRing A] [Algebra K A]

/- In the textbook's phrase "commutative `K`-algebra", the adjective "commutative" means exactly
that the underlying ring structure on `A` is commutative. -/
#check (inferInstance : CommRing A)

end
