import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Definition 1.4.35: the textbook notion of a `K`-algebra structure on a ring is the
field-and-ring specialization of the canonical mathlib typeclass `Algebra R A`; in the setting
of this chapter, this specialization is `Algebra K A`. -/
recall Algebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] : Type (max u v)

section

variable {K : Type u} [Field K] {A : Type v} [Ring A] [Algebra K A]

/- A `K`-algebra is canonically a `K`-vector space. -/
#check (inferInstance : Module K A)

/- In a `K`-algebra, scalar multiplication is compatible with multiplication on the left. -/
#check Algebra.smul_mul_assoc

/- In a `K`-algebra, scalar multiplication is compatible with multiplication on the right. -/
#check Algebra.mul_smul_comm

end
