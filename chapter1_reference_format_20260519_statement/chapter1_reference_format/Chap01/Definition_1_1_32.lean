import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Definition 1.1.32: a ring homomorphism is a map preserving `1`, addition, and multiplication;
mathlib's standard bundled notion is `RingHom R S`, with notation `R →+* S`, and it is available
in the more general semiring setting as well. -/
recall RingHom (R : Type u) (S : Type v) [NonAssocSemiring R] [NonAssocSemiring S] :
  Type (max u v)

variable {R : Type u} {S : Type v} [NonAssocSemiring R] [NonAssocSemiring S]

#check (R →+* S)
