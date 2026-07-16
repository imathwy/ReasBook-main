import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable (R : Type u)

/- Remark 1.1.31: when no confusion can arise, one usually writes a ring `(R, +, ·)` simply as
the ring `R`. In this chapter, that ambient ring structure is the canonical `NonUnitalRing R`
recalled in Definition 1.1.30. -/
#check NonUnitalRing R
