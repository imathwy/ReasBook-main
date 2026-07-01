import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {R : Type u} [Semiring R]

/- Definition 1.3.3: polynomial divisibility is the canonical divisibility relation `(· ∣ ·)` on
`R[X]`; thus `A ∣ B` means that `B = A * P` for some polynomial `P`, equivalently that `B` is a
multiple of `A` and `A` is a factor of `B`. -/
#check ((· ∣ ·) : Polynomial R → Polynomial R → Prop)

/- Polynomial divisibility is characterized by existence of a polynomial quotient. -/
#check (dvd_iff_exists_eq_mul_right :
  ∀ {A B : Polynomial R}, A ∣ B ↔ ∃ P, B = A * P)

/- Polynomial nondivisibility is expressed directly as `¬ A ∣ B`. -/
variable (A B : Polynomial R)
#check (¬ A ∣ B)
