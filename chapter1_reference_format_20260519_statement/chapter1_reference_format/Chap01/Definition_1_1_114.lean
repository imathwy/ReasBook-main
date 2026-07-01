import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Definition 1.1.114: the characteristic of a field `K`, and more generally of any semiring with
`1`, is the canonical natural number `ringChar K`; it is `0` exactly when the canonical
natural-number map has trivial kernel, and otherwise it is the positive generator of that kernel.
-/
recall ringChar (K : Type u) [NonAssocSemiring K] : ℕ

/- A ring has characteristic zero exactly when its canonical characteristic is `0`. -/
recall CharP.ringChar_zero_iff_CharZero (K : Type u) [NonAssocRing K] :
  ringChar K = 0 ↔ CharZero K

section

variable (K : Type u) [Field K]

/- A field has prime characteristic whenever its characteristic is nonzero. This is the canonical
specialization of `CharP.char_prime_of_ne_zero` to the instance `CharP K (ringChar K)`. -/
#check (CharP.char_prime_of_ne_zero K : ringChar K ≠ 0 → Nat.Prime (ringChar K))

end
