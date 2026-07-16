import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-- Theorem 1.1.74: Wilson's theorem in the textbook congruence form. For a natural number `p`
with `p ≠ 1`, the number `p` is prime if and only if `(p - 1)! ≡ -1 [ZMOD p]`. -/
theorem prime_iff_factorial_modEq_neg_one (p : ℕ) (hp : p ≠ 1) :
    Nat.Prime p ↔ (((p - 1).factorial : ℤ) ≡ -1 [ZMOD p]) := by
  rw [Nat.prime_iff_fac_equiv_neg_one hp]
  simpa using ZMod.intCast_eq_intCast_iff ((p - 1).factorial : ℤ) (-1) p
