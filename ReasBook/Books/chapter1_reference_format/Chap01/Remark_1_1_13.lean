import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Remark 1.1.13: when no confusion arises, the multiplication of natural numbers may be written
in multiplicative notation; in Lean, the notation `a * b` is the standard surface syntax for the
canonical multiplication on `ℕ` (implemented by `Nat.mul`). -/
#check ((· * ·) : ℕ → ℕ → ℕ)
