import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 1.1.39: integer divisibility is the canonical relation `(· ∣ ·)` on `ℤ`; `a ∣ b`
means that `b` is an integer multiple of `a`, equivalently that `a` is a factor of `b`. -/
#check ((· ∣ ·) : ℤ → ℤ → Prop)

/- Integer divisibility is characterized by existence of an integer quotient. -/
#check (dvd_iff_exists_eq_mul_right : ∀ {a b : ℤ}, a ∣ b ↔ ∃ n : ℤ, b = a * n)

/- Integer non-divisibility is the negation of the canonical divisibility relation. -/
#check (fun a b : ℤ ↦ ¬ (a ∣ b))
