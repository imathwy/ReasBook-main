import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 1.1.59: [Gauss] for integers `a`, `b`, and `c`, if `a ∣ b * c` and `Int.gcd a b = 1`,
then `a ∣ c`. This is exactly `Int.dvd_of_dvd_mul_right_of_gcd_one`. -/
recall Int.dvd_of_dvd_mul_right_of_gcd_one {a b c : ℤ} (habc : a ∣ b * c)
    (hab : Int.gcd a b = 1) : a ∣ c
