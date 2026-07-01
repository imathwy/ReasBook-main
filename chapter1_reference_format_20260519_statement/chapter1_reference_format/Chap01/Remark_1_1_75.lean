import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Nat

/-- Remark 1.1.75: a Wilson prime is a prime number `p` such that `p^2` divides
`(p - 1)! + 1`. -/
def IsWilsonPrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ p ^ 2 ∣ (p - 1)! + 1

/-- A Wilson prime is, in particular, a prime number. -/
theorem IsWilsonPrime.prime {p : ℕ} (hp : IsWilsonPrime p) : Nat.Prime p :=
  hp.1

/-- For a Wilson prime `p`, the integer `(p - 1)! + 1` is divisible by `p^2`. -/
theorem IsWilsonPrime.sq_dvd_factorial_add_one {p : ℕ} (hp : IsWilsonPrime p) :
    p ^ 2 ∣ (p - 1)! + 1 :=
  hp.2
