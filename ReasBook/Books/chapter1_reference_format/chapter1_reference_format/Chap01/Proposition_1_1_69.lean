import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-- Proposition 1.1.69: if a prime number `p` does not divide a natural number `a`, then `p` and
`a` are coprime. -/
theorem coprime_of_prime_not_dvd {p a : ℕ} (hp : Nat.Prime p) (hpa : ¬ p ∣ a) :
    Nat.Coprime p a :=
  (hp.coprime_iff_not_dvd).2 hpa
