import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Proposition 1.1.73: if `p` is a prime number and `k ∈ {1, …, p - 1}` (equivalently,
`k ≠ 0` and `k < p` in `ℕ`), then `p` divides the binomial coefficient `Nat.choose p k`. -/
recall Nat.Prime.dvd_choose_self {p k : ℕ} (hp : Nat.Prime p) (hk : k ≠ 0) (hkp : k < p) :
  p ∣ Nat.choose p k
