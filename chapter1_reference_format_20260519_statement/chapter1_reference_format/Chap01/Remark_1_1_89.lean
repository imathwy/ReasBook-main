import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Remark 1.1.89: historically, Fermat first proved the prime-modulus case of the theorem, and
Euler later generalized it to arbitrary modulus `n`; in mathlib, the general Euler theorem is the
canonical statement `Nat.ModEq.pow_totient`. -/
recall Nat.ModEq.pow_totient {x n : ℕ} (h : x.Coprime n) :
  x ^ n.totient ≡ 1 [MOD n]

/- The prime-modulus case mentioned in the remark is Fermat's little theorem. -/
recall Nat.ModEq.pow_card_sub_one_eq_one {p : ℕ} (hp : Nat.Prime p) {n : ℕ}
    (hpn : n.Coprime p) : n ^ (p - 1) ≡ 1 [MOD p]
