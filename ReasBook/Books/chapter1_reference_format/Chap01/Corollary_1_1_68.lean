import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-- Corollary 1.1.68 (1): for positive natural numbers `a` and `b`, the greatest common
divisor is the product of prime powers whose exponents are the pointwise minima of the
exponents in the prime factorizations of `a` and `b`. -/
-- Proof sketch: rewrite the factorization of `Nat.gcd a b` using `Nat.factorization_gcd`,
-- then reconstruct the number from its factorization via `Nat.prod_factorization_pow_eq_self`.
theorem gcd_eq_factorization_inf_prod (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Nat.gcd a b = (a.factorization ⊓ b.factorization).prod (· ^ ·) := by
  rw [← Nat.prod_factorization_pow_eq_self (Nat.gcd_ne_zero_left ha.ne'),
    Nat.factorization_gcd ha.ne' hb.ne']

/-- Corollary 1.1.68 (2): for positive natural numbers `a` and `b`, the least common
multiple is the product of prime powers whose exponents are the pointwise maxima of the
exponents in the prime factorizations of `a` and `b`. -/
-- Proof sketch: use `Nat.factorization_lcm` to identify the factorization of `Nat.lcm a b`
-- with `a.factorization ⊔ b.factorization`, then reconstruct the number from its
-- factorization with `Nat.prod_factorization_pow_eq_self`.
theorem lcm_eq_factorization_sup_prod (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Nat.lcm a b = (a.factorization ⊔ b.factorization).prod (· ^ ·) := by
  rw [← Nat.prod_factorization_pow_eq_self (Nat.lcm_ne_zero ha.ne' hb.ne'),
    Nat.factorization_lcm ha.ne' hb.ne']
