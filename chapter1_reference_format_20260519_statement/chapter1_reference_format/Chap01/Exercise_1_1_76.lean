import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-- Exercise 1.1.76 (1): for positive `m`, if `2^m + 1` is prime, then `m` is a power of `2`. -/
-- Proof sketch: specialize `Nat.pow_of_pow_add_prime` to the base `2`.
theorem prime_two_pow_add_one_exponent_is_two_pow (m : ℕ) (hm : m ≠ 0)
    (hprime : (2 ^ m + 1).Prime) : ∃ n : ℕ, m = 2 ^ n := by
  simpa using Nat.pow_of_pow_add_prime one_lt_two hm hprime

/-- Exercise 1.1.76 (2): for the Fermat numbers `Nat.fermatNumber n = 2^(2^n) + 1`, if `n < m`,
then `Nat.fermatNumber n` divides `Nat.fermatNumber m - 2`. -/
-- Proof sketch: use `Nat.prod_fermatNumber m = Nat.fermatNumber m - 2` and note that the factor
-- `Nat.fermatNumber n` appears in the product because `n ∈ Finset.range m`.
theorem fermatNumber_dvd_sub_two_of_lt (n m : ℕ) (h : n < m) :
    Nat.fermatNumber n ∣ Nat.fermatNumber m - 2 := by
  rw [← Nat.prod_fermatNumber m]
  exact Finset.dvd_prod_of_mem Nat.fermatNumber (Finset.mem_range.mpr h)

/-- Exercise 1.1.76 (3): distinct Fermat numbers have greatest common divisor `1`. -/
-- Proof sketch: rewrite the claim as coprimality and apply
-- `Nat.coprime_fermatNumber_fermatNumber`.
theorem gcd_fermatNumber_eq_one_of_ne (n m : ℕ) (h : n ≠ m) :
    Nat.gcd (Nat.fermatNumber n) (Nat.fermatNumber m) = 1 :=
  Nat.coprime_iff_gcd_eq_one.mp <| Nat.coprime_fermatNumber_fermatNumber h

/- Exercise 1.1.76 (4): there are infinitely many prime numbers.
This is the canonical theorem `Nat.infinite_setOf_prime`,
already recalled earlier in the chapter. -/
recall Nat.infinite_setOf_prime : Set.Infinite {p : ℕ | Nat.Prime p}
