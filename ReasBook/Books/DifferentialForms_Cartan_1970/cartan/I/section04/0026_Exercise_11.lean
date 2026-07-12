import Mathlib

open Finset
open scoped BigOperators

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: `lean_leansearch` was unavailable in this session, so the owner/API choice
-- was checked directly against Mathlib's binomial-theorem interface
-- (`add_pow`, `Nat.choose_eq_descFactorial_div_factorial`) and the canonical complex limit theorem
-- `Complex.tendsto_one_add_div_pow_exp`.

/-- Helper for Exercise 11: split the binomial sum into its constant, linear, and higher-order
terms. -/
lemma binomial_sum_split_zero_one_tail {k : Type*} [Field k] [CharZero k] {n : ℕ} (hn : 1 ≤ n)
    (z : k) :
    ∑ p ∈ range (n + 1), (z / n) ^ p * (n.choose p : k) =
      1 + z + ∑ p ∈ Icc 2 n, (z / n) ^ p * (n.choose p : k) := by
  have hn0 : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have h0 : insert 0 (Icc 1 n) = Icc 0 n := insert_Icc_add_one_left_eq_Icc (Nat.zero_le n)
  have h1 : insert 1 (Icc 2 n) = Icc 1 n := insert_Icc_add_one_left_eq_Icc hn
  -- Rewrite the range as a closed interval and peel off the `p = 0` and `p = 1` terms.
  rw [Nat.range_succ_eq_Icc_zero]
  rw [← h0]
  rw [sum_insert]
  · rw [← h1]
    rw [sum_insert]
    · -- The edge terms simplify to `1` and `z`.
      have hz : z / (n : k) * (n : k) = z := by
        rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hn0, mul_one]
      rw [pow_zero, Nat.choose_zero_right, pow_one, Nat.choose_one_right]
      simp [hz, add_assoc]
    · simp
  · simp

/-- Helper for Exercise 11: the descending factorial of `n` is `n^p` times the normalized
descending product appearing in the textbook coefficient. -/
lemma cast_descFactorial_eq_natCast_pow_mul_prod_Icc {k : Type*} [Field k] [CharZero k]
    {n p : ℕ} (hn : 1 ≤ n) (hp : p ≤ n) :
    (n.descFactorial p : k) =
      (n : k) ^ p * ∏ j ∈ Icc 1 (p - 1), (1 - (j : k) / n) := by
  have hn0 : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  induction p with
  | zero =>
      -- At `p = 0`, both sides are the empty product.
      simp
  | succ p ih =>
      cases p with
      | zero =>
          -- At `p = 1`, the interval product is empty, so only the leading factor `n` remains.
          simp
      | succ q =>
          have hp' : q + 1 ≤ n := Nat.le_trans (Nat.le_succ (q + 1)) hp
          have hlt : q + 1 < n := lt_of_lt_of_le (Nat.lt_succ_self (q + 1)) hp
          have hrec :
              (n.descFactorial (q + 1) : k) =
                (n : k) ^ (q + 1) * ∏ j ∈ Icc 1 q, (1 - (j : k) / n) :=
            ih hp'
          have hfactor :
              (((n - (q + 1) : ℕ) : k)) =
                (n : k) * (1 - ((q + 1 : ℕ) : k) / n) := by
            rw [Nat.cast_sub hlt.le]
            rw [mul_sub, mul_one, ← mul_div_assoc, mul_div_cancel_left₀ _ hn0]
          have hinsert : insert (q + 1) (Icc 1 q) = Icc 1 (q + 1) := by
            exact insert_Icc_right_eq_Icc_add_one (by simp)
          have hnot : q + 1 ∉ Icc 1 q := by
            simp
          -- Route correction: instead of unfolding the whole product, extend the interval product
          -- by the new right-endpoint factor and reuse the induction hypothesis.
          calc
            (n.descFactorial (q + 2) : k)
                = (((n - (q + 1) : ℕ) : k)) * (n.descFactorial (q + 1) : k) := by
                    rw [Nat.descFactorial, Nat.cast_mul]
            _ = ((n : k) * (1 - ((q + 1 : ℕ) : k) / n)) *
                  ((n : k) ^ (q + 1) * ∏ j ∈ Icc 1 q, (1 - (j : k) / n)) := by
                    rw [hfactor, hrec]
            _ = ((n : k) ^ (q + 1) * (n : k)) *
                  ((1 - ((q + 1 : ℕ) : k) / n) * ∏ j ∈ Icc 1 q, (1 - (j : k) / n)) := by
                    ac_rfl
            _ = (((n : k) ^ q * (n : k)) * (n : k)) *
                  ((1 - ((q + 1 : ℕ) : k) / n) * ∏ j ∈ Icc 1 q, (1 - (j : k) / n)) := by
                    rw [pow_succ]
            _ = (n : k) ^ (q + 2) *
                  ((1 - ((q + 1 : ℕ) : k) / n) * ∏ j ∈ Icc 1 q, (1 - (j : k) / n)) := by
                    rw [pow_succ, pow_succ]
            _ = (n : k) ^ (q + 2) * ∏ j ∈ Icc 1 (q + 1), (1 - (j : k) / n) := by
                    rw [← hinsert, prod_insert hnot]

/-- Helper for Exercise 11: each binomial tail coefficient rewrites to the normalized descending
product divided by `p!`. -/
lemma binomial_term_eq_descending_product {k : Type*} [Field k] [CharZero k] {n p : ℕ}
    (hn : 1 ≤ n) (hp : p ≤ n) (z : k) :
    (z / n) ^ p * (n.choose p : k) =
      (∏ j ∈ Icc 1 (p - 1), (1 - (j : k) / n)) * z ^ p / (p.factorial : k) := by
  have hn0 : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hfact0 : (p.factorial : k) ≠ 0 := Nat.cast_ne_zero.mpr p.factorial_ne_zero
  have hchoose_mul :
      (n.descFactorial p : k) = (p.factorial : k) * (n.choose p : k) := by
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose n p
  have hchoose :
      (n.choose p : k) = (n.descFactorial p : k) / (p.factorial : k) := by
    apply (eq_div_iff hfact0).2
    rw [mul_comm]
    exact hchoose_mul.symm
  have hdesc_div :
      (n.descFactorial p : k) / (n : k) ^ p =
        ∏ j ∈ Icc 1 (p - 1), (1 - (j : k) / n) := by
    apply (div_eq_iff (pow_ne_zero p hn0)).2
    rw [mul_comm]
    exact cast_descFactorial_eq_natCast_pow_mul_prod_Icc (k := k) hn hp
  -- Rewrite the binomial coefficient via descending factorial, then commute the scalar factors.
  calc
    (z / n) ^ p * (n.choose p : k)
        = (z ^ p / (n : k) ^ p) * ((n.descFactorial p : k) / (p.factorial : k)) := by
            rw [div_pow, hchoose]
    _ = ((n.descFactorial p : k) / (n : k) ^ p) * z ^ p / (p.factorial : k) := by
            rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
            ac_rfl
    _ = (∏ j ∈ Icc 1 (p - 1), (1 - (j : k) / n)) * z ^ p / (p.factorial : k) := by
            rw [hdesc_div]

/-- Exercise 11 (1): for every integer `n ≥ 1`, the binomial expansion of `(1 + z / n)^n`
can be written as `1 + z` plus the higher-order terms whose coefficient of `z^p` is
`(∏_{j=1}^{p-1} (1 - j / n)) / p!`. -/
theorem one_add_div_pow_eq_one_add_sum_descending_product {k : Type*} [Field k] [CharZero k]
    {n : ℕ} (hn : 1 ≤ n) (z : k) :
    (1 + z / n) ^ n =
      1 + z +
        ∑ p ∈ Icc 2 n, (∏ j ∈ Icc 1 (p - 1), (1 - (j : k) / n)) * z ^ p / (p.factorial : k) :=
  calc
    (1 + z / n) ^ n = ∑ p ∈ range (n + 1), (z / n) ^ p * (n.choose p : k) := by
      -- Expand by the binomial theorem and simplify the powers of `1`.
      simpa [add_comm, one_pow, mul_assoc] using (add_pow (z / n) (1 : k) n)
    _ = 1 + z + ∑ p ∈ Icc 2 n, (z / n) ^ p * (n.choose p : k) := by
      -- Separate the constant and linear coefficients from the tail.
      exact binomial_sum_split_zero_one_tail (k := k) hn z
    _ = 1 + z +
          ∑ p ∈ Icc 2 n, (∏ j ∈ Icc 1 (p - 1), (1 - (j : k) / n)) * z ^ p / (p.factorial : k) := by
      -- Rewrite each tail coefficient by the descending-factorial identity.
      refine congrArg (fun s ↦ 1 + z + s) ?_
      apply sum_congr rfl
      intro p hp
      exact binomial_term_eq_descending_product (k := k) hn (mem_Icc.mp hp).2 z

/- Exercise 11 (2): mathlib's canonical limit theorem states that `(1 + z / n)^n`
converges to `Complex.exp z` as `n → ∞`. -/
recall Complex.tendsto_one_add_div_pow_exp
