import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Finset
open scoped BigOperators

-- Proof sketch: expand `(1 + z / n) ^ n` using the binomial theorem, rewrite the binomial
-- coefficient as a descending factorial divided by `p!`, and factor the descending factorial term
-- into the displayed product `∏_{j=1}^{p-1} (1 - j / n)`.
/-- Helper for Cartan section04 frozen_0026_Exercise_11: split the binomial sum into its constant,
linear, and higher-order terms. -/
lemma binomial_sum_split_zero_one_tail {n : ℕ} (hn : 1 ≤ n) (z : ℂ) :
    ∑ p ∈ range (n + 1), (z / n) ^ p * (n.choose p : ℂ) =
      1 + z + ∑ p ∈ Icc 2 n, (z / n) ^ p * (n.choose p : ℂ) := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have h0 : insert 0 (Icc 1 n) = Icc 0 n := insert_Icc_add_one_left_eq_Icc (Nat.zero_le n)
  have h1 : insert 1 (Icc 2 n) = Icc 1 n := insert_Icc_add_one_left_eq_Icc hn
  -- Rewrite the full range as a closed interval and peel off the first two summands.
  rw [Nat.range_succ_eq_Icc_zero]
  rw [← h0]
  rw [sum_insert]
  · rw [← h1]
    rw [sum_insert]
    · -- The `p = 0` and `p = 1` contributions simplify to `1` and `z`.
      have hz : z / (n : ℂ) * (n : ℂ) = z := by
        rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hn0, mul_one]
      rw [pow_zero, Nat.choose_zero_right, pow_one, Nat.choose_one_right]
      simp [hz, add_assoc]
    · simp
  · simp

/-- Helper for Cartan section04 frozen_0026_Exercise_11: the cast descending factorial equals
`n^p` times the normalized descending product appearing in the coefficient. -/
lemma cast_descFactorial_eq_natCast_pow_mul_prod_Icc {n p : ℕ} (hn : 1 ≤ n) (hp : p ≤ n) :
    (n.descFactorial p : ℂ) = (n : ℂ) ^ p * ∏ j ∈ Icc 1 (p - 1), (1 - (j : ℂ) / n) := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  induction p with
  | zero =>
      -- At `p = 0`, both sides are empty products.
      simp
  | succ p ih =>
      cases p with
      | zero =>
          -- At `p = 1`, the interval product is empty.
          simp
      | succ q =>
          have hp' : q + 1 ≤ n := Nat.le_trans (Nat.le_succ (q + 1)) hp
          have hlt : q + 1 < n := lt_of_lt_of_le (Nat.lt_succ_self (q + 1)) hp
          have hrec :
              (n.descFactorial (q + 1) : ℂ) =
                (n : ℂ) ^ (q + 1) * ∏ j ∈ Icc 1 q, (1 - (j : ℂ) / n) :=
            ih hp'
          have hfactor :
              (((n - (q + 1) : ℕ) : ℂ)) = (n : ℂ) * (1 - ((q + 1 : ℕ) : ℂ) / n) := by
            rw [Nat.cast_sub hlt.le]
            rw [mul_sub, mul_one, ← mul_div_assoc, mul_div_cancel_left₀ _ hn0]
          have hinsert : insert (q + 1) (Icc 1 q) = Icc 1 (q + 1) := by
            exact insert_Icc_right_eq_Icc_add_one (by simp)
          have hnot : q + 1 ∉ Icc 1 q := by
            simp
          -- Route correction: extend the interval product by the new right endpoint.
          calc
            (n.descFactorial (q + 2) : ℂ) =
                (((n - (q + 1) : ℕ) : ℂ)) * (n.descFactorial (q + 1) : ℂ) := by
                  rw [Nat.descFactorial, Nat.cast_mul]
            _ = ((n : ℂ) * (1 - ((q + 1 : ℕ) : ℂ) / n)) *
                  ((n : ℂ) ^ (q + 1) * ∏ j ∈ Icc 1 q, (1 - (j : ℂ) / n)) := by
                  rw [hfactor, hrec]
            _ = ((n : ℂ) ^ (q + 1) * (n : ℂ)) *
                  ((1 - ((q + 1 : ℕ) : ℂ) / n) * ∏ j ∈ Icc 1 q, (1 - (j : ℂ) / n)) := by
                  ac_rfl
            _ = (((n : ℂ) ^ q * (n : ℂ)) * (n : ℂ)) *
                  ((1 - ((q + 1 : ℕ) : ℂ) / n) * ∏ j ∈ Icc 1 q, (1 - (j : ℂ) / n)) := by
                  rw [pow_succ]
            _ = (n : ℂ) ^ (q + 2) *
                  ((1 - ((q + 1 : ℕ) : ℂ) / n) * ∏ j ∈ Icc 1 q, (1 - (j : ℂ) / n)) := by
                  rw [pow_succ, pow_succ]
            _ = (n : ℂ) ^ (q + 2) * ∏ j ∈ Icc 1 (q + 1), (1 - (j : ℂ) / n) := by
                  rw [← hinsert, prod_insert hnot]

/-- Helper for Cartan section04 frozen_0026_Exercise_11: rewrite each binomial tail coefficient as
the normalized descending product divided by `p!`. -/
lemma binomial_term_eq_descending_product {n p : ℕ} (hn : 1 ≤ n) (hp : p ≤ n) (z : ℂ) :
    (z / n) ^ p * (n.choose p : ℂ) =
      (∏ j ∈ Icc 1 (p - 1), (1 - (j : ℂ) / n)) * z ^ p / (p.factorial : ℂ) := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hfact0 : (p.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr p.factorial_ne_zero
  have hchoose_mul :
      (n.descFactorial p : ℂ) = (p.factorial : ℂ) * (n.choose p : ℂ) := by
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose n p
  have hchoose : (n.choose p : ℂ) = (n.descFactorial p : ℂ) / (p.factorial : ℂ) := by
    apply (eq_div_iff hfact0).2
    rw [mul_comm]
    exact hchoose_mul.symm
  have hdesc_div :
      (n.descFactorial p : ℂ) / (n : ℂ) ^ p =
        ∏ j ∈ Icc 1 (p - 1), (1 - (j : ℂ) / n) := by
    apply (div_eq_iff (pow_ne_zero p hn0)).2
    rw [mul_comm]
    exact cast_descFactorial_eq_natCast_pow_mul_prod_Icc hn hp
  -- Rewrite the binomial coefficient through the descending factorial identity.
  calc
    (z / n) ^ p * (n.choose p : ℂ) =
        (z ^ p / (n : ℂ) ^ p) * ((n.descFactorial p : ℂ) / (p.factorial : ℂ)) := by
          rw [div_pow, hchoose]
    _ = ((n.descFactorial p : ℂ) / (n : ℂ) ^ p) * z ^ p / (p.factorial : ℂ) := by
          rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
          ac_rfl
    _ = (∏ j ∈ Icc 1 (p - 1), (1 - (j : ℂ) / n)) * z ^ p / (p.factorial : ℂ) := by
          rw [hdesc_div]

/-- Cartan section04 frozen_0026_Exercise_11: for every integer `n ≥ 1`, the binomial expansion of
`(1 + z / n)^n`
can be written as `1 + z` plus the higher-order terms whose coefficient of `z^p` is
`(∏_{j=1}^{p-1} (1 - j / n)) / p!`. -/
theorem one_add_div_pow_eq_one_add_sum_descending_product {n : ℕ} (hn : 1 ≤ n) (z : ℂ) :
    (1 + z / n) ^ n =
      1 + z +
        ∑ p ∈ Icc 2 n, (∏ j ∈ Icc 1 (p - 1), (1 - (j : ℂ) / n)) * z ^ p / (p.factorial : ℂ) :=
  calc
    (1 + z / n) ^ n = ∑ p ∈ range (n + 1), (z / n) ^ p * (n.choose p : ℂ) := by
      -- Expand by the binomial theorem and simplify the powers of `1`.
      simpa [add_comm, one_pow, mul_assoc] using (add_pow (z / n) (1 : ℂ) n)
    _ = 1 + z + ∑ p ∈ Icc 2 n, (z / n) ^ p * (n.choose p : ℂ) := by
      -- Separate the constant and linear coefficients from the tail.
      exact binomial_sum_split_zero_one_tail hn z
    _ = 1 + z +
          ∑ p ∈ Icc 2 n, (∏ j ∈ Icc 1 (p - 1), (1 - (j : ℂ) / n)) * z ^ p / (p.factorial : ℂ) := by
      -- Rewrite each tail coefficient in the textbook product form.
      refine congrArg (fun s ↦ 1 + z + s) ?_
      apply sum_congr rfl
      intro p hp
      exact binomial_term_eq_descending_product hn (mem_Icc.mp hp).2 z

/- Exercise 11 (2): mathlib's canonical limit theorem states that `(1 + z / n)^n`
converges to `Complex.exp z` as `n → ∞`. -/
recall Complex.tendsto_one_add_div_pow_exp
