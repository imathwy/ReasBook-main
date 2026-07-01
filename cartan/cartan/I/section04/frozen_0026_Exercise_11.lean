import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Finset
open scoped BigOperators

-- Proof sketch: expand `(1 + z / n) ^ n` using the binomial theorem, rewrite the binomial
-- coefficient as a descending factorial divided by `p!`, and factor the descending factorial term
-- into the displayed product `∏_{j=1}^{p-1} (1 - j / n)`.
/-- Exercise 11 (1): for every integer `n ≥ 1`, the binomial expansion of `(1 + z / n)^n`
can be written as `1 + z` plus the higher-order terms whose coefficient of `z^p` is
`(∏_{j=1}^{p-1} (1 - j / n)) / p!`. -/
theorem one_add_div_pow_eq_one_add_sum_descending_product {n : ℕ} (hn : 1 ≤ n) (z : ℂ) :
    (1 + z / n) ^ n =
      1 + z +
        ∑ p ∈ Icc 2 n, (∏ j ∈ Icc 1 (p - 1), (1 - (j : ℂ) / n)) * z ^ p / (p.factorial : ℂ) :=
      sorry

/- Exercise 11 (2): mathlib's canonical limit theorem states that `(1 + z / n)^n`
converges to `Complex.exp z` as `n → ∞`. -/
recall Complex.tendsto_one_add_div_pow_exp
