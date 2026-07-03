import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_8_27 (from Chap08) -/
section

/- Lemma 8.27 is `source-facing`: it records two explicit bounds for ratios of finite sums of the
harmonic sequence and the inverse-square-root sequence that appear in the dynamic stepsize
analysis. The canonical owners here are `Finset.range` and `Finset.Icc` for the finite sums, with
`Real.log` and `Real.sqrt` for the analytic bounds, so the two textbook clauses are formalized as
atomic real inequalities without introducing any surrogate wrapper for these sum ratios. -/

-- Proof sketch: bound the numerator by
-- `D + 1 + log (k + 1)` using the integral comparison from Lemma 8.26 for `x ↦ 1 / (x + 1)`,
-- and bound the denominator below by `sqrt (k + 1)` using the same comparison for
-- `x ↦ 1 / sqrt (x + 1)`. Dividing the two estimates gives the displayed ratio bound.
/-- Lemma 8.27 (1): for every real `D` and every `k ≥ 1`, the ratio of the prefix harmonic sum
shifted by `D` to the corresponding prefix inverse-square-root sum is bounded by
`(D + 1 + log (k + 1)) / √(k + 1)` as in equation (8.30). -/
lemma harmonic_prefix_ratio_le_log_bound
    (D : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    (D + Finset.sum (Finset.range (k + 1)) (fun n ↦ 1 / ((n : ℝ) + 1))) /
        Finset.sum (Finset.range (k + 1)) (fun n ↦ 1 / Real.sqrt ((n : ℝ) + 1)) ≤
      (D + 1 + Real.log ((k : ℝ) + 1)) / Real.sqrt ((k : ℝ) + 1) := sorry

-- Proof sketch: compare the numerator with the integral of `x ↦ 1 / (x + 1)` over
-- `[⌊k / 2⌋, k]` to get the upper bound `log 3`, then compare the denominator with the integral of
-- `x ↦ 1 / sqrt (x + 1)` over the same range to get the lower bound `sqrt (k + 2) / 4`. The
-- resulting quotient estimate is equation (8.31).
/-- Lemma 8.27 (2): for every real `D` and every `k ≥ 2`, the ratio of the tail sums from
`⌊k / 2⌋` to `k` is bounded by `4 (D + log 3) / √(k + 2)` as in equation (8.31). -/
lemma harmonic_half_tail_ratio_le_log_three_bound
    (D : ℝ) (k : ℕ) (hk : 2 ≤ k) :
    (D + Finset.sum (Finset.Icc (k / 2) k) (fun n ↦ 1 / ((n : ℝ) + 1))) /
        Finset.sum (Finset.Icc (k / 2) k) (fun n ↦ 1 / Real.sqrt ((n : ℝ) + 1)) ≤
      (4 * (D + Real.log 3)) / Real.sqrt ((k : ℝ) + 2) := sorry

end
