import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_30 (from Items/Chap15) -/
/- Lemma 15.30 is `source-facing`: its public content is the explicit Taylor remainder estimate
for the oscillatory scalar `t ↦ exp (it)`.

The owner abstractions for the proof are the interval-integral FTC identities for
`x ↦ Complex.exp ((x : ℂ) * Complex.I)`, the base-case bound
`Real.norm_exp_I_mul_ofReal_sub_one_le`, and the interval-integral moment formula
`integral_pow_abs_sub_uIoc`.

Accordingly, the public API stays as the textbook explicit partial-sum estimate; we do not add a
parallel local wrapper around `taylorWithinEval` or a local packaged Taylor object.
-/
-- Proof sketch: integrate the derivative identity for `x ↦ Complex.exp ((x : ℂ) * Complex.I)`
-- recursively. The base case is `Real.norm_exp_I_mul_ofReal_sub_one_le`, and each induction step
-- gains a factor `1 / n` from the interval-integral bound on `|x| ^ (n - 1)`.
/-- Lemma 15.30: for `t ∈ ℝ` and `n ∈ ℕ`, the remainder after truncating the Taylor series of
`exp (i t)` at order `n - 1` is bounded by `|t| ^ n / n!`. -/
theorem norm_exp_mul_I_sub_taylor_sum_le (t : ℝ) (n : ℕ) :
    ‖Complex.exp ((t : ℂ) * Complex.I) -
        Finset.sum (Finset.range n) (fun m ↦ (((t : ℂ) * Complex.I) ^ m) / m.factorial)‖ ≤
      |t| ^ n / n.factorial := sorry
