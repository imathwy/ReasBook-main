import Mathlib

open scoped Topology
open Filter

/-- The leading digit in the base-`p` expansion of `n`, i.e. the last entry of `p.digits n`. -/
def baseLeadingDigit (p n : ℕ) : ℕ :=
  (p.digits n).getLastD 0

-- Proof sketch: for `n ≠ 0`, the base-`p` digit list of `n` is nonempty, so `getLastD` is the
-- actual last digit of `p.digits n`; then apply the canonical bound `Nat.digits_lt_base`.
/-- The leading digit of a nonzero natural number in base `p` is strictly less than `p`. -/
theorem baseLeadingDigit_lt_base {p n : ℕ} (hp : 1 < p) (hn : n ≠ 0) :
    baseLeadingDigit p n < p := by
  have hdigits : p.digits n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn
  rw [baseLeadingDigit, List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hdigits,
    Option.getD_some]
  exact Nat.digits_lt_base hp (List.getLast_mem hdigits)

-- Proof sketch: write the leading base-`p` digit of `q^i` as the indicator of the interval
-- `[log d / log p, log (d + 1) / log p)` for the fractional parts of `i * log q / log p`, then
-- apply equidistribution on the circle using the squarefreeness hypothesis on `p`.
/-- Exercise 20.3.2: for squarefree `p` and `2 ≤ q < p`, the leading base-`p` digits of `q^n`
satisfy Benford's law with logarithmic frequencies. -/
theorem powers_leading_digit_benford
    {p q d : ℕ} (hpSq : Squarefree p) (hq2 : 2 ≤ q) (hq_lt : q < p)
    (hd1 : 1 ≤ d) (hd_lt : d < p) :
    Tendsto
      (fun n : ℕ ↦
        (((Finset.Icc 1 n).filter fun i ↦ baseLeadingDigit p (q ^ i) = d).card : ℝ) / n)
      atTop
      (𝓝 ((Real.log (d + 1) - Real.log d) / Real.log p)) := sorry
