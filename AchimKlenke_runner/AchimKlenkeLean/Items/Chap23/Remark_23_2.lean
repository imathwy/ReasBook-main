import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Set

noncomputable section

namespace ProbabilityTheory

/-- The finite-value branch of the Bernoulli Cramér rate function, namely
`((1 + x) log (1 + x) + (1 - x) log (1 - x)) / 2`. -/
def bernoulliCramerRateFunction (x : ℝ) : ℝ :=
  ((1 + x) * Real.log (1 + x) + (1 - x) * Real.log (1 - x)) / 2

-- Proof sketch: combine mathlib's canonical continuity theorem `Real.continuous_mul_log` with the
-- affine maps `x ↦ 1 + x` and `x ↦ 1 - x`; on `[-1,1]` both arguments stay in `[0,2]`, so the sum
-- and scalar multiple remain continuous.
/-- Remark 23.2: with the convention `0 log 0 = 0`, the restriction of the Bernoulli Cramér rate
function to `[-1,1]` is continuous. -/
theorem bernoulliCramerRateFunction_continuousOn :
    ContinuousOn bernoulliCramerRateFunction (Icc (-1 : ℝ) 1) := sorry

-- Proof sketch: substitute `x = -1` into the explicit formula; the `0 log 0` term vanishes and
-- the remaining term is `(2 * log 2) / 2`.
/-- The Bernoulli Cramér rate function takes the endpoint value `log 2` at `-1`. -/
theorem bernoulliCramerRateFunction_neg_one :
    bernoulliCramerRateFunction (-1) = Real.log 2 := sorry

-- Proof sketch: substitute `x = 1` into the explicit formula; again the `0 log 0` term vanishes
-- and the remaining term is `(2 * log 2) / 2`.
/-- The Bernoulli Cramér rate function takes the endpoint value `log 2` at `1`. -/
theorem bernoulliCramerRateFunction_one :
    bernoulliCramerRateFunction 1 = Real.log 2 := sorry

-- Proof sketch: combine the canonical strict convexity of `x ↦ x * Real.log x` on `Ici 0` given by
-- `Real.strictConvexOn_mul_log` with the affine maps `x ↦ 1 + x` and `x ↦ 1 - x`, then use the
-- endpoint continuity to extend strict convexity to the closed interval.
/-- The Bernoulli Cramér rate function is strictly convex on `[-1,1]`. -/
theorem bernoulliCramerRateFunction_strictConvexOn :
    StrictConvexOn ℝ (Icc (-1 : ℝ) 1) bernoulliCramerRateFunction := sorry

-- Proof sketch: evaluate the explicit formula at `x = 0`; both logarithmic terms are
-- `1 * log 1 = 0`.
/-- The Bernoulli Cramér rate function vanishes at the origin. -/
theorem bernoulliCramerRateFunction_zero :
    bernoulliCramerRateFunction 0 = 0 := sorry

-- Proof sketch: the derivative of the explicit formula is nonnegative on `[0,1]`, so the
-- function is monotone increasing there.
/-- The Bernoulli Cramér rate function is monotone increasing on `[0,1]`. -/
theorem bernoulliCramerRateFunction_monotoneOn_nonneg :
    MonotoneOn bernoulliCramerRateFunction (Icc (0 : ℝ) 1) := sorry

-- Proof sketch: the derivative of the explicit formula is nonpositive on `[-1,0]`, so the
-- function is monotone decreasing there.
/-- The Bernoulli Cramér rate function is monotone decreasing on `[-1,0]`. -/
theorem bernoulliCramerRateFunction_antitoneOn_nonpos :
    AntitoneOn bernoulliCramerRateFunction (Icc (-1 : ℝ) 0) := sorry

end ProbabilityTheory
