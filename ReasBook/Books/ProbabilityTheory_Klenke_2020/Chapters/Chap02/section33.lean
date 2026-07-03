import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_2_33 (from Items/Chap02) -/
open MeasureTheory ProbabilityTheory
open scoped NNReal

-- Proof sketch: realize the sum of two independent Poisson random variables via
-- `IndepFun.hasLaw_add`, so its law is the additive convolution `poissonMeasure r ∗
-- poissonMeasure s`. Then identify the point masses of that convolution with the textbook
-- binomial expansion and compare them with the point masses of `poissonMeasure (r + s)`.
/-- Example 2.33: The additive convolution of two Poisson laws on `ℕ` is again Poisson, with
parameter equal to the sum of the parameters. -/
theorem poissonMeasure_conv_poissonMeasure (r s : ℝ≥0) :
    poissonMeasure r ∗ poissonMeasure s = poissonMeasure (r + s) := sorry
