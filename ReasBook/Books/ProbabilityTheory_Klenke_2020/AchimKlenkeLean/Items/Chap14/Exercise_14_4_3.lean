import ProbabilityTheory_Klenke_2020.Items.Chap14.Definition_14_46

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

namespace IsNonnegativeConvolutionSemigroup

variable {ν : NNReal → ProbabilityMeasure ℝ} [IsNonnegativeConvolutionSemigroup ν]

/-- Exercise 14.4.3: every nonnegative convolution semigroup on `[0, ∞)` with values in
probability measures on `ℝ` is continuous at the origin in the weak topology. -/
-- Proof sketch: use the nonnegativity assumption to identify the family as a subprobability
-- semigroup supported on `[0, ∞)`, then prove that the semigroup law forces the weak limit at
-- `t → 0` to be the Dirac mass at `0`.
instance toIsContinuousConvolutionSemigroup
    :
    IsContinuousConvolutionSemigroup ν := sorry

end IsNonnegativeConvolutionSemigroup
