import Mathlib
import AchimKlenkeLean.Items.Chap16.Definition_16_1
import AchimKlenkeLean.Items.Chap16.Definition_16_20

-- Declarations for this item will be appended below by the statement pipeline.

namespace MeasureTheory.ProbabilityMeasure

-- Proof sketch: extract the affine realizations of the convolution powers from
-- `IsStableInBroadSense.exists_scale_shift`; for each `n`, invert the corresponding affine map to
-- produce an `n`th convolution root of `μ`.
/-- Remark 16.21: if `μ` is stable in the broad sense, then it is infinitely divisible. -/
theorem isInfinitelyDivisible_of_isStableInBroadSense
    {μ : ProbabilityMeasure ℝ} (hμ : IsStableInBroadSense μ) :
    IsInfinitelyDivisible μ := by
  sorry

end MeasureTheory.ProbabilityMeasure
