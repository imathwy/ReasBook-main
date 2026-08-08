import ProbabilityTheory_Klenke_2020.Chap14.Definition_14_46

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

namespace IsContinuousConvolutionSemigroup

/-- Exercise 14.4.4: if a continuous real convolution semigroup has one positive-time marginal
with zero mass on the negative half-line `(-∞, 0)`, then it satisfies the owner predicate
`IsNonnegativeConvolutionSemigroup`. -/
-- Proof sketch: use the convolution semigroup property to propagate the support condition from one
-- positive time to its rational subdivisions and multiples, then combine continuity at `0` with
-- weak convergence to extend the zero-mass property on `(-∞, 0)` to every time `t ≥ 0`.
theorem isNonnegative_of_exists_pos_measure_Iio_zero
    (ν : NNReal → ProbabilityMeasure ℝ)
    [IsContinuousConvolutionSemigroup ν]
    (h_nonneg_time : ∃ t > 0, (ν t : Measure ℝ) (Set.Iio 0) = 0) :
    IsNonnegativeConvolutionSemigroup ν := sorry

end IsContinuousConvolutionSemigroup
