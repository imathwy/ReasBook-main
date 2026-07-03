import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_16_9 (from Items/Chap16) -/
open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace MeasureTheory.ProbabilityMeasure

-- Proof sketch: fix a positive integer `k`. For each `n`, choose a `k`th convolution root `νₙ` of
-- `μs n`. Weak convergence gives pointwise convergence of the characteristic functions of `μs n`,
-- so Theorem 16.6 applies to the characteristic functions of the roots `νₙ` and yields a
-- probability measure whose `k`th convolution power is `μ`. Since `k` was arbitrary, `μ` is
-- infinitely divisible.
/-- Corollary 16.9: if a sequence of infinitely divisible probability measures on `ℝ` converges
weakly to a probability measure `μ`, then `μ` is infinitely divisible. -/
theorem isInfinitelyDivisible_of_tendsto
    {μs : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (hμs : ∀ n : ℕ, IsInfinitelyDivisible (μs n)) (hμ : Tendsto μs atTop (𝓝 μ)) :
    IsInfinitelyDivisible μ := sorry

end MeasureTheory.ProbabilityMeasure
