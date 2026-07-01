import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u

variable {𝕜 : Type u} [NormedRing 𝕜]

/- Auxiliary canonical recall: absolute convergence of the range-indexed Cauchy-product
coefficients is already provided by mathlib. -/
recall summable_norm_sum_mul_range_of_summable_norm
    {f g : ℕ → 𝕜}
    (hf : Summable (fun n ↦ ‖f n‖))
    (hg : Summable (fun n ↦ ‖g n‖)) :
    Summable (fun n ↦ ‖∑ k ∈ Finset.range (n + 1), f k * g (n - k)‖)

/- Proposition 4.2: the Cauchy product of two absolutely convergent series converges to the
product of their sums; this is exactly mathlib's canonical range-indexed Cauchy-product theorem. -/
recall hasSum_sum_range_mul_of_summable_norm
    [CompleteSpace 𝕜]
    {f g : ℕ → 𝕜}
    (hf : Summable (fun n ↦ ‖f n‖))
    (hg : Summable (fun n ↦ ‖g n‖)) :
    HasSum (fun n ↦ ∑ k ∈ Finset.range (n + 1), f k * g (n - k))
      ((∑' n, f n) * ∑' n, g n)
