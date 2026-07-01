import Mathlib.NumberTheory.Chebyshev

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Asymptotics Nat.Prime
open Filter

-- Proof sketch: use the canonical owner-level comparison
-- `Chebyshev.primeCounting_sub_theta_div_log_isBigO` together with
-- `Chebyshev.integral_theta_div_log_sq_isLittleO`, then combine these with the prime number
-- theorem input `θ x ~ x` to conclude that `π ⌊x⌋₊ ~ x / log x`.
/-- Remark 1.1.72: the prime number theorem asserts that the prime-counting function is
asymptotic to `x / log x`, so the density of prime numbers near `x` is described by `1 / log x`. -/
theorem prime_counting_asymptotic :
    (fun x : ℝ ↦ (π ⌊x⌋₊ : ℝ)) ~[atTop] (fun x ↦ x / Real.log x) := sorry
