import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_16_7 (from Items/Chap16) -/
open Filter MeasureTheory ProbabilityTheory

noncomputable section

section

variable {φs : ℕ → ℝ → ℂ} {ψ : ℝ → ℂ}

variable (hcfp : ∀ n : ℕ, IsCFP (φs n))
variable (hlin : ∀ t : ℝ, Tendsto (fun n : ℕ ↦ (n : ℂ) * (φs n t - 1)) atTop (nhds (ψ t)))
variable (hψ_cont : ContinuousAt ψ 0)

-- Proof sketch: if `φs n` is the characteristic function of `μₙ`, then for each `r > 0` the
-- compound-Poisson law with intensity `r * μₙ` has characteristic function
-- `t ↦ exp (((r * n : ℝ) : ℂ) * (φs n t - 1))`. The assumed convergence
-- `n (φs n(t) - 1) → ψ(t)` upgrades this to pointwise convergence toward `exp (r ψ(t))`, and the
-- continuity of `ψ` at `0` gives continuity at `0` of the limit. Lévy's continuity theorem then
-- yields a probability measure with characteristic function `exp (r ψ)`.
/-- Corollary 16.7: under the linearized-limit hypothesis from Theorem 16.6, the scaled exponent
`t ↦ exp (r ψ(t))` is again a characteristic function for every `r > 0`. -/
theorem levyKhinchin_scaledExponent_isCharacteristicFunction
    {r : ℝ}
    (hcfp : ∀ n : ℕ, IsCFP (φs n))
    (hlin : ∀ t : ℝ, Tendsto (fun n : ℕ ↦ (n : ℂ) * (φs n t - 1)) atTop (nhds (ψ t)))
    (hψ_cont : ContinuousAt ψ 0)
    (hr : 0 < r) :
    IsCFP (fun t ↦ Complex.exp ((r : ℂ) * ψ t)) := sorry

-- Proof sketch: for each positive integer `n`, apply
-- `levyKhinchin_scaledExponent_isCharacteristicFunction` with `r = 1 / n` to obtain a
-- characteristic function root `t ↦ exp (((1 / n : ℝ) : ℂ) * ψ t)`. Its `n`th pointwise power is
-- `t ↦ exp (ψ t)`, so the definition of `IsInfinitelyDivisibleCFP` applies.
/-- Under the linearized-limit hypothesis from Theorem 16.6, the characteristic function `e^ψ` is
infinitely divisible in the owner predicate `IsInfinitelyDivisibleCFP`. -/
theorem levyKhinchin_exponential_has_characteristicRoots
    (hcfp : ∀ n : ℕ, IsCFP (φs n))
    (hlin : ∀ t : ℝ, Tendsto (fun n : ℕ ↦ (n : ℂ) * (φs n t - 1)) atTop (nhds (ψ t)))
    (hψ_cont : ContinuousAt ψ 0) :
    IsInfinitelyDivisibleCFP (fun t ↦ Complex.exp (ψ t)) := sorry

end
