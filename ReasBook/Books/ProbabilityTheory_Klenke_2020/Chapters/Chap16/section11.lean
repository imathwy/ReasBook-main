import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_16_11 (from Items/Chap16) -/
open MeasureTheory

/-
Corollary 16.11 is `source-facing` at the characteristic-function level, but the reusable
`core/canonical` owner abstraction in this chapter is `ProbabilityMeasure ℝ` together with
`ProbabilityMeasure.IsInfinitelyDivisible`. The owner-side theorem below is the canonical core;
the textbook characteristic-function statement remains as the thin `bridge/view`.
-/
namespace MeasureTheory.ProbabilityMeasure

/-- An infinitely divisible probability law on `ℝ` has a characteristic function with a Gaussian
lower bound. -/
theorem charFun_gaussian_lower_bound_of_isInfinitelyDivisible
    {μ : ProbabilityMeasure ℝ} (hμ : IsInfinitelyDivisible μ) :
    ∃ γ > 0, ∀ t : ℝ, (1 / 2 : ℝ) * Real.exp (-γ * t ^ 2) ≤ ‖charFun (μ : Measure ℝ) t‖ := sorry

end MeasureTheory.ProbabilityMeasure

/-- Corollary 16.11: every infinitely divisible characteristic function on `ℝ` admits a Gaussian
lower bound; there is `γ > 0` such that `|φ(t)| ≥ (1 / 2) e^{-γ t^2}` for all real `t`. -/
-- Proof sketch: apply the quadratic lower bound obtained from formula `(16.3)` for the
-- logarithm/exponent in the infinitely divisible characteristic-function representation, then
-- exponentiate to get the displayed Gaussian lower bound. This is the `bridge/view` statement
-- obtained by realizing `φ` as the characteristic function of an infinitely divisible probability
-- law and applying
-- `MeasureTheory.ProbabilityMeasure.charFun_gaussian_lower_bound_of_isInfinitelyDivisible`.
theorem infinitelyDivisibleCFP_gaussian_lower_bound
    {φ : ℝ → ℂ} (hφ : IsInfinitelyDivisibleCFP φ) :
    ∃ γ > 0, ∀ t : ℝ, (1 / 2 : ℝ) * Real.exp (-γ * t ^ 2) ≤ ‖φ t‖ := sorry

/-- For `α > 2`, the stretched exponential `t ↦ exp (-|t|^α)` is not a characteristic function
on `ℝ`. -/
-- Proof sketch: if `t ↦ exp (-|t|^α)` were a CFP, the scaling identity
-- `exp (-|t|^α) = (exp (-|(n : ℝ) ^ (-1 / α) * t|^α))^n` would make it infinitely divisible.
-- The Gaussian lower bound from `infinitelyDivisibleCFP_gaussian_lower_bound` would then
-- contradict the faster-than-Gaussian decay when `α > 2`.
theorem stretchedExponential_not_isCFP_of_two_lt
    {α : ℝ} (hα : 2 < α) :
    ¬ IsCFP (fun t : ℝ ↦ Complex.exp (-(|t| ^ α : ℝ))) := sorry
