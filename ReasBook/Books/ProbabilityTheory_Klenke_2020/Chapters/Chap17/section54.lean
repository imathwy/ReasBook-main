import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_17_54 (from Items/Chap17) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

/-- The covariance of two monotone increasing real functions under a probability law on `ℝ`
is nonnegative when both functions have finite second moment. -/
-- Proof sketch: take two independent random variables with law `μ`, observe that
-- `(f x - f y) * (g x - g y) ≥ 0` by monotonicity, integrate this nonnegative quantity over the
-- product law, and rewrite the result as `2 * cov[f, g; μ]`.
theorem covariance_nonneg_of_monotone {μ : Measure ℝ} [IsProbabilityMeasure μ] {f g : ℝ → ℝ}
    (hf : Monotone f) (hg : Monotone g) (hf_sq : MemLp f 2 μ) (hg_sq : MemLp g 2 μ) :
    0 ≤ cov[f, g; μ] := sorry

namespace HasLaw

/-- Transport `covariance_nonneg_of_monotone` along the law of a real random variable. -/
-- Proof sketch: use `ProbabilityTheory.covariance_nonneg_of_monotone` on the law `ν` of `X`,
-- then rewrite the covariance on `Ω` by `HasLaw.covariance_fun_comp`.
theorem covariance_nonneg_of_monotone_comp {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ν : Measure ℝ} {X : Ω → ℝ} (hX : HasLaw X ν μ)
    {f g : ℝ → ℝ} (hf : Monotone f) (hg : Monotone g) (hf_sq : MemLp f 2 ν)
    (hg_sq : MemLp g 2 ν) :
    0 ≤ cov[fun ω ↦ f (X ω), fun ω ↦ g (X ω); μ] := sorry

end HasLaw

/-- Example 17.54: if `X` is a real random variable and `f`, `g : ℝ → ℝ` are monotone increasing
with finite second moments, then `f(X)` and `g(X)` are nonnegatively correlated. -/
-- Proof sketch: package `X` as the canonical law statement `HasLaw X (Measure.map X μ) μ`, turn
-- the `MemLp` hypotheses on `f ∘ X` and `g ∘ X` into `MemLp` hypotheses on the pushforward law,
-- and apply `HasLaw.covariance_nonneg_of_monotone_comp`.
theorem monotone_comp_covariance_nonneg {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {f g : ℝ → ℝ} (hX : AEMeasurable X μ)
    (hf : Monotone f) (hg : Monotone g) (hf_sq : MemLp (fun ω ↦ f (X ω)) 2 μ)
    (hg_sq : MemLp (fun ω ↦ g (X ω)) 2 μ) :
    0 ≤ cov[fun ω ↦ f (X ω), fun ω ↦ g (X ω); μ] := sorry

end ProbabilityTheory
