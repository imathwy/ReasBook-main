import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

-- Proof sketch: rewrite the moment integral against `betaMeasure r s` as the Beta integral with
-- parameters `r + n` and `s`.
private lemma integral_pow_eq_beta_ratio_betaMeasure
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s) (n : ℕ) :
    ∫ x, x ^ n ∂betaMeasure r s = beta (r + n) s / beta r s := sorry

-- Proof sketch: unfold `beta` in terms of Gamma functions and use the Gamma recurrence to convert
-- the beta-function ratio into the finite product.
private lemma beta_ratio_eq_prod (r s : ℝ) (hr : 0 < r) (hs : 0 < s) (n : ℕ) :
    beta (r + n) s / beta r s = ∏ k ∈ Finset.range n, (r + k) / (r + s + k) := sorry

-- Proof sketch: transport the canonical beta-ratio moment formula for `betaMeasure r s` along
-- `HasLaw.integral_comp`, then rewrite the ratio with `beta_ratio_eq_prod`.
/-- Exercise 5.1.2: If a real random variable has Beta law with parameters `r, s > 0`, then its
`n`th moment is `∏_{k=0}^{n-1} (r + k) / (r + s + k)`. -/
theorem beta_moment_formula (r s : ℝ) (hr : 0 < r) (hs : 0 < s) {P : Measure Ω} {X : Ω → ℝ}
    (hX : HasLaw X (betaMeasure r s) P) (n : ℕ) :
    P[fun ω ↦ X ω ^ n] = ∏ k ∈ Finset.range n, (r + k) / (r + s + k) := sorry
