import Mathlib

open MeasureTheory

namespace MeasureTheory

/-- The Dirac probability measure at `0` is invariant under negation. -/
instance diracProba_zero_isNegInvariant :
    Measure.IsNegInvariant (((diracProba (0 : ℝ)) : ProbabilityMeasure ℝ) : Measure ℝ) := sorry

end MeasureTheory

/-- The function `t ↦ exp (-|r t|^α)` appearing in the symmetric stable-law corollary. -/
noncomputable def symmetricStableCharFun (α r : ℝ) (t : ℝ) : ℂ :=
  Complex.exp (-(|r * t| ^ α : ℝ))

-- Proof sketch: unfold `symmetricStableCharFun`; this is exactly its defining formula.
/-- The defining formula for `symmetricStableCharFun`. -/
theorem symmetricStableCharFun_apply (α r t : ℝ) :
    symmetricStableCharFun α r t = Complex.exp (-(|r * t| ^ α : ℝ)) := sorry

-- Proof sketch: apply Theorem 15.24 to the function `t ↦ exp (-|r t|^α)`, using the positivity
-- condition `0 < α ≤ 1` to obtain a probability measure with this characteristic function; then
-- use the evenness of the function to deduce the owner symmetry property
-- `Measure.IsNegInvariant`.
/-- Corollary 15.25: for every `α ∈ (0,1]` and `r ∈ ℝ`, the function
`t ↦ exp (-|r t|^α)` is the characteristic function of a symmetric probability measure on `ℝ`. -/
theorem exists_symmetricProbabilityMeasure_charFun_eq_symmetricStableCharFun
    (α r : ℝ) (hα₀ : 0 < α) (hα₁ : α ≤ 1) :
    ∃ μ : ProbabilityMeasure ℝ, ((μ : Measure ℝ)).IsNegInvariant ∧
      ∀ t : ℝ, charFun μ t = symmetricStableCharFun α r t := sorry
