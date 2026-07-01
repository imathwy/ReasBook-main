import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

-- Proof sketch: write the conditional expectation of `fun ω ↦ X₁ ω ⊓ X₂ ω` given `X₁`
-- using `ProbabilityTheory.condExp_prod_ae_eq_integral_condDistrib` for the function
-- `(x, y) ↦ x ⊓ y`. The measurability of `X₁` determines the conditioning σ-algebra
-- `MeasurableSpace.comap X₁ (borel ℝ)`, while `HasLaw X₂ (expMeasure θ) P` supplies the
-- `P`-almost-everywhere measurability required by the conditional-distribution API. Independence
-- then identifies the conditional distribution of `X₂` given `X₁` with `expMeasure θ`, and the
-- resulting one-dimensional integral evaluates to `(1 - exp (-θ x)) / θ`.
/-- Exercise 8.2.8: if `X₁` is measurable, `X₁` and `X₂` are independent, and both have
exponential law with common rate `θ`, then the conditional expectation of `X₁ ∧ X₂` given `X₁`
is `(1 - exp (-θ X₁)) / θ` almost surely. Since `P` is a probability measure, the law hypotheses
already force `expMeasure θ` to be a probability measure, hence in particular `θ > 0`. -/
theorem condExp_min_of_indep_exp_ae_eq {X₁ X₂ : Ω → ℝ} {θ : ℝ}
    (hX₁_meas : Measurable X₁)
    (hX₁_exp : HasLaw X₁ (expMeasure θ) P) (hX₂_exp : HasLaw X₂ (expMeasure θ) P)
    (h_indep : X₁ ⟂ᵢ[P] X₂) :
    P[fun ω ↦ X₁ ω ⊓ X₂ ω | MeasurableSpace.comap X₁ (borel ℝ)] =ᵐ[P]
      fun ω ↦ (1 - Real.exp (-(θ * X₁ ω))) / θ := sorry
