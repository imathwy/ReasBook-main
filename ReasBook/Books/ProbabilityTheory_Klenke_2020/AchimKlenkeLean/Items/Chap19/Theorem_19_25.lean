import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap17.Definition_17_30
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap19.Definition_19_23

open MeasureTheory
open scoped ENNReal

noncomputable section

universe u v

attribute [local instance] Classical.propDecidable

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]
variable {Ω : Type v} [MeasurableSpace Ω]

/- Layering for Theorem 19.25:
- `source-facing`: the finite-boundary conductance formula
  `conductance C x₁ * escapeToSetProbability P X x₁ A₀` and the resulting escape and recurrence
  criteria at infinity.
- `core/canonical`: `conductance`, `IsRandomWalkWithWeights`, `escapeProbability`,
  `effectiveConductanceToInfinity`, and the Chapter 17 recurrence owner `IsRecurrentState`.
- `bridge/view`: `effectiveResistanceToInfinity` is the reciprocal reformulation of the owner
  conductance-to-infinity statement. -/

variable {p C : E → E → ℝ≥0∞}
variable {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}

/-- The effective resistance from `x` to infinity is the reciprocal of the Chapter 19 effective
conductance to infinity. -/
def effectiveResistanceToInfinity
    (C : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (x : E) : ℝ≥0∞ :=
  (effectiveConductanceToInfinity C P X x)⁻¹

section RandomWalkWithWeights

variable [IsRandomWalkWithWeights p C]
variable [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]

-- Proof sketch: approximate infinity by cofinite sets `A₀ⁿ` avoiding `x₁`. By Lemma 19.24, the
-- finite-boundary conductances `conductance C x₁ * escapeToSetProbability P X x₁ (A₀ⁿ)` converge to
-- `effectiveConductanceToInfinity C P X x₁`; the corresponding escape probabilities converge to
-- `escapeProbability P X x₁`. The owner abstraction `IsRandomWalkWithWeights p C` supplies the
-- needed finite-conductance hypothesis through `IsRandomWalkWithWeights.conductance_lt_top`, so
-- the common factor `(conductance C x₁)⁻¹` yields the displayed identity.
/-- Theorem 19.25: the escape probability from `x₁` equals the effective conductance from `x₁`
to infinity divided by the total conductance `C(x₁)`. -/
theorem escapeProbability_eq_conductance_inv_mul_effectiveConductanceToInfinity
    (x₁ : E) :
    escapeProbability P X x₁ =
      (conductance C x₁)⁻¹ * effectiveConductanceToInfinity C P X x₁ := sorry

-- Proof sketch: rewrite recurrence using
-- `isRecurrentState_iff_escapeProbability_eq_zero`, then apply
-- `escapeProbability_eq_conductance_inv_mul_effectiveConductanceToInfinity`. The conductance
-- factor `(conductance C x₁)⁻¹` is evaluated in the finite-conductance random-walk setting
-- provided by `IsRandomWalkWithWeights p C`, so recurrence is equivalent to vanishing effective
-- conductance to infinity.
/-- A state is recurrent exactly when its effective conductance to infinity vanishes. -/
theorem isRecurrentState_iff_effectiveConductanceToInfinity_eq_zero
    (x₁ : E) :
    IsRecurrentState P X x₁ ↔ effectiveConductanceToInfinity C P X x₁ = 0 := sorry

end RandomWalkWithWeights

-- Proof sketch: unfold `effectiveResistanceToInfinity` and use the reciprocal relation in
-- `ℝ≥0∞`: the reciprocal is `∞` exactly when the original quantity is `0`.
/-- The effective conductance to infinity vanishes exactly when the effective resistance to
infinity is infinite. -/
theorem effectiveConductanceToInfinity_eq_zero_iff_effectiveResistanceToInfinity_eq_top
    (C : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (x₁ : E) :
    effectiveConductanceToInfinity C P X x₁ = 0 ↔
      effectiveResistanceToInfinity C P X x₁ = ∞ := sorry

end ProbabilityTheory
