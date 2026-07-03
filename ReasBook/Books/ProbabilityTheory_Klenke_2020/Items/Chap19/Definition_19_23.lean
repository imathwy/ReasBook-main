import AchimKlenkeLean.Items.Chap17.Definition_17_30
import AchimKlenkeLean.Items.Chap19.Definition_19_11
import Mathlib

open MeasureTheory
open scoped ENNReal

noncomputable section

universe u v

namespace ProbabilityTheory

attribute [local instance] Classical.propDecidable

variable {Ω : Type v} [MeasurableSpace Ω]

section

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]

/- Layering for Definition 19.23:
- `source-facing`: `escapeToSetProbability`, `escapeProbability`, the finite-boundary effective
  conductance formula `conductance C x₁ * escapeToSetProbability P X x₁ A₀`, and the effective
  conductance to infinity defined from those escape probabilities.
- `core/canonical`: the Chapter 19 conductance owner `conductance` from Definition 19.11 and the
  canonical positive-time ever-hit owner `F[P, X]`.
- `bridge/view`: the Chapter 19 escape probability lives in `ℝ≥0∞`, so its complement formula uses
  `ENNReal.ofReal ((F[P, X]) x₁ x₁)` while the theorem statements below still restate the source
  events in textbook coordinate form and connect them to the earlier owner predicate
  `IsRecurrentState`. -/

/-- The probability that the trajectory started from `x₁` reaches the set `A₀` before making its
first positive-time return to `x₁`. -/
def escapeToSetProbability (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    (x₁ : E) (A₀ : Set E) : ℝ≥0∞ :=
  (P x₁ : Measure Ω) {ω | hittingAfter X A₀ 1 ω < hittingAfter X ({x₁} : Set E) 1 ω}

-- Proof sketch: unfold `escapeToSetProbability`; it is defined as the probability, under the law
-- started from `x₁`, that the first positive entrance time into `A₀` is strictly smaller than the
-- first positive return time to `x₁`. In coordinates, this means that some positive time `n`
-- lands in `A₀` and there is no positive-time return to `x₁` up to and including time `n`.
/-- The escape-to-set probability is the probability of hitting `A₀` before the first positive-time
return to `x₁`. -/
theorem escapeToSetProbability_def
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (x₁ : E) (A₀ : Set E) :
    escapeToSetProbability P X x₁ A₀ =
      (P x₁ : Measure Ω) {ω |
        ∃ n : ℕ, 0 < n ∧ X n ω ∈ A₀ ∧ ∀ m : ℕ, 0 < m → m ≤ n → X m ω ≠ x₁} := sorry

-- Proof sketch: if `A₀ ⊆ A₁`, then the event "hit `A₀` before the first positive return to `x₁`"
-- is contained in the corresponding event for `A₁`. Apply monotonicity of the probability measure
-- `P x₁` to those events.
/-- The escape-to-set probability is monotone in the target set. -/
theorem escapeToSetProbability_mono
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (x₁ : E) :
    Monotone (escapeToSetProbability P X x₁) := sorry

/-- Definition 19.23 (1): the escape probability from `x₁` is the probability of never making a
positive-time return to `x₁`, equivalently `1 - F(x₁,x₁)` where `F(x₁,x₁)` is the return
probability. -/
def escapeProbability (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (x₁ : E) : ℝ≥0∞ :=
  1 - ENNReal.ofReal ((F[P, X]) x₁ x₁)

-- Proof sketch: the event that the trajectory never returns to `x₁` at positive times is the
-- complement of the positive-return event defining `(F[P, X]) x₁ x₁`. Since `P x₁` is a
-- probability measure, the complement has mass `1 - ENNReal.ofReal ((F[P, X]) x₁ x₁)`.
/-- The escape probability is the probability that the trajectory never returns to `x₁` at a
strictly positive time. -/
theorem escapeProbability_eq_prob_no_return
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (x₁ : E) :
    escapeProbability P X x₁ =
      (P x₁ : Measure Ω) {ω | ∀ n : ℕ, 0 < n → X n ω ≠ x₁} := sorry

-- Proof sketch: `IsRecurrentState P X x₁` is the Chapter 17 owner statement that the positive-time
-- return probability `(F[P, X]) x₁ x₁` is `1`. By Definition 19.23, the escape probability is the
-- complementary mass `1 - ENNReal.ofReal ((F[P, X]) x₁ x₁)`, so it vanishes exactly in the
-- recurrent case.
/-- A state is recurrent exactly when its Chapter 19 escape probability is `0`. -/
theorem isRecurrentState_iff_escapeProbability_eq_zero
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (x₁ : E) :
    IsRecurrentState P X x₁ ↔ escapeProbability P X x₁ = 0 := sorry

/-- Definition 19.23 (2): the effective conductance from `x₁` to infinity is `conductance C x₁`
times the infimum of the escape probabilities to cofinite sets avoiding `x₁`. -/
def effectiveConductanceToInfinity
    (C : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (x₁ : E) : ℝ≥0∞ :=
  conductance C x₁ *
    sInf {r : ℝ≥0∞ |
      ∃ A₀ : Set E, A₀ᶜ.Finite ∧ x₁ ∉ A₀ ∧ r = escapeToSetProbability P X x₁ A₀}

end

-- Proof sketch: unfold `effectiveConductanceToInfinity`; it is defined exactly as `conductance C
-- x₁` multiplied by the infimum of the escape-to-set probabilities over all cofinite subsets
-- `A₀` avoiding `x₁`.
/-- The effective conductance to infinity is the conductance at `x₁` times the infimum of the
escape probabilities toward cofinite sets not containing `x₁`. -/
theorem effectiveConductanceToInfinity_def
    {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]
    (C : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (x₁ : E) :
    effectiveConductanceToInfinity C P X x₁ =
      conductance C x₁ *
        sInf {r : ℝ≥0∞ |
          ∃ A₀ : Set E, A₀ᶜ.Finite ∧ x₁ ∉ A₀ ∧ r = escapeToSetProbability P X x₁ A₀} := rfl

end ProbabilityTheory
