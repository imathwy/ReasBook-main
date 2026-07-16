import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap17.Definition_17_28
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap17.Definition_17_30
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap17.Theorem_17_8
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E] [DiscreteMeasurableSpace E]

/- Layering for Theorem 17.47:
- `returnCycleOccupationMass` and `returnCycleOccupationMeasure` are the source-facing excursion
  objects attached to the textbook statement.
- The singleton-mass lemma is derived API from that primitive data.
- The invariance conclusion is a `core/canonical` owner property, so the main theorem should use
  `Kernel.Invariant` rather than a raw measure-kernel composition equality. -/

/-- The occupation mass of the state `y` during the excursion from `x` up to the first positive
return to `x`, written as the sum of the probabilities of the events
`{ω | X n ω = y ∧ n < τ_x^1(ω)}`. This is the textbook quantity
`𝔼_x [∑_{n=0}^{τ_x^1 - 1} 1_{ {X_n = y} }]`. -/
def returnCycleOccupationMass
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (x y : E) : ℝ≥0∞ :=
  ∑' n : ℕ, (P x : Measure Ω) {ω | X n ω = y ∧ (n : ℕ∞) < (τ_[X, x]^1) ω}

/-- The measure on the discrete state space whose singleton masses are the excursion occupation
mass before the first positive return to `x`. -/
def returnCycleOccupationMeasure
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (x : E) : Measure E :=
  Measure.count.withDensity (returnCycleOccupationMass P X x)

notation "μ[" P ", " X "]" => returnCycleOccupationMeasure P X

-- Proof sketch: unfold `returnCycleOccupationMeasure`, evaluate the `withDensity` of
-- `Measure.count` on the singleton `{y}`, and use `Measure.count_singleton` to identify the value
-- with the density at `y`, which is `returnCycleOccupationMass P X x y`.
/-- The singleton mass formula for the return-cycle occupation measure `(μ[P, X]) x`. -/
theorem returnCycleOccupationMeasure_apply_singleton
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (x y : E) :
    (μ[P, X] x) {y} = returnCycleOccupationMass P X x y := sorry

section

variable {κ : ℕ → Kernel E E}
variable {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
variable [IsMarkovProcessRealization κ P X]

-- Proof sketch: use the strong Markov property at the first positive return time `τ_x^1` and the
-- decomposition of one-step transitions by whether the next state is `x` or not. The singleton
-- masses of `κ 1 ∘ₘ (μ[P, X] x)` match those of `(μ[P, X] x)`; since `E` is discrete, equality
-- on singletons gives
-- equality of measures, which is exactly `Kernel.Invariant (κ 1)`.
/-- Theorem 17.47: if `x` is recurrent, then the measure
`(μ[P, X]) x`, whose singleton masses count the expected visits to each state before the first
positive return to `x`, is invariant under the one-step kernel `κ 1`. -/
theorem recurrentState_returnCycleOccupationMeasure_comp_eq
    {x : E} (hx : IsRecurrentState P X x) :
    Kernel.Invariant (κ 1) ((μ[P, X]) x) := sorry

end

end ProbabilityTheory
