import AchimKlenkeLean.Items.Chap17.Theorem_17_8
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u v w

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {T : Type v} [Preorder T]
variable {E : Type w} [mE : MeasurableSpace E]

/-- The event that a process realizes the prescribed finite history `states` at the times
`times`. -/
def finiteHistoryEvent {n : ℕ} (X : T → Ω → E) (times : Fin (n + 1) → T)
    (states : Fin (n + 1) → E) : Set Ω :=
  {ω | ∀ k, X (times k) ω = states k}

/-- In a countable state space, the remark's formulation of the Markov property says that for every
strictly increasing finite history with positive probability, the conditional probability of the
future state depends only on the last observed state. -/
def HasFiniteHistoryMarkovProperty (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : T → Ω → E) : Prop :=
  (∀ t, Measurable (X t)) ∧
    ∀ {n : ℕ} (times : Fin (n + 1) → T), StrictMono times → ∀ {t : T}, times (Fin.last n) < t →
      ∀ (states : Fin (n + 1) → E) (i : E),
        0 < μ (finiteHistoryEvent X times states) →
          μ[{ω | X t ω = i} | finiteHistoryEvent X times states] =
            μ[{ω | X t ω = i} | {ω | X (times (Fin.last n)) ω = states (Fin.last n)}]

-- Proof sketch: use the countability of the state space to reduce measurable state events to
-- countable unions of singleton events, then apply the Definition 17.1 conditional-probability
-- identity to singleton state events and conversely recover the full conditional-expectation
-- identity from equality on positive-probability finite history atoms.
/-- Remark 17.2: for a countable state space, the Markov property is equivalent to the statement
that on every positive-probability finite history, the conditional probability of `X_t = i`
depends only on the last state in that history. The time index only carries the ordering needed to
form strictly increasing histories and compare the observation time with the future time. -/
theorem hasNaturalMarkovProperty_iff_conditionalProb_eq_given_finite_history_of_countable
    [Countable E] [MeasurableSingletonClass E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : T → Ω → E) :
    HasNaturalMarkovProperty μ X ↔ HasFiniteHistoryMarkovProperty μ X := sorry

end ProbabilityTheory
