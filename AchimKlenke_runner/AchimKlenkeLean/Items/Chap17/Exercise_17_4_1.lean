import AchimKlenkeLean.Items.Chap17.Definition_17_30
import AchimKlenkeLean.Items.Chap17.Theorem_17_8
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
variable {κ : ℕ → Kernel E E}
variable {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}

/- Exercise 17.4.1 is source-facing. Its ambient owner data is the realization
`[IsMarkovProcessRealization κ P X]`, while the hypotheses and conclusion are phrased in the
derived Chapter 17 API `IsPositiveRecurrentState` and `F[P, X]`. -/
section CommunicatingStates

variable [IsMarkovProcessRealization κ P X]
variable {x y : E}

-- Proof sketch: use the positive-probability hit from `x` to `y` together with the strong Markov
-- property at the first visit to `y` to compare return cycles; finiteness of the expected return
-- time to `x` then transfers to finiteness of the expected return time to `y`.
/-- Exercise 17.4.1: if `x` is positive recurrent and the probability `F(x, y)` of ever hitting
`y` from `x` is positive, then `y` is also positive recurrent. -/
theorem isPositiveRecurrentState_of_isPositiveRecurrentState_of_everHitsProbability_pos
    (hx : IsPositiveRecurrentState P X x) (hxy : 0 < (F[P, X]) x y) :
    IsPositiveRecurrentState P X y := sorry

end CommunicatingStates

end ProbabilityTheory
