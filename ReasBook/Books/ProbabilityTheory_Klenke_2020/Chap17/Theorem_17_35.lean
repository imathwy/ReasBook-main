import ProbabilityTheory_Klenke_2020.Chap17.Definition_17_28
import ProbabilityTheory_Klenke_2020.Chap17.Definition_17_30
import ProbabilityTheory_Klenke_2020.Chap17.Theorem_17_8
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

/- Theorem 17.35 is source-facing. Its ambient owner data is the realization
`[IsMarkovProcessRealization κ P X]`, while the hypotheses and conclusions are phrased in the
derived Chapter 17 API `IsRecurrentState` and `F[P, X]`. -/
section CommunicatingStates

variable [IsMarkovProcessRealization κ P X]
variable {x y : E}
variable (hx : IsRecurrentState P X x) (hxy : 0 < (F[P, X]) x y)

-- Proof sketch: realize the chain as a time-homogeneous Markov process, use the positive
-- probability of ever reaching `y` from `x` to deduce that any nonreturn to `x` after arriving at
-- `y` would force a nonreturn from the recurrent state `x`, and then compare Green functions
-- along a positive-probability path from `y` back to `x`.
/-- Theorem 17.35 (1): if a recurrent state `x` has positive probability of ever hitting `y`,
then `y` is also recurrent. -/
theorem isRecurrentState_of_isRecurrentState_of_everHitsProbability_pos :
    IsRecurrentState P X y := sorry

-- Proof sketch: combine recurrence of `x` with the Markov property at the first visit to `y`; a
-- positive-probability path from `x` to `y` forces the eventual hit probability from `x` to `y`
-- to be `1`, since otherwise the chain could avoid returning to `x` with positive probability.
/-- Theorem 17.35 (2): if a recurrent state `x` has positive probability of ever hitting `y`,
then starting from `x` the chain hits `y` almost surely. -/
theorem everHitsProbability_eq_one_of_isRecurrentState_of_everHitsProbability_pos :
    (F[P, X]) x y = 1 := sorry

-- Proof sketch: after obtaining recurrence of `y` from the first clause, repeat the same
-- argument with the roles of `x` and `y` reversed; the positive-probability path from `x` to `y`
-- and recurrence of both states imply that `y` also hits `x` almost surely.
/-- Theorem 17.35 (3): if a recurrent state `x` has positive probability of ever hitting `y`,
then starting from `y` the chain hits `x` almost surely. -/
theorem everHitsProbability_swap_eq_one_of_isRecurrentState_of_everHitsProbability_pos :
    (F[P, X]) y x = 1 := sorry

end CommunicatingStates

end ProbabilityTheory
