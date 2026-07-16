import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap17.Definition_17_28
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap17.Theorem_17_8
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E] [MeasurableSingletonClass E]
variable {κ : ℕ → Kernel E E}
variable {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}

section

variable [IsMarkovProcessRealization κ P X]

-- Proof sketch: argue by induction on the positive entrance index `k`. For `k = 1`, the event is
-- exactly the defining event for `F[P, X] x y`. For the induction step, stop the chain at
-- the `(k - 1)`st entrance time and apply the strong Markov property from Theorem 17.14 to the
-- event of one further entrance into `y`, which contributes the factor `F[P, X] y y`.
/-- Theorem 17.29: for a discrete-time Markov process realization, the probability under `P x`
that the `k`th entrance time into `y` is finite is the first-entrance probability from `x` to
`y` times the `(k - 1)`st power of the return probability from `y` to itself. Here `τ_[X, y]^k` is
the textbook `k`th entrance time into `y`. -/
theorem iteratedEntranceTime_finite_probability_eq_everHitsProbability_mul_selfPow
    (x y : E) (k : ℕ+) :
    (P x : Measure Ω).real {ω | (τ_[X, y]^k) ω < ⊤} =
      (F[P, X]) x y * (F[P, X]) y y ^ k.natPred := sorry

end

end ProbabilityTheory
