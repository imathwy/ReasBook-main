import ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_41
import ProbabilityTheory_Klenke_2020.Items.Chap18.Theorem_18_8
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: sum the geometric series with ratio `2 / 3`; the sum is `3`, and the prefactor
-- `1 / 3` reduces the value to `1`.
/-- The resistance series of the dyadically branching subtree used in the `ℤ^3` transience
argument has value `1`. -/
theorem dyadicTreeResistanceSeries_eq_one :
    (1 / (3 : ℝ≥0∞)) * ∑' k : ℕ, (((2 : ℝ≥0∞) / 3) ^ k) = 1 := sorry

-- Proof sketch: combine the `d = 3` case of
-- `symmetricSimpleRandomWalk_isRecurrent_iff_dimension_le_two` with irreducibility of the
-- symmetric simple walk on `ℤ^3`; the irreducible dichotomy then gives transience of every
-- state, while the chapter text computes the needed transience input through the finite-resistance
-- subtree encoded by `dyadicTreeResistanceSeries_eq_one`.
/-- Example 19.31: every state of the symmetric simple random walk on `ℤ^3`, modeled by the
translation-invariant step law `symmetricSimpleRandomWalkStepPMF 3`, is transient; equivalently,
its positive-time return probability at each state is strictly smaller than `1`. -/
theorem symmetricSimpleRandomWalkOnZ3_allStatesTransient
    (p : (Fin 3 → ℤ) → PMF (Fin 3 → ℤ))
    (P : (Fin 3 → ℤ) → ProbabilityMeasure Ω) (X : ℕ → Ω → (Fin 3 → ℤ))
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel (fun x y ↦ p x y) ^ n) P X]
    [Kernel.IsIrreducible
      (Measure.count : Measure (Fin 3 → ℤ)) (discreteMatrixKernel (fun x y ↦ p x y))]
    (hp : IsTranslationInvariantStepMatrix (fun x y ↦ p x y))
    (hstep : p 0 = symmetricSimpleRandomWalkStepPMF 3)
    :
    ∀ x : Fin 3 → ℤ, everHitsProbability P X x x < 1 := sorry

end ProbabilityTheory
