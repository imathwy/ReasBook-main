import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap08.Example_8_27
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap17.Definition_17_30
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap17.Definition_17_43
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap17.Remark_17_31
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap17.Theorem_17_8
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory.DiscreteMarkovChain

open Figure17_1State

/-- The weights of the invariant distributions of Fig. 17.1, parameterized by the mass assigned to
the absorbing state `s2`. -/
def figure17_1InvariantWeights (t : Set.Icc (0 : ℝ≥0∞) 1) : Figure17_1State → ℝ≥0∞
  | s2 => t.1
  | s6 => (1 - t.1) * ((4 : ℝ≥0∞) / 17)
  | s7 => (1 - t.1) * ((5 : ℝ≥0∞) / 17)
  | s8 => (1 - t.1) * ((8 : ℝ≥0∞) / 17)
  | _ => 0

-- Proof sketch: expand the finite sum over the eight states of `Figure17_1State`; only the masses
-- at `s2`, `s6`, `s7`, and `s8` are nonzero, and their total is
-- `t + (1 - t) * (4 / 17 + 5 / 17 + 8 / 17) = 1`.
/-- The weights defining the invariant family of Fig. 17.1 form a probability vector. -/
theorem figure17_1InvariantWeights_sum (t : Set.Icc (0 : ℝ≥0∞) 1) :
    Finset.univ.sum (figure17_1InvariantWeights t) = 1 := sorry

/-- The invariant distribution of Fig. 17.1 with mass `t` at the absorbing state `s2` and
remaining mass distributed over the positive recurrent class `{s6, s7, s8}` in the proportions
`4 : 5 : 8`. -/
def figure17_1InvariantDistribution (t : Set.Icc (0 : ℝ≥0∞) 1) :
    ProbabilityMeasure Figure17_1State :=
  ⟨(PMF.ofFintype (figure17_1InvariantWeights t) (figure17_1InvariantWeights_sum t)).toMeasure,
    inferInstance⟩

-- Proof sketch: the only closed communicating classes of Fig. 17.1 are the absorbing singleton
-- `{s2}` and the irreducible class `{s6, s7, s8}`. Every invariant distribution is therefore a
-- convex combination of the Dirac mass at `s2` and the unique stationary distribution on
-- `{s6, s7, s8}`, whose weights are `4 / 17`, `5 / 17`, and `8 / 17`.
/-- Exercise 17.6.1 (1): the invariant distributions of Fig. 17.1 are exactly the convex
combinations of the absorbing law at `s2` and the stationary law on `{s6, s7, s8}` with weights
`4 / 17`, `5 / 17`, and `8 / 17`. -/
theorem figure17_1_invariantDistributions_eq_range :
    invariantDistributions (discreteMatrixKernel figure17_1TransitionMatrix) =
      Set.range figure17_1InvariantDistribution := sorry

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Figure17_1State → ProbabilityMeasure Ω} {X : ℕ → Ω → Figure17_1State}
variable [IsMarkovProcessRealization
  (fun n : ℕ ↦ (discreteMatrixKernel figure17_1TransitionMatrix) ^ n) P X]

/- Exercise 17.6.1 (2): this is the Fig. 17.1 positive-recurrence statement already owned by
Remark 17.31, so the exercise file reuses that canonical theorem directly. -/
recall figure17_1_states678_positiveRecurrent

/- Exercise 17.6.1 (3)-(5): the three Fig. 17.1 first-return-time values are already owned by
Remark 17.31, so the exercise file reuses that canonical theorem directly. -/
recall figure17_1_expectedReturnTimes

end

end ProbabilityTheory.DiscreteMarkovChain
