import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Remark_17_31 (from Items/Chap17) -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace ProbabilityTheory

namespace DiscreteMarkovChain

universe u

/-- The eight states of the Markov chain drawn in Fig. 17.1. -/
inductive Figure17_1State
  | s1 | s2 | s3 | s4 | s5 | s6 | s7 | s8
  deriving DecidableEq, Fintype

open Figure17_1State

/-- The finite state space of Fig. 17.1 carries the discrete measurable structure. -/
instance instMeasurableSpaceFigure17_1State : MeasurableSpace Figure17_1State := ⊤

/-- The transition matrix encoded by Fig. 17.1. -/
def figure17_1TransitionMatrix : Figure17_1State → Figure17_1State → ENNReal
  | s1, s2 => 1 / 2
  | s1, s3 => 1 / 3
  | s1, s4 => 1 / 6
  | s2, s2 => 1
  | s3, s4 => 1 / 2
  | s3, s5 => 1 / 2
  | s4, s3 => 1 / 2
  | s4, s5 => 1 / 2
  | s5, s3 => 3 / 4
  | s5, s6 => 1 / 4
  | s6, s7 => 1 / 4
  | s6, s8 => 3 / 4
  | s7, s8 => 1
  | s8, s6 => 1 / 2
  | s8, s7 => 1 / 2
  | _, _ => 0

-- Proof sketch: unfold `figure17_1TransitionMatrix`; the `(s2,s2)` entry is the loop of weight
-- `1` shown in Fig. 17.1.
/-- In Fig. 17.1, the state `2` has one-step self-transition probability `1`. -/
theorem figure17_1TransitionMatrix_s2_self :
    figure17_1TransitionMatrix s2 s2 = 1 := sorry

/-- The nearest-neighbor transition matrix encoded by Fig. 17.2, with parameter `r ∈ [0,1]`,
deterministic jump `0 → 1`, and, for `n + 1`, left jump probability `1 - r` and right jump
probability `r`. -/
def figure17_2TransitionMatrix (r : Set.Icc (0 : ENNReal) 1) : ℕ → ℕ → ENNReal
  | 0, 1 => 1
  | 0, _ => 0
  | n + 1, m =>
      if m = n then 1 - (r : ENNReal) else if m = n + 2 then (r : ENNReal) else 0

-- Proof sketch: unfold `figure17_2TransitionMatrix` at the boundary state `0`; the definition
-- makes the jump to `1` deterministic.
/-- At the boundary state `0`, Fig. 17.2 jumps to `1` with probability `1`. -/
theorem figure17_2TransitionMatrix_zero (r : Set.Icc (0 : ENNReal) 1) :
    figure17_2TransitionMatrix r 0 1 = 1 := sorry

-- Proof sketch: unfold `figure17_2TransitionMatrix` at the state `n + 1`; the definition is
-- exactly the left/right nearest-neighbor rule shown in Fig. 17.2.
/-- Away from `0`, Fig. 17.2 moves to `n` with probability `1 - r` and to `n + 2` with
probability `r`. -/
theorem figure17_2TransitionMatrix_succ (r : Set.Icc (0 : ENNReal) 1) (n m : ℕ) :
    figure17_2TransitionMatrix r (n + 1) m =
      if m = n then 1 - (r : ENNReal) else if m = n + 2 then (r : ENNReal) else 0 := sorry

-- Proof sketch: for the boundary row only the jump `0 → 1` contributes. For the row `n + 1`,
-- only the entries at `n` and `n + 2` are nonzero, and because `r ∈ [0,1]` their masses add up
-- to `(1 - r) + r = 1`.
/-- The Fig. 17.2 transition matrix is stochastic for every parameter `r ∈ [0,1]`. -/
theorem figure17_2TransitionMatrix_isStochastic
    (r : Set.Icc (0 : ENNReal) 1) :
    IsStochasticMatrix (figure17_2TransitionMatrix r) := sorry

-- Proof sketch: the textbook item is directly the absorbing-state assertion for `s2`, and the
-- owner declaration `ProbabilityTheory.IsAbsorbingState` already supplies the canonical notion.
/-- Remark 17.31 (1): in the supplied source excerpt, state `2` of Fig. 17.1 is absorbing. -/
theorem figure17_1_state2_isAbsorbing :
    IsAbsorbingState figure17_1TransitionMatrix s2 := sorry

section Figure17_1

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Figure17_1State → ProbabilityMeasure Ω} {X : ℕ → Ω → Figure17_1State}
variable [IsMarkovProcessRealization
  (fun n : ℕ ↦ discreteMatrixKernel figure17_1TransitionMatrix ^ n) P X]

-- Proof sketch: this is the subset formulation of the four transient-state assertions from the
-- source excerpt, now expressed for realizations of the Fig. 17.1 chain through the owner
-- predicate `IsTransientState`.
/-- Remark 17.31 (2): in any realization of the Markov chain of Fig. 17.1, the states `1`, `3`,
`4`, and `5` are transient. -/
theorem figure17_1_states1345_transient :
    {x | x = s1 ∨ x = s3 ∨ x = s4 ∨ x = s5} ⊆ {x | IsTransientState P X x} := sorry

-- Proof sketch: this is the subset formulation of the three positive-recurrent-state assertions
-- from the source excerpt, now expressed through the owner predicate
-- `IsPositiveRecurrentState`.
/-- Remark 17.31 (3): in any realization of the Markov chain of Fig. 17.1, the states `6`, `7`,
and `8` are positive recurrent. -/
theorem figure17_1_states678_positiveRecurrent :
    {x | x = s6 ∨ x = s7 ∨ x = s8} ⊆ {x | IsPositiveRecurrentState P X x} := sorry

-- Proof sketch: the statement is exactly the ordered triple of return-time values quoted in the
-- source excerpt, expressed through the owner function `expectedFirstReturnTime`.
/-- Remark 17.31 (4): in any realization of the Markov chain of Fig. 17.1, the expected first
return times are `17 / 4`, `17 / 5`, and `17 / 8` at the states `6`, `7`, and `8`. -/
theorem figure17_1_expectedReturnTimes :
    (expectedFirstReturnTime P X s6 = (17 : ENNReal) / 4) ∧
      (expectedFirstReturnTime P X s7 = (17 : ENNReal) / 5) ∧
      expectedFirstReturnTime P X s8 = (17 : ENNReal) / 8 := sorry

end Figure17_1

section Figure17_2

variable {Ω : Type u} [MeasurableSpace Ω]
variable {r : Set.Icc (0 : ENNReal) 1} {P : ℕ → ProbabilityMeasure Ω} {X : ℕ → Ω → ℕ}
variable [IsMarkovProcessRealization
  (fun n : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ n) P X]

-- Proof sketch: this is exactly the transient-regime implication stated for the right-drift
-- regime `r ∈ (1 / 2, 1]`, including the boundary case `r = 1` of deterministic drift to `+∞`.
/-- Remark 17.31 (5): for any realization of the Markov chain of Fig. 17.2, every state is
transient when `r ∈ (1 / 2, 1]`. -/
theorem figure17_2_allStatesTransient_of_half_lt
    (hrhalf : 1 / 2 < (r : ENNReal)) :
    ∀ x : ℕ, IsTransientState P X x := sorry

-- Proof sketch: this is the stated positive-recurrence strengthening of the left-drift case.
/-- Remark 17.31 (6): for any realization of the Markov chain of Fig. 17.2, the chain is
positive recurrent when `r ∈ (0, 1 / 2)`. -/
theorem figure17_2_allStatesPositiveRecurrent_of_lt_half
    (hr0 : 0 < (r : ENNReal)) (hrhalf : (r : ENNReal) < 1 / 2) :
    IsPositiveRecurrentMarkovChain P X := sorry

-- Proof sketch: this is exactly the critical parameter statement at `r = 1 / 2`.
/-- Remark 17.31 (7): for any realization of the Markov chain of Fig. 17.2, the chain is null
recurrent when `r = 1 / 2`. -/
theorem figure17_2_allStatesNullRecurrent_of_eq_half
    (hr : (r : ENNReal) = 1 / 2) :
    IsNullRecurrentMarkovChain P X := sorry

end Figure17_2

end DiscreteMarkovChain

end ProbabilityTheory
