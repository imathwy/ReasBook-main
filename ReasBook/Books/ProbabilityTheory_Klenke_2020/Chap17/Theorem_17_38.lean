import ProbabilityTheory_Klenke_2020.Chap17.Theorem_17_37
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]
variable {Ω : Type v} [MeasurableSpace Ω]

section FiniteStateSpace

variable [Finite E]
variable (p : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
variable [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]

-- Proof sketch: apply the source-facing dichotomy theorem
-- `irreducibleMarkovChain_recurrent_or_transient`. On a finite state space, the transient branch
-- is impossible because the Green-function sum over all states is infinite for every starting
-- point, so some state has infinite expected number of visits; irreducibility then propagates
-- recurrence to every state.
/-- Theorem 17.38: if the discrete state space `E` is finite and the realized chain with
transition matrix `p` is irreducible in the Chapter 17 sense, then the chain is recurrent. -/
theorem finite_irreducibleMarkovChain_isRecurrent
    (hirr : IsIrreducibleMarkovChain P X) :
    IsRecurrentMarkovChain P X := sorry

-- Proof sketch: pass from the discrete-kernel irreducibility of `discreteMatrixKernel p` to the
-- source-facing Chapter 17 predicate `IsIrreducibleMarkovChain P X` using Theorem 17.37, then
-- apply Theorem 17.38.
/-- Kernel-style specialization of Theorem 17.38 for realizations of a stochastic matrix. -/
theorem finite_irreducibleMarkovChain_isRecurrent_of_discreteMatrixKernel_isIrreducible
    [Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel p)] :
    IsRecurrentMarkovChain P X := by
  apply finite_irreducibleMarkovChain_isRecurrent
  exact isIrreducibleMarkovChain_of_discreteMatrixKernel_isIrreducible p P X

end FiniteStateSpace

end ProbabilityTheory
