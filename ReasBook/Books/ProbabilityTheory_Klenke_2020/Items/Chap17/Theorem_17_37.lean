import ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_16
import ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_36
import ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_17
import ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_35
import Mathlib

open MeasureTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]
variable {Ω : Type v} [MeasurableSpace Ω]

section RecurrentOrTransient

variable (p : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
variable [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]

/- Theorem 17.37 (1) is source-facing: its main irreducibility hypothesis is the chapter API
`IsIrreducibleMarkovChain P X`. The discrete-kernel irreducibility of `discreteMatrixKernel p`
is the concrete model-specific bridge to that source-facing notion. -/

-- Proof sketch: apply kernel irreducibility to singleton state sets, then use the realization
-- marginal identity `(P x).map (X n) = (discreteMatrixKernel p ^ n) x` to obtain a positive-time
-- hit of each state from every initial state.
/-- The discrete-kernel irreducibility of the transition matrix yields the Chapter 17
irreducibility predicate for any realization of that chain. -/
theorem isIrreducibleMarkovChain_of_discreteMatrixKernel_isIrreducible
    [Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel p)] :
    IsIrreducibleMarkovChain P X := sorry

-- Proof sketch: by Theorem 17.35, irreducibility makes recurrence a class property, so if one
-- state is recurrent then all states are recurrent, and otherwise every state is transient.
/-- Theorem 17.37 (1): an irreducible discrete Markov chain is either recurrent or transient. -/
theorem irreducibleMarkovChain_recurrent_or_transient
    (hirr : IsIrreducibleMarkovChain P X) :
    IsRecurrentMarkovChain P X ∨ ∀ x : E, IsTransientState P X x := sorry

-- Proof sketch: first pass from the discrete-kernel irreducibility of `p` to the source-facing
-- chapter predicate `IsIrreducibleMarkovChain P X`, then apply Theorem 17.37 (1).
/-- The kernel-style specialization of Theorem 17.37 (1) for realizations of a stochastic matrix.
-/
theorem irreducibleMarkovChain_recurrent_or_transient_of_discreteMatrixKernel_isIrreducible
    [Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel p)] :
    IsRecurrentMarkovChain P X ∨ ∀ x : E, IsTransientState P X x :=
  irreducibleMarkovChain_recurrent_or_transient P X
    (isIrreducibleMarkovChain_of_discreteMatrixKernel_isIrreducible p P X)

end RecurrentOrTransient

section NoAbsorbingState

variable [Nontrivial E]

/- Theorem 17.37 (2) is source-facing: its main irreducibility hypothesis is again the chapter API
`IsIrreducibleMarkovChain P X`. The discrete-kernel irreducibility of `discreteMatrixKernel p`
remains only the concrete bridge to that source-facing statement. -/

-- Proof sketch: if `x` were absorbing and `E` had a second point `y`, then irreducibility would
-- force a positive-probability path from `x` to `{y}`, but the absorbing property prevents the
-- chain from ever leaving `x`.
/-- Theorem 17.37 (2): if the irreducible discrete state space has at least two points, then the
transition matrix has no absorbing state. -/
theorem irreducibleMarkovChain_has_no_absorbing_state
    (p : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (hirr : IsIrreducibleMarkovChain P X) :
    ∀ x : E, ¬ IsAbsorbingState p x := sorry

-- Proof sketch: pass from the discrete-kernel irreducibility of `p` to the chapter predicate
-- `IsIrreducibleMarkovChain P X`, then apply Theorem 17.37 (2).
/-- The kernel-style specialization of Theorem 17.37 (2) for realizations of a stochastic matrix.
-/
theorem irreducibleMarkovChain_has_no_absorbing_state_of_discreteMatrixKernel_isIrreducible
    (p : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    [Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel p)] :
    ∀ x : E, ¬ IsAbsorbingState p x :=
  irreducibleMarkovChain_has_no_absorbing_state p P X
    (isIrreducibleMarkovChain_of_discreteMatrixKernel_isIrreducible p P X)

end NoAbsorbingState

end ProbabilityTheory
