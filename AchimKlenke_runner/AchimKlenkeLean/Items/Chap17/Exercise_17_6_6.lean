import AchimKlenkeLean.Items.Chap17.Theorem_17_37
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]
variable {Ω : Type v} [MeasurableSpace Ω]

/- Layering for Exercise 17.6.6:
- `IsIrreducibleMarkovChain P X` and `IsRecurrentMarkovChain P X` are the source-facing Chapter 17
  hypotheses.
- `Kernel.Invariant` is the core/canonical owner predicate for invariant measures of a fixed
  kernel.
- `discreteMatrixKernel p` remains only the concrete bridge/view turning a stochastic matrix into
  the kernel whose invariant measures are being compared. -/

section

variable {p : E → E → ℝ≥0∞} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
variable [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]

-- Proof sketch: for a fixed nonzero invariant measure `π`, use the exercise's induction on the
-- first return to a reference state `x` to identify every singleton mass `π {y}` with
-- `π {x} * μ_x {y}`, where `μ_x` is the return-cycle occupation measure from Theorem 17.47.
-- Applying this description to two invariant measures and comparing the same reference state
-- yields a strictly positive scalar relating them.
/-- Exercise 17.6.6: if the realized discrete-time chain with transition matrix `p` is
irreducible in the Chapter 17 sense and recurrent, then any two nonzero invariant measures for
`discreteMatrixKernel p` are proportional. Equivalently, the invariant measure is unique up to
multiplication by a positive constant. -/
theorem invariantMeasures_unique_up_to_scale_of_irreducible_recurrent
    (hirr : IsIrreducibleMarkovChain P X) (hrec : IsRecurrentMarkovChain P X) {μ ν : Measure E}
    (hμ : Kernel.Invariant (discreteMatrixKernel p) μ)
    (hν : Kernel.Invariant (discreteMatrixKernel p) ν)
    (hμ_ne : μ ≠ 0) (hν_ne : ν ≠ 0) :
    ∃ c : ℝ≥0∞, 0 < c ∧ ν = c • μ := sorry

-- Proof sketch: apply Theorem 17.37 to pass from the kernel irreducibility of
-- `discreteMatrixKernel p` to the source-facing predicate `IsIrreducibleMarkovChain P X`, then
-- invoke Exercise 17.6.6.
/-- Kernel-style specialization of Exercise 17.6.6 for realizations of a stochastic matrix. -/
theorem invariantMeasures_unique_up_to_scale_of_irreducible_recurrent_of_discreteMatrixKernel_isIrreducible
    [Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel p)]
    (hrec : IsRecurrentMarkovChain P X) {μ ν : Measure E}
    (hμ : Kernel.Invariant (discreteMatrixKernel p) μ)
    (hν : Kernel.Invariant (discreteMatrixKernel p) ν)
    (hμ_ne : μ ≠ 0) (hν_ne : ν ≠ 0) :
    ∃ c : ℝ≥0∞, 0 < c ∧ ν = c • μ := by
  exact invariantMeasures_unique_up_to_scale_of_irreducible_recurrent
    (isIrreducibleMarkovChain_of_discreteMatrixKernel_isIrreducible p P X) hrec hμ hν hμ_ne hν_ne

end

end ProbabilityTheory
