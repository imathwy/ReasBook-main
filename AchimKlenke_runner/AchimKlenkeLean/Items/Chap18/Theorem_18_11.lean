import AchimKlenkeLean.Items.Chap18.Definition_18_1
import AchimKlenkeLean.Items.Chap18.Definition_18_5
import AchimKlenkeLean.Items.Chap18.Example_18_6
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E] [Countable E]
variable {Ω : Type v} [MeasurableSpace Ω]

-- Proof sketch: unpack the canonical Chapter 18 owner `IsSuccessfulMarkovCoupling`. Its
-- `IsMarkovCoupling` field is exactly the pair of coordinate realization owners, and the
-- remaining owner field is the tail-disagreement limit.
/-- The canonical Chapter 18 owner `IsSuccessfulMarkovCoupling p P Z` is equivalent to the two
coordinate realization conditions together with the vanishing tail disagreement probability. -/
theorem isSuccessfulMarkovCoupling_iff_coordinateRealizations (p : E → E → ℝ≥0∞)
    (P : E × E → ProbabilityMeasure Ω) (Z : ℕ → Ω → E × E) :
    IsSuccessfulMarkovCoupling p P Z ↔
      (∀ y : E,
        IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n)
          (fun x : E ↦ P (x, y)) (fun n ω ↦ (Z n ω).1)) ∧
        (∀ x : E,
          IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n)
            (fun y : E ↦ P (x, y)) (fun n ω ↦ (Z n ω).2)) ∧
          ∀ x y : E,
            Tendsto
              (fun n : ℕ ↦
                (P (x, y) : Measure Ω) (⋃ m ≥ n, {ω | (Z m ω).1 ≠ (Z m ω).2}))
              atTop (nhds 0) := sorry

-- Proof sketch: the canonical realization owner says that `Z` is the Markov chain on `E × E`
-- with one-step kernel `discreteMatrixKernel (independentCoalescentMatrix p)`. Irreducibility
-- together with aperiodicity makes the pre-coalescence product dynamics hit the diagonal with
-- positive probability at arbitrarily large times, while positive recurrence is encoded here by
-- the existence of an invariant distribution for `discreteMatrixKernel p`; its product makes the
-- bivariate chain recurrent. Hence the diagonal is hit almost surely from every starting pair,
-- and once the chain reaches the diagonal it stays there, forcing the tail disagreement
-- probabilities to converge to `0`.
/-- Theorem 18.11: if `p` is the transition matrix of an irreducible, positive recurrent,
aperiodic Markov chain on `E`, with positive recurrence encoded here by the existence of an
invariant distribution for `discreteMatrixKernel p`, then every independent coalescent chain for
`p`, expressed through the canonical realization owner for
`discreteMatrixKernel (independentCoalescentMatrix p)`, is a successful Markov coupling. -/
theorem independentCoalescentChain_isSuccessfulMarkovCoupling
    {p : E → E → ℝ≥0∞}
    [Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel p)]
    (hinv : ∃ π : ProbabilityMeasure E, Kernel.Invariant (discreteMatrixKernel p) π)
    (haper : IsAperiodic (discreteMatrixKernel p))
    {P : E × E → ProbabilityMeasure Ω} {Z : ℕ → Ω → E × E}
    (hrealization :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel (independentCoalescentMatrix p) ^ n) P Z) :
    IsSuccessfulMarkovCoupling p P Z := sorry

end ProbabilityTheory
