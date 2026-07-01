import Mathlib
import AchimKlenkeLean.Items.Chap12.Definition_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators

universe u

noncomputable section

-- Proof sketch: realize the textbook counterexample on a common probability space, verify that
-- each sequence is exchangeable, compute that the induced laws on `ℝ^ℕ` are distinct, and show
-- that every finite partial sum process has the same one-dimensional distribution for the two
-- sequences.
/-- Exercise 15.3.1: there exist two exchangeable sequences of real random variables on a common
probability space whose laws as `ℝ^ℕ`-valued random variables are different, although for every
`n` their first `n` partial sums have the same distribution. In the canonical `0`-based Lean
indexing, these partial sums are `ω ↦ ∑ k ∈ Finset.range n, X k ω` and
`ω ↦ ∑ k ∈ Finset.range n, Y k ω`. -/
theorem exists_exchangeable_sequences_with_equal_partial_sum_laws_and_distinct_sequence_laws :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X Y : ℕ → Ω → ℝ),
      Measurable (Function.swap X) ∧
        Measurable (Function.swap Y) ∧
        IsExchangeable X P ∧
        IsExchangeable Y P ∧
        Measure.map (Function.swap X) P ≠ Measure.map (Function.swap Y) P ∧
        (∀ n, IdentDistrib
          (fun ω ↦ ∑ k ∈ Finset.range n, X k ω)
          (fun ω ↦ ∑ k ∈ Finset.range n, Y k ω) P P) := sorry
