import Mathlib
import AchimKlenkeLean.Items.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

/-
Corollary 16.8 is `source-facing`: it characterizes infinite divisibility directly at the
characteristic-function level by existence of a positive-integer-root approximation sequence. The
owner abstraction remains `IsInfinitelyDivisibleCFP`; the sequence in the right-hand side is
derived API, not new primitive data. The reverse implication is mediated by the chapter bridge
results in Theorem 16.6 / Corollary 16.7.
-/
-- Proof sketch: for the forward implication, take for each positive integer `n` the
-- characteristic-function root supplied by `IsInfinitelyDivisibleCFP`; then the `n`th
-- powers are exactly `φ`, so the sequence converges trivially. For the converse implication, apply
-- Corollary 16.7 to the pointwise limit of the `n`th powers of characteristic functions, using
-- the assumed continuity of `φ` at `0`.
/-- Corollary 16.8: a complex-valued function on `ℝ` that is continuous at `0` is an infinitely
divisible characteristic function if and only if there is a sequence of characteristic functions of
probability laws on `ℝ`, indexed by positive integers, whose `n`th pointwise powers converge to
`φ`. -/
theorem isInfinitelyDivisibleCFP_iff_exists_charFun_pow_tendsto
    {φ : ℝ → ℂ} (hφ : ContinuousAt φ 0) :
    IsInfinitelyDivisibleCFP φ ↔
      ∃ φs : ℕ+ → ℝ → ℂ,
        (∀ n : ℕ+, IsCFP (φs n)) ∧
          ∀ t, Tendsto (fun n : ℕ+ ↦ (φs n t) ^ (n : ℕ)) atTop (𝓝 (φ t)) := sorry
