import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u

-- Proof sketch: apply `ProbabilityTheory.iIndepFun.iIndepFun_process` to the two-point process
-- `n ↦ (X (2 * n + 2), X (2 * n + 1))`. For each finite family of indices, the corresponding
-- coordinates come from pairwise disjoint subsets of the original sequence, so the needed finite
-- tuple-independence follows from the finitary tuple construction lemmas for `iIndepFun`.
/- Internal support lemma: the process of adjacent coordinate pairs extracted from an independent
real-valued sequence is itself independent. -/
private theorem iIndepFun_adjacent_pairs_of_iIndepFun
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}
    (hX_meas : ∀ n, Measurable (X n)) (hX_indep : iIndepFun X μ) :
    iIndepFun (fun n ω ↦ (X (2 * n + 2) ω, X (2 * n + 1) ω)) μ := sorry

-- Proof sketch: first use `iIndepFun_adjacent_pairs_of_iIndepFun` to obtain independence of the
-- pair process `n ↦ (X (2 * n + 2), X (2 * n + 1))`, then postcompose each pair with the
-- measurable subtraction map `(x, y) ↦ x - y` via `ProbabilityTheory.iIndepFun.comp`.
/-- Example 2.27: with Lean's `0`-based indexing, the textbook family
`(X_{2n} - X_{2n-1})_{n ∈ ℕ}` is rendered as
`(X (2 * n + 2) - X (2 * n + 1))_{n ∈ ℕ}`; this adjacent-pair difference family is independent
whenever `X` is an independent family of real random variables. -/
theorem iIndepFun_adjacent_pair_differences_of_iIndepFun
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}
    (hX_meas : ∀ n, Measurable (X n)) (hX_indep : iIndepFun X μ) :
    iIndepFun (fun n ω ↦ X (2 * n + 2) ω - X (2 * n + 1) ω) μ := sorry
