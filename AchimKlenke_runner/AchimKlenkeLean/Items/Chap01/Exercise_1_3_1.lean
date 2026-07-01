import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

open scoped ENNReal

-- Proof sketch: a Lebesgue--Stieltjes measure on `ℝ` is locally finite, so every bounded interval
-- has finite mass; for the weighted atomic measure this interval mass is exactly the bounded
-- partial weight sum. Conversely, the bounded-weight summability hypothesis gives local finiteness
-- of the atomic measure, and one reconstructs a monotone right-continuous distribution function
-- whose Stieltjes measure is the given weighted Dirac sum.
/-- The weighted atomic measure `∑' n, α n δ_(x n)` on `ℝ` is locally finite exactly when the
total weight of the atoms in every bounded interval `[-K, K]` is finite. -/
theorem weightedDiracSum_isLocallyFiniteMeasure_iff_boundedWeightSummable
    (x : ℕ → ℝ) (α : ℕ → NNReal) :
    IsLocallyFiniteMeasure
        (Measure.sum (fun n ↦ (α n : ℝ≥0∞) • Measure.dirac (x n))) ↔
      ∀ K : ℝ, 0 < K → Summable (fun n ↦ if |x n| ≤ K then α n else 0) := sorry

/-- Exercise 1.3.1: The weighted atomic measure `∑' n, α n δ_(x n)` on `ℝ` is a
Lebesgue--Stieltjes measure if and only if the total weight of the atoms in every bounded set
`[-K, K]` is finite. -/
theorem weightedDiracSum_isLebesgueStieltjes_iff_boundedWeightSummable
    (x : ℕ → ℝ) (α : ℕ → NNReal) :
    (∃ F : StieltjesFunction ℝ,
      F.measure = Measure.sum (fun n ↦ (α n : ℝ≥0∞) • Measure.dirac (x n))) ↔
      ∀ K : ℝ, 0 < K → Summable (fun n ↦ if |x n| ≤ K then α n else 0) := sorry
