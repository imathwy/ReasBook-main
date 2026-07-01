import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

/- Exercise 13.2.11 is source-facing. Its owner abstraction is weak convergence in
`ProbabilityMeasure ℝ`, and the scaled geometric law is the derived pushforward of the geometric
probability measure along `k ↦ k / n`, so no separate public wrapper definition is needed. -/

private noncomputable def geometricProbabilityMeasure (p : ℝ) (hp_pos : 0 < p) (hp_lt_one : p < 1) :
    ProbabilityMeasure ℕ :=
  ⟨geometricMeasure hp_pos (le_of_lt hp_lt_one),
    isProbabilityMeasure_geometricMeasure hp_pos (le_of_lt hp_lt_one)⟩

private noncomputable def expProbabilityMeasure (α : ℝ) (hα : 0 < α) : ProbabilityMeasure ℝ :=
  ⟨expMeasure α, isProbabilityMeasure_expMeasure hα⟩

/-- Exercise 13.2.11: the laws of the scaled geometric variables `Xₙ / n` converge weakly to the
exponential distribution with rate `α` exactly when the success probabilities satisfy
`n * pₙ → α`. -/
-- Proof sketch: view the law of `Xₙ / n` directly as the pushforward of the geometric
-- probability measure under `k ↦ k / n`, compute the associated distribution functions from the
-- explicit geometric and exponential formulas, and use the limit
-- `(1 - pₙ)^(n x) → exp (-α * x)` to show that weak convergence is equivalent to
-- `n * pₙ → α`.
theorem scaled_geometric_law_tendsto_expMeasure_iff
    (α : ℝ) (hα : 0 < α) (p : ℕ+ → ℝ) (hp_pos : ∀ n, 0 < p n)
    (hp_lt_one : ∀ n, p n < 1) :
    Tendsto
      (fun n ↦
        (geometricProbabilityMeasure (p n) (hp_pos n) (hp_lt_one n)).map
          ((measurable_of_countable fun k : ℕ ↦ (k : ℝ) / (n : ℝ)).aemeasurable))
      atTop
      (𝓝 (expProbabilityMeasure α hα)) ↔
    Tendsto (fun n : ℕ+ ↦ (n : ℝ) * p n) atTop (𝓝 α) := sorry
