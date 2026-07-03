import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_17_60 (from Items/Chap17) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory unitInterval

noncomputable section

namespace MeasureTheory.ProbabilityMeasure

private theorem measurable_natToFin1Real : Measurable (fun n : ℕ ↦ (![n] : Fin 1 → ℝ)) := by
  simpa using (Measurable.of_discrete : Measurable (fun n : ℕ ↦ (![n] : Fin 1 → ℝ)))

/-- View a probability law on `ℕ` as a one-dimensional law in the chapter's ambient state space
`Fin 1 → ℝ`. -/
abbrev toFin1Real (μ : ProbabilityMeasure ℕ) : ProbabilityMeasure (Fin 1 → ℝ) :=
  ProbabilityMeasure.map μ measurable_natToFin1Real.aemeasurable

end MeasureTheory.ProbabilityMeasure

namespace ProbabilityTheory

-- Proof sketch: in one dimension, increasing bounded measurable test functions on the embedded
-- laws are equivalent to increasing bounded measurable functions on `ℕ`; the indicator functions
-- of the upper tails `Set.Ici k` recover the textbook inequalities, and conversely the tail
-- family determines the stochastic order on laws supported on `ℕ`.
/-- For nat-valued laws embedded into `Fin 1 → ℝ`, the chapter owner `StochasticLE` is equivalent
to comparison of all upper tails `μ([k, ∞))`. -/
theorem stochasticLE_toFin1Real_iff_upper_tail (μ₁ μ₂ : ProbabilityMeasure ℕ) :
    StochasticLE μ₁.toFin1Real μ₂.toFin1Real ↔
      ∀ k : ℕ, (μ₁ : Measure ℕ) (Set.Ici k) ≤ (μ₂ : Measure ℕ) (Set.Ici k) := sorry

/-- Any stochastic-order comparison between probability laws on `ℕ` compares their upper tails at
each threshold `k`. -/
theorem StochasticLE.upper_tail_nat {μ₁ μ₂ : ProbabilityMeasure ℕ}
    (h : StochasticLE μ₁.toFin1Real μ₂.toFin1Real) (k : ℕ) :
    (μ₁ : Measure ℕ) (Set.Ici k) ≤ (μ₂ : Measure ℕ) (Set.Ici k) :=
  (stochasticLE_toFin1Real_iff_upper_tail μ₁ μ₂).1 h k

-- Proof sketch: express the comparison directly in the chapter owner `StochasticLE` on the
-- embedded one-dimensional laws, then use `stochasticLE_toFin1Real_iff_upper_tail` to recover
-- the textbook tail inequalities. The necessity of (17.30) comes from the atom at `0`, and the
-- necessity of (17.31) comes from comparing the maximal possible values. Sufficiency is obtained
-- by the occupancy coupling from Example 17.59 together with Theorem 17.58 in the interior case
-- `0 < p₂ < 1`; the endpoint cases `p₂ = 0` and `p₂ = 1` reduce directly to degenerate binomial
-- laws and satisfy the same criterion.
/-- Theorem 17.60: for `p₁ ∈ (0,1)` and arbitrary `p₂ : I`, the binomial law `Bin(n₁, p₁)` is
below `Bin(n₂, p₂)` in stochastic order if and only if (17.30)
`(1 - p₁)^n₁ ≥ (1 - p₂)^n₂` and (17.31) `n₁ ≤ n₂`. -/
theorem binomial_stochasticLE_iff
    (n₁ n₂ : ℕ) (p₁ p₂ : I)
    (hp₁₀ : 0 < (p₁ : ℝ)) (hp₁₁ : (p₁ : ℝ) < 1)
    : StochasticLE
        (ProbabilityMeasure.toFin1Real
          (⟨Bin(n₁, p₁), inferInstance⟩ : ProbabilityMeasure ℕ))
        (ProbabilityMeasure.toFin1Real
          (⟨Bin(n₂, p₂), inferInstance⟩ : ProbabilityMeasure ℕ)) ↔
        (1 - (p₁ : ℝ)) ^ n₁ ≥ (1 - (p₂ : ℝ)) ^ n₂ ∧ n₁ ≤ n₂ := sorry

end ProbabilityTheory
