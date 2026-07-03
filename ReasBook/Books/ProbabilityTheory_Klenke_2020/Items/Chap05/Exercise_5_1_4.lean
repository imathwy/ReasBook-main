import ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_14

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

/-- The weighted exponential series from Exercise 5.1.4, written in the textbook indexing
`X 1, X 2, ...`. -/
def weightedExpSeries (X : ℕ → Ω → ℝ) (c : Set.Ioo (0 : ℝ) 1) (ω : Ω) : ℝ≥0∞ :=
  ∑' n, ENNReal.ofReal (Real.exp (X (n + 1) ω) * (c : ℝ) ^ (n + 1))

-- Proof sketch: apply the Borel--Cantelli lemma to the tail events
-- `{ω | X (n + 1) ω > -(n + 1) * Real.log (c : ℝ) - Real.log ((n + 1 : ℝ)^2)}`. Finite first
-- moment gives summability of the corresponding probabilities, hence eventually
-- `exp (X (n + 1) ω) * (c : ℝ)^(n + 1) ≤ (n + 1)⁻²`, which makes `weightedExpSeries X c ω`
-- surely by comparison with the convergent p-series.
/-- Exercise 5.1.4 (1): if `X₁, X₂, …` are i.i.d. nonnegative real random variables on a
probability space, `X₁` is almost surely nonnegative, and `X₁` has finite expectation,
equivalently `Integrable (X 1) P` under this nonnegativity hypothesis, then for every
`c ∈ (0, 1)` the weighted exponential series `∑ exp(Xₙ) cⁿ` is finite almost surely. -/
theorem ae_weightedExpSeries_lt_top_of_integrable (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (c : Set.Ioo (0 : ℝ) 1) (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX1_nonneg : 0 ≤ᵐ[P] X 1) (hX1_integrable : Integrable (X 1) P) :
    ∀ᵐ ω ∂P, weightedExpSeries X c ω < ∞ := sorry

-- Proof sketch: use the same threshold events as in the finite-moment case. When `X 1` is not
-- integrable, equivalently its nonnegative expectation is infinite, a tail-integral estimate
-- together with identical distribution shows that the probabilities of these events have
-- divergent sum; independence and the second Borel--Cantelli lemma then yield infinitely many
-- occurrences almost surely, forcing the partial sums of the nonnegative series to diverge to
-- `∞`.
/-- Exercise 5.1.4 (2): if `X₁, X₂, …` are i.i.d. nonnegative real random variables on a
probability space, `X₁` is almost surely nonnegative, and `X₁` has infinite expectation,
equivalently `¬ Integrable (X 1) P` under this nonnegativity hypothesis, then for every
`c ∈ (0, 1)` the weighted exponential series `∑ exp(Xₙ) cⁿ` is equal to `∞` almost surely. -/
theorem ae_weightedExpSeries_eq_top_of_not_integrable (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (c : Set.Ioo (0 : ℝ) 1) (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX1_nonneg : 0 ≤ᵐ[P] X 1) (hX1_not_integrable : ¬ Integrable (X 1) P) :
    ∀ᵐ ω ∂P, weightedExpSeries X c ω = ∞ := sorry
