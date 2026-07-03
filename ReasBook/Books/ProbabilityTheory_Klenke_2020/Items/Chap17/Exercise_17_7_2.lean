import AchimKlenkeLean.Items.Chap17.Theorem_17_60

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

noncomputable section

/- Exercise 17.7.2 (first claim): reflexivity is already the chapter stochastic-order owner from
Definition 17.57, specialized to the embedded nat-valued laws. -/
recall stochasticLE_refl

-- Proof sketch: for the forward implication, test the stochastic order with increasing tail or
-- truncated identity functions to recover `λ₁ ≤ λ₂`; for the reverse implication, couple
-- `Poi_{λ₂}` as `Poi_{λ₁} + Poi_{λ₂ - λ₁}` when `λ₁ ≤ λ₂`.
/-- Exercise 17.7.2: the Poisson law with parameter `λ₁` is below the Poisson law with parameter
`λ₂` in the discrete stochastic order on `ℕ` if and only if `λ₁ ≤ λ₂`. -/
theorem poissonMeasure_stochasticLE_iff (lam1 lam2 : NNReal) :
    StochasticLE
      (ProbabilityMeasure.toFin1Real
        (⟨poissonMeasure lam1, inferInstance⟩ : ProbabilityMeasure ℕ))
      (ProbabilityMeasure.toFin1Real
        (⟨poissonMeasure lam2, inferInstance⟩ : ProbabilityMeasure ℕ)) ↔
      lam1 ≤ lam2 := sorry
