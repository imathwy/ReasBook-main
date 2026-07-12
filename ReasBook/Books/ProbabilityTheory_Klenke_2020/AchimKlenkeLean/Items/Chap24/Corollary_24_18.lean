import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap16.Theorem_16_14

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped MeasureTheory

noncomputable section

namespace MeasureTheory.ProbabilityMeasure

/-- The stochastic order on probability laws on `[0, ∞)` tested against bounded measurable
increasing real-valued functions. -/
def NNRealStochasticLE (μ₁ μ₂ : ProbabilityMeasure NNReal) : Prop :=
  ∀ ⦃f : NNReal → ℝ⦄, Monotone f →
    Bornology.IsBounded (Set.range f) →
    Measurable f →
    ∫ x, f x ∂(μ₁ : Measure NNReal) ≤ ∫ x, f x ∂(μ₂ : Measure NNReal)

-- Proof sketch: for every admissible increasing test function `f`, both sides of the defining
-- inequality are the same integral when the two laws coincide.
/-- The stochastic order on `[0, ∞)` is reflexive. -/
theorem nnrealStochasticLE_refl (μ : ProbabilityMeasure NNReal) :
    NNRealStochasticLE μ μ := sorry

-- Proof sketch: represent each law by the Chapter 16 Lévy--Khinchin data `(αᵢ, νᵢ)` and use the
-- Poisson-point-process construction from Theorems 24.16 and 24.17. Pushing one Poisson point
-- process with Lebesgue intensity through the generalized inverse of the tail functions
-- `x ↦ νᵢ (Set.Ici x)` gives coupled random variables with laws `μᵢ`; the tail comparison forces
-- the first inverse and hence the first random variable to be pointwise smaller. The resulting
-- almost sure order implies stochastic order.
/-- Corollary 24.18: if two infinitely divisible probability laws on `[0, ∞)` have
Lévy--Khinchin data `(α₁, ν₁)` and `(α₂, ν₂)` with `α₁ ≤ α₂` and
`ν₁([x, ∞)) ≤ ν₂([x, ∞))` for every `x > 0`, then the first law is stochastically smaller than
the second. On `NNReal`, the tail sets `[x, ∞)` are represented by `Set.Ici x`. -/
theorem levyKhinchin_tail_order_implies_nnrealStochasticLE
    {μ₁ μ₂ : ProbabilityMeasure NNReal} {α₁ α₂ : NNReal} {ν₁ ν₂ : Measure NNReal}
    (hrep₁ : HasSubordinatorLevyKhinchinRepresentation μ₁ α₁ ν₁)
    (hrep₂ : HasSubordinatorLevyKhinchinRepresentation μ₂ α₂ ν₂)
    (hα : α₁ ≤ α₂)
    (hν : ∀ x : NNReal, 0 < x → ν₁ (Set.Ici x) ≤ ν₂ (Set.Ici x)) :
    NNRealStochasticLE μ₁ μ₂ := sorry

end MeasureTheory.ProbabilityMeasure
