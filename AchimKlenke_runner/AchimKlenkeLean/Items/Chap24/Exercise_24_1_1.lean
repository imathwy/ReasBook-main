import AchimKlenkeLean.Items.Chap24.Definition_24_1
import AchimKlenkeLean.Items.Chap24.Definition_24_3
import AchimKlenkeLean.Items.Chap24.Theorem_24_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [PseudoMetricSpace E] [MeasurableSpace E]

/-- The countable weighted sum `ω ↦ ∑' n, weights n • X n ω` of a family of measure-valued random
variables. -/
def weightedRandomMeasureSeries (weights : ℕ → NNReal) (X : ℕ → Ω → Measure E) : Ω → Measure E :=
  fun ω ↦ Measure.sum fun n ↦ (weights n : ENNReal) • X n ω

-- Proof sketch: unfold `weightedRandomMeasureSeries` and evaluate the countable sum of measures on
-- the measurable set `A`; then use `Measure.sum_apply` and `Measure.smul_apply`.
/-- Evaluating the weighted random-measure series on a measurable set gives the corresponding
weighted series of evaluations. -/
theorem weightedRandomMeasureSeries_apply
    (weights : ℕ → NNReal) (X : ℕ → Ω → Measure E) (ω : Ω) {A : Set E} (hA : MeasurableSet A) :
    weightedRandomMeasureSeries weights X ω A =
      ∑' n, (weights n : ENNReal) * X n ω A := sorry

-- Proof sketch: combine the defining measurability and almost-sure local-finiteness clauses of
-- `IsRandomMeasure` with the metric-space characterization that a measure is locally finite
-- exactly when it is finite on every bounded measurable set, then rewrite the almost-sure
-- condition pointwise on those bounded sets.
/-- A measurable measure-valued random variable is a random measure exactly when every bounded
measurable set has finite mass almost surely. -/
theorem isRandomMeasure_iff_ae_lt_top_on_bounded
    (P : ProbabilityMeasure Ω) {X : Ω → Measure E} (hX : Measurable X) :
    IsRandomMeasure P X ↔
      ∀ A : Set E, MeasurableSet A → Bornology.IsBounded A →
        ∀ᵐ ω ∂(P : Measure Ω), X ω A < ∞ := sorry

-- Proof sketch: measurability of each `X n` follows from `(hX n).measurable`; countable sums and
-- scalar multiples preserve measurability into `Measure E`. Then apply
-- `isRandomMeasure_iff_ae_lt_top_on_bounded` to the series `ω ↦ ∑' n, λ n • X n ω`.
/-- Exercise 24.1.1: for a countable weighted sum of random measures, being a random measure is
equivalent to almost-sure finiteness on every bounded measurable set. -/
theorem isRandomMeasure_weightedRandomMeasureSeries_iff_ae_lt_top_on_bounded
    (P : ProbabilityMeasure Ω) (weights : ℕ → NNReal) (X : ℕ → Ω → Measure E)
    (hX : ∀ n, IsRandomMeasure P (X n)) :
    IsRandomMeasure P (weightedRandomMeasureSeries weights X) ↔
      ∀ A : Set E, MeasurableSet A → Bornology.IsBounded A →
        ∀ᵐ ω ∂(P : Measure Ω), weightedRandomMeasureSeries weights X ω A < ∞ := sorry

-- Proof sketch: apply `intensityMeasure_apply` to the canonical kernel `Kernel.mk X hX` to
-- identify the bounded-set expectation with a Lebesgue integral. Finite intensity on each bounded
-- measurable set yields almost-sure finiteness there by `ae_lt_top`, and the previous
-- characterization then gives `IsRandomMeasure P X`.
/-- If a measurable measure-valued random variable has finite intensity on every bounded
measurable set, then it is a random measure. -/
theorem isRandomMeasure_of_intensityMeasure_lt_top_on_bounded
    (P : ProbabilityMeasure Ω) (X : Ω → Measure E) (hX : Measurable X)
    (hEX :
      ∀ A : Set E, MeasurableSet A → Bornology.IsBounded A →
        intensityMeasure P (Kernel.mk X hX) A < ∞) :
    IsRandomMeasure P X := sorry

end ProbabilityTheory
