import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_24_1 (from Items/Chap24) -/
open MeasureTheory Set
open scoped ENNReal Topology

universe u

section

variable {E : Type u}

/-- The source-facing space `\mathcal{M}(E)` of boundedly finite measures: measures that assign
finite mass to every bounded measurable subset of `E`. -/
def BoundedlyFiniteMeasure (E : Type u) [PseudoMetricSpace E] [MeasurableSpace E] : Type u :=
  {μ : Measure E // ∀ ⦃A : Set E⦄, MeasurableSet A → Bornology.IsBounded A → μ A < ∞}

namespace BoundedlyFiniteMeasure

variable [PseudoMetricSpace E] [MeasurableSpace E]

/-- A boundedly finite measure can be interpreted as an ordinary measure. -/
@[coe] def toMeasure : BoundedlyFiniteMeasure E → Measure E := Subtype.val

instance : Coe (BoundedlyFiniteMeasure E) (Measure E) := ⟨toMeasure⟩

/-- A boundedly finite measure assigns finite mass to every bounded measurable subset of `E`. -/
theorem lt_top_of_isBounded (μ : BoundedlyFiniteMeasure E) {A : Set E}
    (hA : MeasurableSet A) (hA_bdd : Bornology.IsBounded A) :
    (μ : Measure E) A < ∞ :=
  μ.2 hA hA_bdd

end BoundedlyFiniteMeasure

/-- Definition 24.1: `𝕄` is the smallest sigma-algebra on the space `\mathcal{M}(E)` of boundedly
finite measures with respect to which every bounded Borel evaluation map `μ ↦ μ(A)` is
measurable. -/
@[reducible] def randomMeasureMeasurableSpace (E : Type u) [PseudoMetricSpace E]
    [MeasurableSpace E] :
    MeasurableSpace (BoundedlyFiniteMeasure E) :=
  ⨆ (A : Set E) (_ : MeasurableSet A) (_ : Bornology.IsBounded A),
    (borel ℝ≥0∞).comap fun μ ↦ (μ : Measure E) A

/-- The defining supremum formula for the random-measure sigma-algebra on
`BoundedlyFiniteMeasure E`. -/
@[simp]
theorem randomMeasureMeasurableSpace_def [PseudoMetricSpace E] [MeasurableSpace E] :
    randomMeasureMeasurableSpace E =
      ⨆ (A : Set E) (_ : MeasurableSet A) (_ : Bornology.IsBounded A),
        (borel ℝ≥0∞).comap fun μ : BoundedlyFiniteMeasure E ↦ (μ : Measure E) A :=
  rfl

/-- The sigma-algebra `randomMeasureMeasurableSpace E` is the ambient measurable structure on
`BoundedlyFiniteMeasure E`. -/
instance [PseudoMetricSpace E] [MeasurableSpace E] :
    MeasurableSpace (BoundedlyFiniteMeasure E) :=
  randomMeasureMeasurableSpace E

/-- Evaluation on a bounded Borel set is measurable for the random-measure sigma-algebra. -/
theorem measurable_apply_of_isBounded [PseudoMetricSpace E] [MeasurableSpace E]
    (A : Set E) (hA : MeasurableSet A)
    (hA_bdd : Bornology.IsBounded A) :
    Measurable fun μ : BoundedlyFiniteMeasure E ↦ (μ : Measure E) A := by
  exact Measurable.of_comap_le <|
    le_iSup_of_le A <| le_iSup_of_le hA <| le_iSup_of_le hA_bdd <| le_rfl

namespace MeasureTheory
namespace ProbabilityMeasure

variable [PseudoMetricSpace E] [MeasurableSpace E]

/-- The canonical inclusion of `\mathcal M_1(E)` into the space `\mathcal M(E)` of boundedly
finite measures. -/
def toBoundedlyFiniteMeasure (μ : ProbabilityMeasure E) : BoundedlyFiniteMeasure E :=
  ⟨μ, fun _ _ _ ↦ by simp⟩

/-- Coercing `μ.toBoundedlyFiniteMeasure` back to a measure recovers `μ`. -/
@[simp] theorem toMeasure_toBoundedlyFiniteMeasure (μ : ProbabilityMeasure E) :
    (μ.toBoundedlyFiniteMeasure : Measure E) = (μ : Measure E) :=
  rfl

end ProbabilityMeasure
end MeasureTheory

-- Proof sketch: the compact support is bounded in a pseudometric space, hence has finite measure
-- for a boundedly finite measure; the bounded range gives a uniform bound on `‖f‖`, so the
-- integral of `|f|` over its support is finite and `f` is integrable.
/-- Every bounded measurable real-valued function with compact support is integrable against a
boundedly finite measure. -/
theorem integrable_of_measurable_isBounded_range_hasCompactSupport
    [PseudoMetricSpace E] [MeasurableSpace E]
    (μ : BoundedlyFiniteMeasure E) {f : E → ℝ} (hf_measurable : Measurable f)
    (hf_bdd : Bornology.IsBounded (range f)) (hf_compact : HasCompactSupport f) :
    Integrable f (μ : Measure E) := sorry

end

/-! ### Exercise_24_1_1 (from Items/Chap24) -/
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

/-! ### Exercise_24_1_2 (from Items/Chap24) -/
open MeasureTheory
open scoped ENNReal Topology

universe u

variable {E : Type u} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace.SeparableSpace E]

-- Proof sketch: identify `\mathcal M_1(E)` with `ProbabilityMeasure E`, pull back the
-- random-measure sigma-algebra `𝕄` along the canonical inclusion into `BoundedlyFiniteMeasure E`,
-- and compare the resulting generated sigma-algebra with the Borel sigma-algebra of the weak
-- topology on `ProbabilityMeasure E`.
/-- Exercise 24.1.2: the restriction of the random-measure sigma-algebra `𝕄` to the probability
measures `\mathcal M_1(E)` agrees with the Borel sigma-algebra of the weak-convergence topology
on `ProbabilityMeasure E`. -/
theorem randomMeasureMeasurableSpace_comap_probabilityMeasure_eq_borel :
    MeasurableSpace.comap ProbabilityMeasure.toBoundedlyFiniteMeasure
      (randomMeasureMeasurableSpace E) =
        borel (ProbabilityMeasure E) := sorry
