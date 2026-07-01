import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

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
