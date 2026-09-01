import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

/-- Lemma 1.49: A set belongs to the Carathéodory measurable space of an outer measure if and
only if for every set `E`, the sum of the outer measures of `A ∩ E` and `Aᶜ ∩ E` is bounded above
by the outer measure of `E`. -/
-- Proof sketch: rewrite the textbook condition using `Aᶜ ∩ E = E \ A` and apply
-- `MeasureTheory.OuterMeasure.isCaratheodory_iff_le`; the converse direction uses subadditivity of
-- the outer measure.
theorem measurableSet_caratheodory_iff_le_inter_compl {Ω : Type u} (μ : OuterMeasure Ω)
    (A : Set Ω) :
    MeasurableSet[μ.caratheodory] A ↔ ∀ E : Set Ω, μ (A ∩ E) + μ (Aᶜ ∩ E) ≤ μ E := by
  -- Rewrite the textbook partition of `E` into the canonical Carathéodory form `E ∩ A` and `E \ A`.
  simpa [Set.diff_eq, Set.inter_comm] using
    (μ.isCaratheodory_iff_le (s := A))
