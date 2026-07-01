import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: compare both measures on an arbitrary set `s`; `Measure.completion_apply` reduces
-- the left-hand side to `Measure.dirac ω s`, and the right-hand side is the same Dirac measure on
-- the type alias `NullMeasurableSpace Ω (Measure.dirac ω)`.
/-- Example 1.72: The completion of the Dirac measure at `ω` is again the Dirac measure at `ω`,
now viewed on the completed measurable space `NullMeasurableSpace Ω (Measure.dirac ω)`. -/
theorem dirac_completion_eq_dirac (ω : Ω) :
    Measure.completion (Measure.dirac ω) =
      (Measure.dirac ω : Measure (NullMeasurableSpace Ω (Measure.dirac ω))) := sorry

-- Proof sketch: if `ω ∉ s`, then `s` is `δ_ω`-null, hence completion-measurable; if `ω ∈ s`,
-- then `s \ {ω}` is `δ_ω`-null and `s = {ω} ∪ (s \ {ω})`, so the measurability of `{ω}` makes `s`
-- completion-measurable as well.
/-- If `{ω}` is measurable, then every set is `δ_ω`-null-measurable; equivalently, every subset is
measurable in the completion of `Measure.dirac ω`. -/
theorem nullMeasurableSet_dirac_of_singleton (ω : Ω)
    (hω : MeasurableSet ({ω} : Set Ω)) (s : Set Ω) :
    NullMeasurableSet s (Measure.dirac ω) := sorry

-- Proof sketch: when the original measurable space is `⊥`, the only measurable sets are `∅` and
-- `univ`, and the only `δ_ω`-null set is `∅`; the completion therefore adds no new measurable
-- sets.
/-- On the trivial `σ`-algebra, the `δ_ω`-null-measurable sets are exactly `∅` and `univ`;
equivalently, the completion adds no new measurable sets. -/
theorem nullMeasurableSet_dirac_iff_empty_or_univ_of_bot (ω : Ω)
    (hΩ : ‹MeasurableSpace Ω› = ⊥) (s : Set Ω) :
    NullMeasurableSet s (Measure.dirac ω) ↔ s = ∅ ∨ s = univ := sorry

-- Proof sketch: with the trivial `σ`-algebra, two Dirac measures agree on the only measurable
-- sets `∅` and `univ`, so they are equal.
/-- On the trivial `σ`-algebra, Dirac measures at different points cannot be distinguished. -/
theorem dirac_eq_dirac_of_bot (ω₁ ω₂ : Ω) (hΩ : ‹MeasurableSpace Ω› = ⊥) :
    (Measure.dirac ω₁ : Measure Ω) = Measure.dirac ω₂ := sorry
