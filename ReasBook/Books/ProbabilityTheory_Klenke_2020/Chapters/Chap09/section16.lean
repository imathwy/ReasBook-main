import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_9_16 (from Items/Chap09) -/
open scoped MeasureTheory
open MeasureTheory

universe u v

/-- Theorem 9.16: For a countable time index set, a random time is a stopping time if and only if
each level event `{τ = t}` is measurable with respect to the time-`t` σ-algebra. -/
-- Proof sketch: Use `MeasureTheory.IsStoppingTime.measurableSet_eq_of_countable` for the forward
-- direction. For the converse, apply `MeasureTheory.isStoppingTime_of_measurableSet_eq`, which
-- rewrites `{τ ≤ t}` as a countable union of the events `{τ = s}` with `s ≤ t`.
theorem isStoppingTime_iff_measurableSet_eq
    {Ω : Type u} {ι : Type v} {mΩ : MeasurableSpace Ω} [PartialOrder ι] [Countable ι]
    (ℱ : Filtration ι mΩ) (τ : Ω → WithTop ι) :
    IsStoppingTime ℱ τ ↔
      ∀ t : ι, MeasurableSet[ℱ t] {ω | τ ω = t} := by
  constructor
  · intro hτ t
    exact hτ.measurableSet_eq_of_countable t
  · intro hτ
    exact isStoppingTime_of_measurableSet_eq hτ
