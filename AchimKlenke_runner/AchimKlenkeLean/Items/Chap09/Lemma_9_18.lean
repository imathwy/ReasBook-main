import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped MeasureTheory
open MeasureTheory

/- Lemma 9.18 (1): Part (i), the pointwise maximum of two stopping times is again a stopping
time. -/
recall MeasureTheory.IsStoppingTime.max

/- Lemma 9.18 (2): Part (i), the pointwise minimum of two stopping times is again a stopping
time. -/
recall MeasureTheory.IsStoppingTime.min

/- Lemma 9.18 (1): Part (ii), the sum of two nonnegative stopping times is again a stopping
time. -/
recall MeasureTheory.IsStoppingTime.add

/- Lemma 9.18 (2): Part (iii), delaying a stopping time by a deterministic nonnegative time
produces another stopping time. -/
recall MeasureTheory.IsStoppingTime.add_const'

/-- Lemma 9.18 (3): Part (iii), a deterministic backward shift of a stopping time need not be a
stopping time in general. -/
-- Proof sketch: Exhibit a filtered probability space and a stopping time `τ` for which the event
-- `{τ - s ≤ t}` depends on strictly more information than is available in the time-`t`
-- σ-algebra.
theorem exists_stoppingTime_sub_const_not_stoppingTime :
    ∃ (Ω : Type u) (m : MeasurableSpace Ω) (ℱ : Filtration NNReal m)
      (τ : Ω → WithTop NNReal), IsStoppingTime ℱ τ ∧
        ∃ s : NNReal, ¬ IsStoppingTime ℱ (fun ω ↦ τ ω - (s : WithTop NNReal)) := sorry
