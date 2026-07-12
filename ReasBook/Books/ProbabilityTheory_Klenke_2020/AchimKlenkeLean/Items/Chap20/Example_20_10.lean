import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap20.Definition_20_1
import ProbabilityTheory_Klenke_2020.Items.Chap20.Definition_20_11

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u

variable {E : Type u} [MeasurableSpace E]

local instance : MeasurableSpace (Stream' E) :=
  inferInstanceAs (MeasurableSpace (ℕ → E))

-- Proof sketch: prove by induction on `n` that each iterate of `Stream'.tail` drops the first
-- `n` coordinates, and then evaluate the resulting identity at `0`.
/-- The `n`th coordinate of a path is the initial coordinate after `n` iterates of the one-sided
shift. -/
theorem coordinate_eq_zero_after_iterate_tail (ω : ℕ → E) (n : ℕ) :
    ω n = (Stream'.tail^[n]) ω 0 := sorry

-- Proof sketch: rewrite stationarity of the canonical coordinate process as invariance of the path
-- law under every iterate of `Stream'.tail`; the case `n = 1` is exactly
-- `MeasurePreserving Stream'.tail P P`, and conversely measure preservation of `Stream'.tail`
-- propagates to all iterates.
/-- Example 20.10: on the canonical path space `E^ℕ`, the coordinate process is stationary exactly
when the left shift preserves the path measure. -/
theorem canonical_process_stationary_iff_measurePreserving_tail
    (P : Measure (ℕ → E)) :
    IsStationaryProcess Function.eval P ↔ MeasurePreserving Stream'.tail P P := sorry
