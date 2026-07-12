import Mathlib
import Mathlib.Dynamics.Ergodic.Ergodic

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

variable {E : Type u} [MeasurableSpace E]

/- Definition 20.11: for the canonical process on the path space `ℕ → E`, ergodicity is exactly
the canonical mathlib notion `Ergodic` for the one-sided shift `Stream'.tail` acting on the
path-space law. No separate process-specific wrapper is needed. -/
#check (fun P : Measure (ℕ → E) ↦ Ergodic Stream'.tail P)
