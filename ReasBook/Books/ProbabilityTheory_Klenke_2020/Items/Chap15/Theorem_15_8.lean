import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

/- Theorem 15.8: a finite measure on `ℝ^d` is characterized by its characteristic function.
This is the owner-level uniqueness theorem for the canonical map `charFun`: mathlib's
`Measure.ext_of_charFun`, valid on complete second-countable real inner product spaces and hence in
particular on `EuclideanSpace ℝ (Fin d)`. -/
recall Measure.ext_of_charFun
