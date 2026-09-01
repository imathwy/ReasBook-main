import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory.Measure

/- Remark 7.31: Mutual singularity of measures is symmetric. The textbook statement
`μ ⟂ₘ ν ↔ ν ⟂ₘ μ` is exactly the canonical mathlib equivalence `MutuallySingular.comm`
in the owner namespace `MeasureTheory.Measure`. -/
recall MutuallySingular.comm
