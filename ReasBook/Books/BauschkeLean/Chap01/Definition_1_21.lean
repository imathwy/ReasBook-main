import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 1.21: for an extended-real-valued function `f : X → EReal`, lower semicontinuity
at a point `x` is the canonical predicate `LowerSemicontinuousAt f x`, and lower semicontinuity
on `X` is the canonical predicate `LowerSemicontinuous f`. -/
recall LowerSemicontinuousAt

/- Companion recall: the textbook liminf inequality along every convergent net is expressed in
mathlib by the neighborhood-filter characterization `lowerSemicontinuousAt_iff_le_liminf`. -/
recall lowerSemicontinuousAt_iff_le_liminf

/- Companion recall: lower semicontinuity on the whole space is the canonical predicate
`LowerSemicontinuous f`. -/
recall LowerSemicontinuous

/- Companion recall: global lower semicontinuity is exactly pointwise lower semicontinuity. -/
recall lowerSemicontinuous_iff
