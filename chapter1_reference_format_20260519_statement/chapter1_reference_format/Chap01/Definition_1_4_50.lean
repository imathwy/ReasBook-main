import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Definition 1.4.50: an algebraic number field is the canonical mathlib predicate
`NumberField K`, i.e. a field `K` that is finite-dimensional over `ℚ` (equivalently, a finite
extension of `ℚ`). -/
recall NumberField (K : Type u) [Field K] : Prop
