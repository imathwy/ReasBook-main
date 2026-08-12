import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 8.34: an isomorphism of measurable spaces is the canonical owner notion
`MeasurableEquiv`, i.e. a bijection whose forward and inverse maps are both measurable. -/
recall MeasurableEquiv

/- A measure-space isomorphism is not a separate owner structure: it is a measurable equivalence
`e : α ≃ᵐ β` together with the canonical measure-preservation predicate
`MeasureTheory.MeasurePreserving e μ ν`. -/
recall MeasureTheory.MeasurePreserving
