import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-- Definition 1.98: For a measurable map `X : Ω → Ω'` and a measure `μ` on `Ω`, the image
measure of `μ` under `X` is the canonical mathlib pushforward measure `μ.map X` on `Ω'`. -/
recall MeasureTheory.Measure.map

/-- On measurable sets `A'`, the image measure `μ.map X` is given by the textbook formula
`μ.map X A' = μ (X ⁻¹' A')`. -/
recall MeasureTheory.Measure.map_apply
