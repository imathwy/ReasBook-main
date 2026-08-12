import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

/- Definition 4.12: By Example 1.71, Lebesgue measure on `ℝⁿ` is the completed measure
`Measure.completion (volume : Measure (Fin n → ℝ))` on the completed measurable space
`NullMeasurableSpace (Fin n → ℝ) (volume : Measure (Fin n → ℝ))`. On that completed space, the
Lebesgue integral of an integrable real-valued function is the canonical Bochner integral
`MeasureTheory.integral`. -/
recall MeasureTheory.integral

/- For a Lebesgue-measurable set `A` in the completed Lebesgue `σ`-algebra on `ℝⁿ`, equivalently
for a `volume`-null-measurable set in the Borel presentation, the set integral with respect to the
same completed Lebesgue measure is the whole-space integral of the indicator function
`A.indicator f`. This is the null-measurable-set form `MeasureTheory.integral_indicator₀`. -/
recall MeasureTheory.integral_indicator₀
