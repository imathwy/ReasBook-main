import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped unitInterval

/-- Example 1.74: The restriction of Lebesgue measure on `ℝ` to `[0,1]`, represented by the
canonical volume measure on the unit interval subtype `I`, is a probability measure on the trace
Borel `σ`-algebra of `[0,1]`. -/
theorem unitInterval_volume_isProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure I) := inferInstance
