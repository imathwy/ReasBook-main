import Mathlib

open MeasureTheory
open scoped MeasureTheory

/-- Remark 2.30: The convolution of two measures on `ℤ` is symmetric. -/
theorem integer_measure_convolution_comm (μ ν : Measure ℤ) :
    μ ∗ ν = ν ∗ μ := by
  simpa using Measure.conv_comm μ ν
