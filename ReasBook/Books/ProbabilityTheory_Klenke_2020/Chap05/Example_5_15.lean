import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter ContinuousMap
open scoped unitInterval

/- The canonical Bernstein approximation on `[0,1]` is `bernsteinApproximation`. -/
recall bernsteinApproximation

/- The defining sum formula for the Bernstein approximation is
`bernsteinApproximation.apply`. -/
recall bernsteinApproximation.apply

/-
Example 5.15 is canonically the uniform-convergence theorem
`bernsteinApproximation_uniform` for real-valued continuous functions on `[0,1]`.
-/
recall bernsteinApproximation_uniform

/-- Example 5.15: for every continuous map `f : [0,1] → ℝ`, the Bernstein approximations
`bernsteinApproximation n f` converge to `f` in the supremum norm, equivalently uniformly on
`[0,1]`. -/
theorem bernsteinApproximation_tendsto_zero_in_norm (f : C(unitInterval, ℝ)) :
    Tendsto (fun n : ℕ ↦ ‖bernsteinApproximation n f - f‖) atTop (nhds 0) := by
  simpa [tendsto_iff_norm_sub_tendsto_zero] using bernsteinApproximation_uniform f
