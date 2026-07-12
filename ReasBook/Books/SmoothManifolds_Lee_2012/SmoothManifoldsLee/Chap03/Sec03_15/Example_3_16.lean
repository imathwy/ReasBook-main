import Mathlib.Analysis.SpecialFunctions.PolarCoord

-- Declarations for this item will be appended below by the statement pipeline.

/-- Example 3.16: at the polar point `(2, π / 2)`, the polar-coordinate tangent vector
`3 ∂/∂r - ∂/∂θ` has standard-coordinate components `(2, 3)`. -/
-- Proof sketch: unfold mathlib's owner `fderivPolarCoordSymm`, evaluate the resulting matrix on
-- `(3, -1)`, and simplify using `Real.cos_pi_div_two` and `Real.sin_pi_div_two`.
theorem polar_vector_in_standard_coordinates :
    fderivPolarCoordSymm (2, Real.pi / 2) (3, -1) = (2, 3) := by
  -- Expand the derivative into the explicit Jacobian action on pairs.
  unfold fderivPolarCoordSymm
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  -- Evaluate the trigonometric entries at `π / 2` and simplify the resulting coordinates.
  simp [Real.cos_pi_div_two, Real.sin_pi_div_two]
