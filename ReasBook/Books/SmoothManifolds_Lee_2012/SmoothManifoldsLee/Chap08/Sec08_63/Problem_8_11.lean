import Mathlib.Analysis.SpecialFunctions.PolarCoord
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap08.Sec08_54.Example_8_3
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap08.Sec08_57.Example_8_17

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold
open NormedSpace

noncomputable section

local notation "Plane" => ℝ × ℝ

-- Domain sampling pass: the source-facing statements here live in the polar-coordinate /
-- tangent-vector domain. The core/canonical owners are the chapter's `euler_vector_field`,
-- mathlib's `polarCoord`, `fderivPolarCoordSymm`, and the canonical tangent-space identification
-- `fromTangentSpace`. The only primitive source-facing data introduced here is the additional
-- plane field `problem_8_11_radius_squared_x_field`; the polar-coordinate formulas are derived
-- bridge/view API for `polarCoord.symm`.

/-- The vector field `Z = (x^2 + y^2) ∂/∂x` on the plane. -/
def problem_8_11_radius_squared_x_field (p : Plane) : TangentSpace 𝓘(ℝ, Plane) p :=
  (fromTangentSpace p).symm (p.1 ^ 2 + p.2 ^ 2, 0)

/-- Under the canonical tangent-space identification, `problem_8_11_radius_squared_x_field` has
coordinate vector `(x^2 + y^2, 0)`. -/
theorem fromTangentSpace_problem_8_11_radius_squared_x_field (p : Plane) :
    fromTangentSpace p (problem_8_11_radius_squared_x_field p) = (p.1 ^ 2 + p.2 ^ 2, 0) := by
  simp [problem_8_11_radius_squared_x_field]

/-- Problem 8-11 (1): in polar coordinates, the field
`X = x ∂/∂x + y ∂/∂y`, i.e. the plane specialization of `euler_vector_field`, has coordinate
representation `r ∂/∂r`, encoded by the coordinate vector `(r, 0)`. -/
theorem problem_8_11_radial_dilation_field_polar_coordinates (q : Plane) :
    fromTangentSpace (polarCoord.symm q)
        (euler_vector_field (polarCoord.symm q)) =
      fderivPolarCoordSymm q (q.1, 0) := sorry

/-- Problem 8-11 (2): in polar coordinates, the field
`Y = x ∂/∂y - y ∂/∂x` has coordinate representation `∂/∂θ`, encoded by the coordinate vector
`(0, 1)`. -/
theorem problem_8_11_rotation_field_polar_coordinates (q : Plane) :
    fromTangentSpace (polarCoord.symm q)
        (example_8_17_rotation_field (polarCoord.symm q)) =
      fderivPolarCoordSymm q (0, 1) := sorry

/-- Problem 8-11 (3): in polar coordinates, the field
`Z = (x^2 + y^2) ∂/∂x` has coordinate representation
`r^2 cos θ ∂/∂r - r sin θ ∂/∂θ`, encoded by the coordinate vector
`(r^2 cos θ, -r sin θ)`. -/
theorem problem_8_11_radius_squared_x_field_polar_coordinates (q : Plane) :
    fromTangentSpace (polarCoord.symm q)
        (problem_8_11_radius_squared_x_field (polarCoord.symm q)) =
      fderivPolarCoordSymm q (q.1 ^ 2 * Real.cos q.2, -q.1 * Real.sin q.2) := sorry
