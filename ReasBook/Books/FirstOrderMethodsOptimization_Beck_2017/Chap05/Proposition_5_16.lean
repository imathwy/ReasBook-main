import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-
Proposition 5.16 is `source-facing`: it records the strong-convexity modulus of the concrete
ball-pen function from Example 5.29 on Euclidean `ℝ^n`. In item-per-file mode, the natural owner
abstraction is mathlib's `StrongConvexOn`, so the proposition is stated directly for the real-valued
ball-pen function on the closed Euclidean unit ball rather than through a project-local wrapper.
-/

-- Proof sketch: work on the closed Euclidean unit ball `‖x‖ ≤ 1`, where the source extension is
-- finite-valued and coincides with `x ↦ -√(1 - ‖x‖²)`. Compute the Hessian on the open unit ball
-- and verify that it dominates the identity; then pass to the Jensen-style `StrongConvexOn`
-- inequality on the closed ball by continuity.
/-- Proposition 5.16: the ball-pen function `x ↦ -√(1 - ‖x‖²)` is `1`-strongly convex on the
closed Euclidean unit ball, which is the canonical real-valued formulation of the source statement
that its extension by `∞` outside the ball is `1`-strongly convex. -/
theorem negative_sqrt_one_sub_norm_sq_extension_is_strongly_convex :
    StrongConvexOn
      ({x : E | ‖x‖ ≤ (1 : ℝ)})
      1
      (fun x ↦ -Real.sqrt (1 - ‖x‖ ^ (2 : ℕ))) := sorry

end
