module

public import Mathlib.Analysis.InnerProductSpace.PiL2

public section

/-- The standard unit `n`-sphere in `ℝⁿ⁺¹`. -/
abbrev StandardSphere (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- The standard closed unit ball in `ℝⁿ⁺¹`. -/
abbrev ClosedUnitBall (n : ℕ) :=
  Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

namespace StandardSphere

/-- The unit sphere viewed as the boundary subset of the closed unit ball. -/
def boundary (n : ℕ) : Set (ClosedUnitBall n) :=
  {x | ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1}

/-- Membership in the boundary of the closed unit ball is the unit-norm equation. -/
theorem mem_boundary_iff_norm_eq (n : ℕ) (x : ClosedUnitBall n) :
    x ∈ boundary n ↔ ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by
  -- Membership in the defining set-builder is exactly its norm predicate.
  rfl

end StandardSphere
