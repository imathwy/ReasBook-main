module

public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.InnerProductSpace.PiL2

public section

/-- Example 24.3 (1): The straight-line interpolation between two points of the
closed Euclidean unit ball remains in that ball. -/
theorem euclideanUnitBall_lineSegment_mem {n : ℕ}
    {x y : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
    (hy : y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    (1 - t) • x + t • y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  convex_closedBall 0 1 hx hy (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)

/- Example 24.3 (2, 4): The closed Euclidean unit ball, and more generally every
closed Euclidean ball of nonnegative radius, is path connected. -/
#check Metric.isPathConnected_closedBall

/- Example 24.3 (3): Every nonempty open Euclidean ball is path connected. -/
#check Metric.isPathConnected_ball
