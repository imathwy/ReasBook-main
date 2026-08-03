module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Group.BallSphere

public section

/-- The closed unit disk `B²` in the Euclidean plane. -/
abbrev ClosedUnitDisk :=
  Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1

/-- Standard notation for the closed unit disk in the Euclidean plane. -/
notation "B²" => ClosedUnitDisk

namespace ClosedUnitDisk

/-- A point of the closed unit disk lies on its boundary circle when its norm is one. -/
def IsBoundary (x : ClosedUnitDisk) : Prop :=
  ‖(x : EuclideanSpace ℝ (Fin 2))‖ = 1

/-- Negation preserves the boundary circle of the closed unit disk. -/
@[simp]
theorem isBoundary_neg (x : ClosedUnitDisk) : IsBoundary (-x) ↔ IsBoundary x := by
  change ‖((-x : ClosedUnitDisk) : EuclideanSpace ℝ (Fin 2))‖ = 1 ↔
    ‖(x : EuclideanSpace ℝ (Fin 2))‖ = 1
  simp

end ClosedUnitDisk

end
