module

public import Topology_Munkres_2000.Book.Definition_55_2.Sphere
public import Mathlib.Analysis.Normed.Group.BallSphere
public import Mathlib.Topology.ContinuousMap.Basic

noncomputable section

public section

/-- The punctured Euclidean space `ℝⁿ⁺¹ ∖ {0}`. -/
abbrev PuncturedEuclideanSpace (n : ℕ) :=
  {x : EuclideanSpace ℝ (Fin (n + 1)) // x ≠ 0}

namespace StandardSphere

/-- A point of the standard sphere lies in the closed unit ball. -/
theorem mem_closedUnitBall {n : ℕ} (x : StandardSphere n) :
    (x : EuclideanSpace ℝ (Fin (n + 1))) ∈
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  Metric.sphere_subset_closedBall x.property

/-- A point of the standard sphere is nonzero in the ambient Euclidean space. -/
theorem ne_zero {n : ℕ} (x : StandardSphere n) :
    (x : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0 :=
  Metric.ne_of_mem_sphere x.property one_ne_zero

/-- The canonical inclusion of the standard sphere into the closed unit ball. -/
@[expose]
def toBall (n : ℕ) : C(StandardSphere n, ClosedUnitBall n) :=
  ContinuousMap.inclusion Metric.sphere_subset_closedBall

/-- The sphere-to-ball inclusion preserves the ambient vector. -/
theorem toBall_apply (n : ℕ) (x : StandardSphere n) :
    (toBall n x : EuclideanSpace ℝ (Fin (n + 1))) = x := rfl

/-- The canonical inclusion of the standard sphere into punctured Euclidean space. -/
@[expose]
def toPunctured (n : ℕ) : C(StandardSphere n, PuncturedEuclideanSpace n) :=
  ContinuousMap.inclusion fun _ hx ↦ Metric.ne_of_mem_sphere hx one_ne_zero

/-- The sphere-to-punctured-space inclusion preserves the ambient vector. -/
theorem toPunctured_apply (n : ℕ) (x : StandardSphere n) :
    (toPunctured n x : EuclideanSpace ℝ (Fin (n + 1))) = x := rfl

end StandardSphere
