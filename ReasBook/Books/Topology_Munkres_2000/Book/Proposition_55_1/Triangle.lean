module

public import Mathlib.Analysis.InnerProductSpace.PiL2

public section

/-- The standard closed triangle in the Euclidean plane with vertices `(0, 0)`, `(1, 0)`,
and `(0, 1)`. -/
def standardTriangle : Set (EuclideanSpace ℝ (Fin 2)) :=
  {point | 0 ≤ point 0 ∧ 0 ≤ point 1 ∧ point 0 + point 1 ≤ 1}

/-- Membership in `standardTriangle` is characterized by its three defining inequalities. -/
theorem mem_standardTriangle (point : EuclideanSpace ℝ (Fin 2)) :
    point ∈ standardTriangle ↔
      0 ≤ point 0 ∧ 0 ≤ point 1 ∧ point 0 + point 1 ≤ 1 :=
  Iff.rfl


end
