module

public import Topology_Munkres_2000.Book.Definition_55_2.Sphere

public section

namespace StandardSphere

/-- A vector field on the standard sphere is a continuous ambient Euclidean vector-valued map. -/
abbrev VectorField (n : ℕ) :=
  C(StandardSphere n, EuclideanSpace ℝ (Fin (n + 1)))

namespace VectorField

/-- A sphere vector field is tangent when its value is orthogonal to the radius at every point. -/
def IsTangent {n : ℕ} (v : VectorField n) : Prop :=
  ∀ x : StandardSphere n, inner ℝ (x : EuclideanSpace ℝ (Fin (n + 1))) (v x) = 0

/-- Tangency is pointwise orthogonality to the radius. -/
theorem isTangent_iff {n : ℕ} (v : VectorField n) :
    v.IsTangent ↔
      ∀ x : StandardSphere n, inner ℝ (x : EuclideanSpace ℝ (Fin (n + 1))) (v x) = 0 := Iff.rfl

end VectorField
end StandardSphere
