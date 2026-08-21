module

public import Mathlib.Geometry.Manifold.Instances.Real

public section

namespace EuclideanQuadrant

/-- The nonnegative orthant in `EuclideanSpace ℝ (Fin n)` is closed. -/
theorem isClosed_nonnegativeOrthant (n : ℕ) :
    IsClosed {x : EuclideanSpace ℝ (Fin n) | ∀ i, 0 ≤ x i} := by
  rw [← range_euclideanQuadrant]
  exact (modelWithCornersEuclideanQuadrant n).isClosed_range

end EuclideanQuadrant
