import Mathlib.Geometry.Manifold.Instances.Real

open scoped Manifold

/-- Example 1.22: the standard smooth structure on `ℝ^n` is the canonical manifold structure
modeled on `EuclideanSpace ℝ (Fin n)`. -/
theorem euclideanSpace_standard_smooth_structure (n : ℕ) :
    IsManifold
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      ⊤
      (EuclideanSpace ℝ (Fin n)) := sorry
