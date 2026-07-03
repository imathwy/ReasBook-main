import Mathlib.Geometry.Manifold.Instances.Real

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_1_22 (from Chap01/Sec01_04) -/
open scoped Manifold

/-- Example 1.22: the standard smooth structure on `ℝ^n` is the canonical manifold structure
modeled on `EuclideanSpace ℝ (Fin n)`. -/
theorem euclideanSpace_standard_smooth_structure (n : ℕ) :
    IsManifold
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      ⊤
      (EuclideanSpace ℝ (Fin n)) := sorry
