import SmoothManifoldsLee.Chap01.Sec01.Example_1_8
import Mathlib.Geometry.Manifold.Instances.Sphere

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold

/-- Example 1.9: The `n`-torus is the product of `n` copies of the circle. For `n = 2`, this is
the usual torus. -/
abbrev n_torus (n : ℕ) := Fin n → Circle

scoped[Torus] notation "𝕋^{" n:max "}" => n_torus n

open scoped Torus

-- Proof sketch: combine the manifold structure on `Circle` with the finite-product manifold
-- instance, using the product model with corners on `n` copies of `ℝ`.
/-- The finite product of circles carries the canonical structure of a topological manifold,
modeled on the finite product of `n` copies of `ℝ`. -/
theorem n_torus_isTopologicalManifold (n : ℕ) :
    IsManifold (ModelWithCorners.pi fun _ : Fin n ↦ 𝓡 1) 0 (𝕋^{n}) := by
  infer_instance
