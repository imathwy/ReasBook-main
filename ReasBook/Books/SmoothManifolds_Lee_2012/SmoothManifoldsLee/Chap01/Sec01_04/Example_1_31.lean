import Mathlib.Geometry.Manifold.Instances.Sphere

open scoped Manifold ContDiff

-- Semantic search note: no `lean_leansearch` tool was available in this environment, so the API
-- choice was checked directly against mathlib's sphere `ChartedSpace`/`IsManifold` owners and
-- nearby chapter recall-style manifold files.

variable (n : ℕ)

/- Example 1.31 (Spheres): the unit sphere `𝕊^n ⊆ ℝ^(n+1)` carries its standard smooth
structure, so it is a smooth `n`-manifold. This is a direct use of mathlib's canonical sphere
`IsManifold` instance, specialized to smooth regularity `∞`. -/
#check
  (inferInstance :
    IsManifold (𝓡 n) ∞ (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
