import Mathlib.Geometry.Manifold.Instances.Sphere
import SmoothManifolds_Lee_2012.Chap01.Sec01.Definition_1_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

/-- Example 1.4: the unit sphere in `ℝ^(n+1)` carries the chapter's canonical source-facing
structure of a topological `n`-manifold. -/
noncomputable instance sphere_topologicalManifold (n : ℕ) :
    TopologicalManifold n (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  topologicalManifoldOfChartedSpace n _
