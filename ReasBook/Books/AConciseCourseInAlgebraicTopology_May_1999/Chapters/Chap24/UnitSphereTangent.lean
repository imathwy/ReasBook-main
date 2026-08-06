import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.VectorBundle.Basic

open Bundle

noncomputable section

/-- The standard unit `n`-sphere realizing `S^n`. -/
abbrev unitSphere (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- The tangent bundle of the standard unit `n`-sphere. -/
abbrev unitSphereTangentBundle (n : ℕ) :=
  TangentBundle (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) (unitSphere n)
