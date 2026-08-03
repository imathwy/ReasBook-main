module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.ChartedSpace

public section

universe u

variable (m : ℕ) (X : Type u) [TopologicalSpace X]

/- Definition 8.99.1: A space `X` is locally `m`-Euclidean if every point has a
neighborhood homeomorphic to an open subset of `EuclideanSpace ℝ (Fin m)`. -/
#check ChartedSpace (EuclideanSpace ℝ (Fin m)) X
