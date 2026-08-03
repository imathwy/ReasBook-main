module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.ChartedSpace

public section

namespace Real

/-- The canonical charted-space structure on `ℝ` modeled on one-dimensional Euclidean space. -/
noncomputable instance instChartedSpaceOne :
    ChartedSpace (EuclideanSpace ℝ (Fin 1)) ℝ :=
  (((EuclideanSpace.equiv (Fin 1) ℝ).trans
    (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)).toHomeomorph).chartedSpace

end Real
