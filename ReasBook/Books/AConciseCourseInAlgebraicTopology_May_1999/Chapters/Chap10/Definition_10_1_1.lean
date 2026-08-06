import Mathlib.Analysis.Normed.Module.RCLike.Real
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.SphereDiskModel

-- Declarations for this item will be appended below by the statement pipeline.

local notation "V[" n "]" => EuclideanSpace ℝ (Fin (n + 1))

-- Semantic recall: `Metric.closedBall`/`Metric.sphere` in `EuclideanSpace` match the source, and
-- `frontier_closedBall'` is the canonical boundary theorem for this model. The underlying disk and
-- sphere owners live in `Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.SphereDiskModel` because Chapter 9 already uses
-- the same standard model.

/-- Definition 10.1.1: the boundary of `unitDisk n` is the unit sphere `S^n`, realized here as
`sphereBoundary n`. -/
theorem frontier_unitDisk (n : ℕ) :
    frontier (unitDisk n) = sphereBoundary n := by
  simpa [unitDisk, sphereBoundary] using (frontier_closedBall' (0 : V[n]) 1)

/-- The sphere model `S^n` is exactly the frontier of `unitDisk n`. -/
theorem sphereBoundary_eq_frontier (n : ℕ) :
    sphereBoundary n = frontier (unitDisk n) :=
  (frontier_unitDisk n).symm
