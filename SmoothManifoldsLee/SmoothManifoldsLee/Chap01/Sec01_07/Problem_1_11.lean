import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import SmoothManifoldsLee.Chap02.Sec02_12.Problem_2_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

noncomputable section

-- Semantic search tooling was unavailable in this environment; this file reuses the explicit
-- closed-ball atlas and smooth structure already constructed later in the project in Problem 2-4,
-- together with mathlib's standard manifold interior/boundary API.

section

local notation "ClosedUnitBall" n =>
  Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1

local notation "OpenUnitBall" n =>
  Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1

local notation "UnitSphere" n =>
  Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1

/-- Problem 1-11 (1): the closed unit ball in `ℝ^n` carries a topological manifold-with-boundary
structure. -/
noncomputable instance closed_unit_ball_topologicalManifoldWithBoundary (n : ℕ) :
    TopologicalManifoldWithBoundary n (ClosedUnitBall n) := by
  cases n with
  | zero =>
      exact closed_unit_ball_zero_topologicalManifoldWithBoundary
  | succ m =>
      cases m with
      | zero =>
          exact closed_unit_ball_one_smoothManifoldWithBoundary.toTopologicalManifoldWithBoundary
      | succ k =>
          let h := closed_unit_ball_higher_dimensional_smoothManifoldWithBoundary k
          exact h.toTopologicalManifoldWithBoundary

/-- Problem 1-11 (2): every point of the boundary sphere `S^{n-1}` of the closed unit ball is a
boundary point for the manifold-with-boundary structure on the closed unit ball. -/
theorem closed_unit_ball_isBoundaryPoint_of_mem_sphere {n : ℕ} {x : ClosedUnitBall n}
    (hx : ((x : ClosedUnitBall n) : EuclideanSpace ℝ (Fin n)) ∈ UnitSphere n) :
    (leeBoundaryModelWithCorners n).IsBoundaryPoint x := sorry

/-- Problem 1-11 (3): every point of the open unit ball `B^n` is an interior point for the
manifold-with-boundary structure on the closed unit ball. -/
theorem closed_unit_ball_isInteriorPoint_of_mem_ball {n : ℕ} {x : ClosedUnitBall n}
    (hx : ((x : ClosedUnitBall n) : EuclideanSpace ℝ (Fin n)) ∈ OpenUnitBall n) :
    (leeBoundaryModelWithCorners n).IsInteriorPoint x := sorry

/-- Problem 1-11 (4): the closed unit ball in `ℝ^n` carries the explicit smooth
manifold-with-boundary structure built from Lee's stereographic-boundary charts. -/
noncomputable instance closed_unit_ball_smoothManifoldWithBoundary (n : ℕ) :
    SmoothManifoldWithBoundary n (ClosedUnitBall n) := by
  cases n with
  | zero =>
      exact closed_unit_ball_zero_smoothManifoldWithBoundary
  | succ m =>
      cases m with
      | zero =>
          exact closed_unit_ball_one_smoothManifoldWithBoundary
      | succ k =>
          exact closed_unit_ball_higher_dimensional_smoothManifoldWithBoundary k

/-- Problem 1-11 (5): for the chosen smooth structure on the closed unit ball, the subtype
inclusion into `ℝ^n` is smooth. This is the source-facing bridge formalizing that smooth interior
charts agree with the standard smooth structure on the open unit ball. -/
theorem closed_unit_ball_subtype_val_contMDiff (n : ℕ) :
    ContMDiff (leeBoundaryModelWithCorners n) (𝓡 n) ∞
      (Subtype.val :
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 →
          EuclideanSpace ℝ (Fin n)) := sorry

end
