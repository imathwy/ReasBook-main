import Mathlib
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Problem_1_11 (from Chap01/Sec01_07) -/
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

/-! ### Proposition_1_11 (from Chap01/Sec01) -/
universe u

open Set TopologicalSpace

variable {M : Type u} [TopologicalSpace M]

namespace TopologicalManifold

/-- Proposition 1.11 (1): a topological manifold is locally path-connected via its Euclidean
chart model. -/
theorem locPathConnectedSpace (n : ℕ) (M : Type u) [TopologicalSpace M]
    [TopologicalManifold n M] : LocPathConnectedSpace M := by
  let _ : LocPathConnectedSpace (EuclideanSpace ℝ (Fin n)) := inferInstance
  exact ChartedSpace.locPathConnectedSpace (EuclideanSpace ℝ (Fin n)) M

end TopologicalManifold

/- Proposition 1.11 (2): once a topological manifold is viewed through the canonical owner
`LocPathConnectedSpace`, path-connectedness and connectedness agree by the general theorem
`pathConnectedSpace_iff_connectedSpace`. -/
recall pathConnectedSpace_iff_connectedSpace {X : Type u} [TopologicalSpace X]
    [LocPathConnectedSpace X] : PathConnectedSpace X ↔ ConnectedSpace X

/- Proposition 1.11 (3): in a locally path-connected space, path components are exactly connected
components. -/
recall pathComponent_eq_connectedComponent {X : Type u} [TopologicalSpace X]
    [LocPathConnectedSpace X] (x : X) : pathComponent x = connectedComponent x

/- Proposition 1.11 (5): connected components are open in every locally connected space, hence in
every topological manifold. -/
recall isOpen_connectedComponent {X : Type u} [TopologicalSpace X] [LocallyConnectedSpace X]
    (x : X) : IsOpen (connectedComponent x : Set X)

/- Proposition 1.11 (6): the connectedness of each connected component is the canonical general
theorem `isConnected_connectedComponent`; no manifold hypothesis is part of the owner abstraction.
-/
recall isConnected_connectedComponent {X : Type u} [TopologicalSpace X] (x : X) :
    IsConnected (connectedComponent x : Set X)

-- Proof sketch: manifolds are second-countable, and by (a) they are locally connected as well.
-- Hence the quotient by connected components is a discrete second-countable space, so it is
-- countable.
/-- Proposition 1.11 (4): (d) A topological manifold has countably many connected components. -/
theorem countable_connectedComponents_of_topologicalManifold (n : ℕ) [TopologicalManifold n M] :
    Countable (ConnectedComponents M) := by
  letI : LocPathConnectedSpace M := TopologicalManifold.locPathConnectedSpace n M
  letI : LocallyConnectedSpace M := inferInstance
  letI : LindelofSpace M := inferInstance
  letI : DiscreteTopology (ConnectedComponents M) := inferInstance
  letI : LindelofSpace (ConnectedComponents M) :=
    LindelofSpace.of_continuous_surjective ConnectedComponents.continuous_coe
      ConnectedComponents.surjective_coe
  exact countable_of_Lindelof_of_discrete

-- Proof sketch: an open subset of a topological manifold inherits the same Euclidean chart model,
-- and by the previous clause each connected component is open.
/-- Proposition 1.11 (7): the connectedness half is the canonical theorem that a connected
component, viewed as a subtype, is connected. -/
theorem connectedComponent_connectedSpace (x : M) : ConnectedSpace (connectedComponent x) :=
  Subtype.connectedSpace
    (show IsConnected (connectedComponent x : Set M) from isConnected_connectedComponent)

/-- Proposition 1.11 (7): (d) Each connected component of a topological manifold is itself a
connected topological manifold. -/
noncomputable instance connectedComponent_topologicalManifold (n : ℕ) [TopologicalManifold n M]
    (x : M) : TopologicalManifold n (connectedComponent x) := by
  letI : LocPathConnectedSpace M := TopologicalManifold.locPathConnectedSpace n M
  exact Opens.topologicalManifold
    (⟨connectedComponent x, show IsOpen (connectedComponent x : Set M) from
      isOpen_connectedComponent⟩ : Opens M)
