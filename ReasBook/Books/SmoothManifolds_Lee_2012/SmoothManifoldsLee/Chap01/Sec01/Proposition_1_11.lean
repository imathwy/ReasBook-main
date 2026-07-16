import Mathlib
import Mathlib.Tactic.Recall
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap01.Sec01.Definition_1_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

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
