module

public import Mathlib.Topology.Connected.PathConnected

public section

universe u

/-- A space is path preconnected if every pair of its points can be joined by a path. -/
class PathPreconnectedSpace (X : Type u) [TopologicalSpace X] : Prop where
  /-- Every pair of points can be joined by a path. -/
  joined (x y : X) : Joined x y

/-- A path-connected space is path preconnected. -/
instance PathConnectedSpace.toPathPreconnectedSpace {X : Type u} [TopologicalSpace X]
    [PathConnectedSpace X] : PathPreconnectedSpace X where
  joined := PathConnectedSpace.joined

/-- A path preconnected space is preconnected. -/
instance PathPreconnectedSpace.toPreconnectedSpace {X : Type u} [TopologicalSpace X]
    [PathPreconnectedSpace X] : PreconnectedSpace X := by
  rw [preconnectedSpace_iff_connectedComponent]
  intro x
  exact Set.eq_univ_of_univ_subset fun y _ ↦
    pathComponent_subset_component x (mem_pathComponent_iff.mpr (PathPreconnectedSpace.joined x y))

/-- The defining characterization of a path preconnected space. -/
theorem pathPreconnectedSpace_iff {X : Type u} [TopologicalSpace X] :
    PathPreconnectedSpace X ↔ ∀ x y : X, Joined x y :=
  ⟨fun h ↦ h.joined, fun h ↦ ⟨h⟩⟩

/-- Mathlib's `PathConnectedSpace` is path preconnectedness together with nonemptiness. -/
theorem pathConnectedSpace_iff_nonempty_and_pathPreconnected {X : Type u}
    [TopologicalSpace X] :
    PathConnectedSpace X ↔ Nonempty X ∧ PathPreconnectedSpace X := by
  constructor
  · intro h
    exact ⟨h.nonempty, ⟨h.joined⟩⟩
  · rintro ⟨hX, h⟩
    exact ⟨hX, h.joined⟩
