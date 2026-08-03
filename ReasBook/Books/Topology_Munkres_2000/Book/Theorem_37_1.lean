module

public import Topology_Munkres_2000.Book.Exercise_25_10.Quasicomponent
public import Mathlib.Topology.Separation.Regular

public section

open Set

universe u

/-- Theorem 37.1: In a compact Hausdorff space, the quasicomponent of a point is its
connected component. -/
theorem quasicomponent_eq_connectedComponent {X : Type u} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] (x : X) :
    quasicomponent x = connectedComponent x := by
  -- Express both sets through membership in every clopen neighborhood of `x`.
  rw [connectedComponent_eq_iInter_isClopen]
  ext y
  rw [mem_quasicomponent_iff, mem_iInter]
  constructor
  · intro hy s
    exact hy s s.2.1 s.2.2
  · intro hy U hU hx
    exact hy ⟨U, hU, hx⟩

/-- Helper for Theorem 37.1: Two points belong to the same quasicomponent exactly when
they belong to the same connected component. -/
theorem sameQuasicomponent_iff_mem_connectedComponent {X : Type u} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] {x y : X} :
    y ∈ quasicomponent x ↔ y ∈ connectedComponent x := by
  rw [quasicomponent_eq_connectedComponent x]
