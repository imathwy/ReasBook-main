module

public import Mathlib.Topology.Connected.PathConnected

public section

universe u v

open Set

/-- An indexed union of path-connected sets with a common point is path connected. -/
theorem isPathConnected_iUnion {X : Type u} [TopologicalSpace X] {ι : Type v} [Nonempty ι]
    {s : ι → Set X} (h_inter : (⋂ i, s i).Nonempty)
    (h_path : ∀ i, IsPathConnected (s i)) : IsPathConnected (⋃ i, s i) := by
  -- Use the common intersection point as the center of the union.
  obtain ⟨x, hx⟩ := h_inter
  obtain ⟨i⟩ := ‹Nonempty ι›
  refine ⟨x, mem_iUnion.mpr ⟨i, mem_iInter.mp hx i⟩, ?_⟩
  intro y hy
  obtain ⟨j, hyj⟩ := mem_iUnion.mp hy
  -- Join inside the member containing `y`, then enlarge the path's carrier.
  exact ((h_path j).joinedIn x (mem_iInter.mp hx j) y hyj).mono (subset_iUnion s j)
