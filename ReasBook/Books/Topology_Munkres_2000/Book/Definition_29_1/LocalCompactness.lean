module

public import Mathlib.Topology.Defs.Filter

public section

open Set Filter Topology

universe u

/-- A point is weakly locally compact if it has some compact neighborhood. -/
def IsWeaklyLocallyCompactAt {X : Type u} [TopologicalSpace X] (x : X) : Prop :=
  ∃ K : Set X, IsCompact K ∧ K ∈ 𝓝 x

/-- A point is weakly locally compact exactly when it has some compact neighborhood. -/
theorem isWeaklyLocallyCompactAt_iff {X : Type u} [TopologicalSpace X] {x : X} :
    IsWeaklyLocallyCompactAt x ↔ ∃ K : Set X, IsCompact K ∧ K ∈ 𝓝 x :=
  Iff.rfl

/-- Every point of a weakly locally compact space is weakly locally compact. -/
theorem WeaklyLocallyCompactSpace.isWeaklyLocallyCompactAt {X : Type u}
    [TopologicalSpace X] [WeaklyLocallyCompactSpace X] (x : X) :
    IsWeaklyLocallyCompactAt x :=
  exists_compact_mem_nhds x

/-- A space is weakly locally compact exactly when every point has some compact neighborhood. -/
theorem weaklyLocallyCompactSpace_iff {X : Type u} [TopologicalSpace X] :
    WeaklyLocallyCompactSpace X ↔ ∀ x : X, IsWeaklyLocallyCompactAt x := by
  constructor
  · intro h x
    exact h.exists_compact_mem_nhds x
  · intro h
    exact ⟨h⟩
