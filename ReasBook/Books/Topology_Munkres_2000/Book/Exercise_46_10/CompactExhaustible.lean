module

public import Mathlib.Topology.Compactness.SigmaCompact

public section

open Set

universe u

/-- A topological space is compactly exhaustible if it has a countable family of compact
subspaces whose interiors cover the space. This is the notion called σ-compact in Munkres. -/
class CompactlyExhaustibleSpace (X : Type u) [TopologicalSpace X] : Prop where
  /-- The space is covered by the interiors of countably many compact subspaces. -/
  exists_compact_interiors_cover :
    ∃ K : ℕ → Set X, (∀ n, IsCompact (K n)) ∧ ⋃ n, interior (K n) = univ

namespace CompactlyExhaustibleSpace

/-- The defining characterization of a compactly exhaustible space. -/
theorem iff_exists_compact_interiors_cover (X : Type u) [TopologicalSpace X] :
    CompactlyExhaustibleSpace X ↔
      ∃ K : ℕ → Set X, (∀ n, IsCompact (K n)) ∧ ⋃ n, interior (K n) = univ :=
  ⟨fun h ↦ h.exists_compact_interiors_cover, fun h ↦ ⟨h⟩⟩

/-- A compactly exhaustible space is σ-compact in mathlib's sense. -/
instance toSigmaCompactSpace (X : Type u) [TopologicalSpace X]
    [CompactlyExhaustibleSpace X] : SigmaCompactSpace X := by
  -- Forgetting the interiors turns the defining family into an ordinary compact cover.
  rcases CompactlyExhaustibleSpace.exists_compact_interiors_cover (X := X) with
    ⟨K, hK_compact, hK_interiors⟩
  rw [SigmaCompactSpace_iff_exists_compact_covering]
  refine ⟨K, hK_compact, eq_univ_of_forall fun x ↦ ?_⟩
  have hx : x ∈ ⋃ n, interior (K n) := by
    rw [hK_interiors]
    exact mem_univ x
  rcases mem_iUnion.mp hx with ⟨n, hxn⟩
  exact mem_iUnion.mpr ⟨n, interior_subset hxn⟩

/-- A compactly exhaustible space is weakly locally compact. -/
instance toWeaklyLocallyCompactSpace (X : Type u)
    [TopologicalSpace X] [CompactlyExhaustibleSpace X] : WeaklyLocallyCompactSpace X := by
  -- A point in one compact member's interior has that compact member as a neighborhood.
  rcases CompactlyExhaustibleSpace.exists_compact_interiors_cover (X := X) with
    ⟨K, hK_compact, hK_interiors⟩
  refine ⟨fun x ↦ ?_⟩
  have hx : x ∈ ⋃ n, interior (K n) := by
    rw [hK_interiors]
    exact mem_univ x
  rcases mem_iUnion.mp hx with ⟨n, hxn⟩
  exact ⟨K n, hK_compact n, mem_interior_iff_mem_nhds.mp hxn⟩

end CompactlyExhaustibleSpace

namespace CompactExhaustion

/-- Helper for Exercise 46.10: the interiors in a compact exhaustion cover the space. -/
theorem iUnion_interior_eq_univ {X : Type u} [TopologicalSpace X]
    (K : CompactExhaustion X) : ⋃ n, interior (K n) = univ := by
  -- Move a point from one exhaustion stage into the interior of the next stage.
  apply eq_univ_of_forall
  intro x
  rcases K.exists_mem x with ⟨n, hxn⟩
  exact mem_iUnion.mpr ⟨n + 1, K.subset_interior_succ n hxn⟩

end CompactExhaustion
