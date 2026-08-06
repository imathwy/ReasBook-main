import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
import Mathlib.Topology.Compactness.LocallyCompact
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Definition_5_1_10
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Remark_5_1_5

universe u

variable {X : Type u} [TopologicalSpace X]

-- Semantic search hits: `CompactlyGeneratedSpace`, `UCompactlyGeneratedSpace`,
-- `instCompactlyGeneratedSpaceOfWeaklyLocallyCompactSpace`; the source-facing owner here is the
-- chapter's stronger weak-Hausdorff `k`-space notion, so we keep only that main instance.

/-- Example 5.1.11. Every locally compact weak Hausdorff space is compactly generated in the sense
of Definition 5.1.10. -/
instance instCompactlyGeneratedWeakHausdorffSpaceOfLocallyCompact
    [LocallyCompactSpace X] [hwh : WeaklyHausdorffSpace.{u, u} X] :
    CompactlyGeneratedWeakHausdorffSpace.{u, u} X where
  toWeaklyHausdorffSpace := hwh
  toUCompactlyGeneratedSpace := by
    refine uCompactlyGeneratedSpace_of_isClosed fun s hs ↦ ?_
    refine closure_eq_iff_isClosed.mp ?_
    ext x
    constructor
    · intro hx
      rcases exists_compact_subset isOpen_univ (by simp : x ∈ (Set.univ : Set X)) with
          ⟨K, hK, hxK, _⟩
      let xK : K := ⟨x, interior_subset hxK⟩
      let _ : WeaklyHausdorffSpace K := Subtype.weaklyHausdorffSpace
      let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
      let _ : T2Space K := CompactSpace.toT2Space_of_weaklyHausdorffSpace K
      let S : CompHaus := CompHaus.of K
      have hKs : IsClosed ((Subtype.val : K → X) ⁻¹' s) := by
        simpa using hs S ⟨Subtype.val, continuous_subtype_val⟩
      have hx' : x ∈ closure (s ∩ K : Set X) := by
        rw [mem_closure_iff_nhds] at hx ⊢
        intro t ht
        have hKmem : K ∈ nhds x := mem_interior_iff_mem_nhds.mp hxK
        simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
          hx (t ∩ K) (Filter.inter_mem ht hKmem)
      have hxK' : xK ∈ closure ((Subtype.val : K → X) ⁻¹' s) := by
        rw [closure_subtype]
        simpa [Set.image_preimage_eq_inter_range, Subtype.range_val, Set.inter_assoc,
          Set.inter_left_comm, Set.inter_comm] using hx'
      have hxKs : xK ∈ (Subtype.val : K → X) ⁻¹' s := by
        simpa [hKs.closure_eq] using hxK'
      exact hxKs
    · intro hx
      exact subset_closure hx
