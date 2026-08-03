module

public import Topology_Munkres_2000.Book.Definition_53_1.Slices
public import Mathlib.Topology.Connected.Basic

public section

universe u v

namespace IsSlicePartition

/-- Two slice partitions over a preconnected set are equal. -/
theorem eq_of_isPreconnected {E : Type u} {B : Type v} [TopologicalSpace E]
    [TopologicalSpace B] {p : E → B} {U : Set B} {P Q : Partition (p ⁻¹' U)}
    (hU : IsPreconnected U) (hP : IsSlicePartition p U P) (hQ : IsSlicePartition p U Q) :
    P = Q := by
  have refines : ∀ (R S : Partition (p ⁻¹' U)),
      IsSlicePartition p U R → IsSlicePartition p U S → R ≤ S := by
    intro R S hR hS V hVR
    obtain ⟨x, hxV⟩ := R.nonempty_of_mem hVR
    obtain ⟨W, hWS, hxW⟩ := S.mem_iff_exists.mp (R.subset_of_mem hVR hxV)
    refine ⟨W, hWS, ?_⟩
    -- Transport preconnectedness from `U` to the slice `V` through its homeomorphism.
    have hV : IsPreconnected V := by
      let f := Set.MapsTo.restrict p V U fun _ hy ↦ R.le_of_mem hVR hy
      have hf : IsHomeomorph f := hR.isHomeomorph hVR
      letI : PreconnectedSpace U := Subtype.preconnectedSpace hU
      rw [isPreconnected_iff_preconnectedSpace]
      exact hf.homeomorph f |>.symm.surjective.denseRange.preconnectedSpace
        (hf.homeomorph f).symm.continuous
    let otherSlices := ⋃₀ ((S : Set (Set E)) \ {W})
    have hOtherOpen : IsOpen otherSlices := by
      exact isOpen_sUnion fun Z hZ ↦ hS.isOpen hZ.1
    have hDisjoint : Disjoint W otherSlices := by
      rw [Set.disjoint_left]
      intro y hyW hyOther
      obtain ⟨Z, ⟨hZS, hZW⟩, hyZ⟩ := hyOther
      exact hZW (Set.mem_singleton_iff.mpr (S.eq_of_mem_of_mem hZS hWS hyZ hyW))
    have hCover : V ⊆ W ∪ otherSlices := by
      intro y hyV
      obtain ⟨Z, hZS, hyZ⟩ := S.mem_iff_exists.mp (R.subset_of_mem hVR hyV)
      by_cases hZW : Z = W
      · exact Or.inl (hZW ▸ hyZ)
      · exact Or.inr ⟨Z, ⟨hZS, Set.mem_singleton_iff.not.mpr hZW⟩, hyZ⟩
    -- The slice meets `W`, so preconnectedness rules out all the other slices.
    exact hV.subset_left_of_subset_union (hS.isOpen hWS) hOtherOpen hDisjoint hCover
      ⟨x, hxV, hxW⟩
  exact le_antisymm (refines P Q hP hQ) (refines Q P hQ hP)

end IsSlicePartition
