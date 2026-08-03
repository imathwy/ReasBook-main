module

public import Topology_Munkres_2000.Book.Definition_41_2

public section

universe u

/- Definition 41.4. The finite-open-refinement characterization of compactness is
equivalent to the usual finite-subcover characterization. -/
#check compactSpace_iff_exists_finite_open_refinement

namespace IsRefinement

/-- Definition 41.4. A finite refinement covering a set yields a finite
subcollection of the original collection covering the same set. -/
theorem exists_finite_subcover {X : Type u} {𝒜 ℬ : Set (Set X)} {Y : Set X}
    (h_refinement : IsRefinement ℬ 𝒜) (h_finite : ℬ.Finite) (h_cover : ℬ.covers Y) :
    ∃ 𝒞 : Set (Set X), 𝒞 ⊆ 𝒜 ∧ 𝒞.Finite ∧ 𝒞.covers Y := by
  classical
  letI : Fintype ℬ := h_finite.fintype
  -- Choose an original collection member containing each refinement member.
  choose parent hparent_mem hparent_subset using
    fun B : ℬ ↦ h_refinement.subset_of_mem B.property
  have h_range_cover : (Set.range parent).covers Y := by
    -- Transfer every covered point through its refinement member's inclusion.
    rw [Set.covers_iff]
    intro y hy
    obtain ⟨B, hB, hyB⟩ := Set.covers_iff.mp h_cover y hy
    let B' : ℬ := ⟨B, hB⟩
    refine ⟨parent B', Set.mem_range_self B', ?_⟩
    exact hparent_subset B' hyB
  -- The selector's range is finite and lies in the original collection.
  refine ⟨Set.range parent, ?_, Set.finite_range parent, h_range_cover⟩
  intro A hA
  obtain ⟨B, rfl⟩ := hA
  exact hparent_mem B

end IsRefinement
