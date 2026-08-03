module

public import Topology_Munkres_2000.Book.Definition_26_2
public import Topology_Munkres_2000.Book.Definition_26_1.Cover

public section

universe u

/-- Lemma 26.1. A subspace `Y` of `X` is compact if and only if every cover of
`Y` by sets open in `X` has a finite subcollection that still covers `Y`. -/
theorem isCompact_iff_finite_ambient_open_subcover {X : Type u} [TopologicalSpace X]
    (Y : Set X) :
    IsCompact Y ↔
      ∀ (𝒜 : Set (Set X)) (h_open : ∀ U ∈ 𝒜, IsOpen U) (h_cover : Set.covers 𝒜 Y),
        ∃ ℬ : Set (Set X), ℬ ⊆ 𝒜 ∧ ℬ.Finite ∧ Set.covers ℬ Y := by
  constructor
  · intro h_compact 𝒜 h_open h_cover
    -- Normalize the collection cover to the indexed-union form used by compactness.
    have h_cover_union : Y ⊆ ⋃ U ∈ 𝒜, U := by
      intro y hy
      obtain ⟨U, hU, hyU⟩ := Set.covers_iff.mp h_cover y hy
      exact Set.mem_iUnion.2 ⟨U, Set.mem_iUnion.2 ⟨hU, hyU⟩⟩
    -- Compactness selects a finite subcollection of the original ambient family.
    obtain ⟨ℬ, h_subset, h_finite, h_finite_cover⟩ :=
      h_compact.elim_finite_subcover_image (c := fun U : Set X ↦ U) h_open h_cover_union
    refine ⟨ℬ, h_subset, h_finite, ?_⟩
    rw [Set.covers_iff]
    intro y hy
    have hy_union := h_finite_cover hy
    simp only [Set.mem_iUnion] at hy_union
    obtain ⟨U, hU, hyU⟩ := hy_union
    exact ⟨U, hU, hyU⟩
  · intro h_subcover
    -- It suffices to produce finite subcovers for arbitrary indexed open families.
    refine isCompact_of_finite_subcover ?_
    intro ι U h_open h_cover
    have h_range_open : ∀ V ∈ Set.range U, IsOpen V := by
      intro V hV
      obtain ⟨i, rfl⟩ := hV
      exact h_open i
    have h_range_cover : Set.covers (Set.range U) Y := by
      rw [Set.covers_iff]
      intro y hy
      have hy_union := h_cover hy
      simp only [Set.mem_iUnion] at hy_union
      obtain ⟨i, hyU⟩ := hy_union
      exact ⟨U i, ⟨i, rfl⟩, hyU⟩
    obtain ⟨ℬ, h_subset, h_finite, h_finite_cover⟩ :=
      h_subcover (Set.range U) h_range_open h_range_cover
    -- Lift the finite family of sets back to a finite collection of indices.
    have h_image_subset : ℬ ⊆ U '' Set.univ := by
      simpa only [Set.image_univ] using h_subset
    obtain ⟨t, _, h_t_finite, h_image⟩ :=
      h_finite.exists_subset_finite_image_eq h_image_subset
    obtain ⟨t', h_t'⟩ := h_t_finite.exists_finset_coe
    have h_t_cover : Set.covers (U '' t) Y := by
      rw [h_image]
      exact h_finite_cover
    refine ⟨t', ?_⟩
    intro y hy
    obtain ⟨V, hV, hyV⟩ := Set.covers_iff.mp h_t_cover y hy
    obtain ⟨i, hit, rfl⟩ := hV
    have hit'_set : i ∈ (t' : Set ι) := by
      rw [h_t']
      exact hit
    have hit' : i ∈ t' := Finset.mem_coe.mp hit'_set
    exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hit', hyV⟩⟩
