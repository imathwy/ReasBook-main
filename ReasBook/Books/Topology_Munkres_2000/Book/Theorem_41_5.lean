module

public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.Compactness.Paracompact
import Topology_Munkres_2000.Book.Lemma_41_3

public section

universe u

/-- Helper for Theorem 41.5: every countable collection of subsets is countably
locally finite. -/
private lemma countableCollection_countablyLocallyFinite
    {X : Type u} [TopologicalSpace X] {𝒜 : Set (Set X)}
    (h𝒜 : 𝒜.Countable) : 𝒜.CountablyLocallyFinite := by
  rw [Set.countablyLocallyFinite_iff]
  by_cases hnonempty : 𝒜.Nonempty
  · obtain ⟨f, hf⟩ := h𝒜.exists_eq_range hnonempty
    -- Enumerate the collection and use singleton, hence locally finite, layers.
    refine ⟨fun n ↦ {f n}, ?_, ?_⟩
    · rw [hf]
      ext A
      simp
    · intro n
      exact locallyFinite_of_finite _
  · have hempty : 𝒜 = ∅ := Set.not_nonempty_iff_eq_empty.mp hnonempty
    -- Represent the empty collection by constantly empty locally finite layers.
    refine ⟨fun _ ↦ ∅, ?_, ?_⟩
    · simp [hempty]
    · intro n
      exact locallyFinite_of_finite _

/-- Helper for Theorem 41.5: an open subcollection is an open refinement of its
containing collection. -/
private lemma isOpenRefinement_of_subset_openCollection
    {X : Type u} [TopologicalSpace X] {ℬ 𝒜 : Set (Set X)}
    (hsubset : ℬ ⊆ 𝒜) (hopen : ∀ U ∈ 𝒜, IsOpen U) :
    IsOpenRefinement ℬ 𝒜 := by
  rw [isOpenRefinement_iff, isRefinement_iff]
  constructor
  · -- Each member refines itself, now regarded as a member of the larger collection.
    intro B hB
    exact ⟨B, hsubset hB, Set.Subset.rfl⟩
  · -- Openness restricts from the containing collection to the subcollection.
    intro B hB
    exact hopen B (hsubset hB)

/-- Helper for Theorem 41.5: every open cover of a Lindelöf space has a countably
locally finite open subcover. -/
private lemma exists_countablyLocallyFinite_openSubcover
    {X : Type u} [TopologicalSpace X] [LindelofSpace X]
    (𝒜 : Set (Set X)) (hopen : ∀ U ∈ 𝒜, IsOpen U)
    (hcover : ⋃₀ 𝒜 = Set.univ) :
    ∃ ℬ : Set (Set X),
      IsOpenRefinement ℬ 𝒜 ∧ ⋃₀ ℬ = Set.univ ∧ ℬ.CountablyLocallyFinite := by
  have hcover_biUnion : (Set.univ : Set X) ⊆ ⋃ U ∈ 𝒜, U := by
    -- Put the collection-form cover into the indexed form used by Lindelöfness.
    rw [← Set.sUnion_eq_biUnion, hcover]
  obtain ⟨ℬ, hℬ_subset, hℬ_countable, hℬ_cover⟩ :=
    isLindelof_univ.elim_countable_subcover_image
      (c := fun U : Set X ↦ U) hopen hcover_biUnion
  have hℬ_cover_eq : ⋃₀ ℬ = Set.univ := by
    -- The selected subcollection covers `univ`, so its union is exactly `univ`.
    apply Set.eq_univ_of_univ_subset
    rwa [Set.sUnion_eq_biUnion]
  -- Package the inherited refinement and the countability invariant.
  exact ⟨ℬ, isOpenRefinement_of_subset_openCollection hℬ_subset hopen,
    hℬ_cover_eq, countableCollection_countablyLocallyFinite hℬ_countable⟩

/-- Theorem 41.5. Every regular Lindelöf space is paracompact. -/
instance paracompact_of_t3_lindelof
    {X : Type u} [TopologicalSpace X] [T3Space X] [LindelofSpace X] :
    ParacompactSpace X := by
  -- The Lindelöf subcover supplies condition 0 of Lemma 41.3, whose implication to
  -- condition 3 is precisely paracompactness.
  exact ((_root_.openCoverRefinement_tfae X).out 0 3).mp
    exists_countablyLocallyFinite_openSubcover
