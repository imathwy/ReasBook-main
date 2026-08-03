module

public import Mathlib.Topology.Compactness.Compact
public import Topology_Munkres_2000.Book.Definition_26_1.Cover
public import Topology_Munkres_2000.Book.Definition_39_4.Refinement

public section

universe u

/-- Helper for Definition 41.2: a compact whole space admits a finite
subcollection from any open cover. -/
private lemma existsFiniteSubcollectionCover {X : Type u} [TopologicalSpace X]
    (𝒜 : Set (Set X)) (hcompact : IsCompact (Set.univ : Set X))
    (hopen : ∀ U ∈ 𝒜, IsOpen U) (hcover : 𝒜.covers Set.univ) :
    ∃ ℬ : Set (Set X), ℬ ⊆ 𝒜 ∧ ℬ.Finite ∧ ℬ.covers Set.univ := by
  -- Express the collection cover as the indexed union expected by compactness.
  have hindexed : Set.univ ⊆ ⋃ U ∈ 𝒜, U := by
    intro x hx
    obtain ⟨U, hU, hxU⟩ := Set.covers_iff.mp hcover x hx
    refine Set.mem_iUnion.2 ⟨U, ?_⟩
    exact Set.mem_iUnion.2 ⟨hU, hxU⟩
  obtain ⟨ℬ, hsub, hfinite, hℬcover⟩ :=
    hcompact.elim_finite_subcover_image (c := fun U : Set X ↦ U) hopen hindexed
  -- Package the finite indexed subcover back in the collection-level API.
  refine ⟨ℬ, hsub, hfinite, Set.covers_iff.mpr ?_⟩
  intro x hx
  obtain ⟨B, hxB⟩ := Set.mem_iUnion.1 (hℬcover hx)
  obtain ⟨hB, hxB⟩ := Set.mem_iUnion.1 hxB
  exact ⟨B, hB, hxB⟩

/-- Helper for Definition 41.2: a subcollection of an open collection is an
open refinement of that collection. -/
private lemma isOpenRefinement_of_subset {X : Type u} [TopologicalSpace X]
    {ℬ 𝒜 : Set (Set X)} (hsub : ℬ ⊆ 𝒜) (hopen : ∀ U ∈ 𝒜, IsOpen U) :
    IsOpenRefinement ℬ 𝒜 := by
  -- Each member refines itself, and openness is inherited from the larger collection.
  rw [isOpenRefinement_iff, isRefinement_iff]
  constructor
  · intro B hB
    exact ⟨B, hsub hB, subset_rfl⟩
  · intro B hB
    exact hopen B (hsub hB)

/-- Helper for Definition 41.2: a finite refinement of an indexed cover yields
a finite subcover of the original indexed family. -/
private lemma existsFiniteSubcoverOfFiniteRefinement {X ι : Type u}
    (U : ι → Set X) (ℬ : Set (Set X)) (hfinite : ℬ.Finite)
    (hrefinement : IsRefinement ℬ (Set.range U)) (hcover : ℬ.covers Set.univ) :
    ∃ t : Finset ι, Set.univ ⊆ ⋃ i ∈ t, U i := by
  classical
  letI : Fintype ℬ := hfinite.fintype
  -- Choose one original cover member containing each refinement member.
  have hexists (B : ℬ) : ∃ i, (B : Set X) ⊆ U i := by
    obtain ⟨A, hA, hBA⟩ := hrefinement.subset_of_mem B.property
    obtain ⟨i, rfl⟩ := hA
    exact ⟨i, hBA⟩
  choose index hindex using hexists
  -- The image of the finite refinement subtype supplies the desired finite indices.
  refine ⟨Finset.univ.image index, ?_⟩
  intro x hx
  obtain ⟨B, hB, hxB⟩ := Set.covers_iff.mp hcover x hx
  have hxU : x ∈ U (index ⟨B, hB⟩) := hindex ⟨B, hB⟩ hxB
  have hmem : index ⟨B, hB⟩ ∈ Finset.univ.image index := by
    exact Finset.mem_image.mpr ⟨⟨B, hB⟩, Finset.mem_univ _, rfl⟩
  refine Set.mem_iUnion.2 ⟨index ⟨B, hB⟩, ?_⟩
  exact Set.mem_iUnion.2 ⟨hmem, hxU⟩

/-- Definition 41.2. A space `X` is compact if and only if every open covering `𝒜`
of `X` has a finite open refinement `ℬ` that covers `X`. -/
theorem compactSpace_iff_exists_finite_open_refinement (X : Type u) [TopologicalSpace X] :
    CompactSpace X ↔
      ∀ 𝒜 : Set (Set X),
        (∀ U ∈ 𝒜, IsOpen U) → 𝒜.covers Set.univ →
          ∃ ℬ : Set (Set X),
            ℬ.Finite ∧ IsOpenRefinement ℬ 𝒜 ∧ ℬ.covers Set.univ := by
  constructor
  · intro hcompact 𝒜 hopen hcover
    letI : CompactSpace X := hcompact
    -- Use compactness to take a finite subcover, which refines the cover by inclusion.
    obtain ⟨ℬ, hsub, hfinite, hℬcover⟩ :=
      existsFiniteSubcollectionCover 𝒜 isCompact_univ hopen hcover
    exact ⟨ℬ, hfinite, isOpenRefinement_of_subset hsub hopen, hℬcover⟩
  · intro hrefinement
    -- Reduce compactness to producing finite subcovers of arbitrary indexed open covers.
    refine ⟨isCompact_of_finite_subcover ?_⟩
    intro ι U hopen hcover
    have hrangeOpen : ∀ V ∈ Set.range U, IsOpen V := by
      intro V hV
      obtain ⟨i, rfl⟩ := hV
      exact hopen i
    have hrangeCover : (Set.range U).covers Set.univ := by
      rw [Set.covers_iff]
      intro x hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 (hcover hx)
      exact ⟨U i, ⟨i, rfl⟩, hxi⟩
    -- Choose finitely many original indices containing the finite refinement members.
    obtain ⟨ℬ, hfinite, hopenRefinement, hℬcover⟩ :=
      hrefinement (Set.range U) hrangeOpen hrangeCover
    exact existsFiniteSubcoverOfFiniteRefinement U ℬ hfinite
      hopenRefinement.toIsRefinement hℬcover
