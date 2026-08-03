module

public import Topology_Munkres_2000.Book.Theorem_50_4
public import Topology_Munkres_2000.Book.Theorem_50_6

public section

universe u v

/-- Helper for Corollary 50.9: covering-dimension bounds are preserved by homeomorphisms. -/
private lemma homeomorphPreservesCoveringDimensionBound
    {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) {n : ℕ} (h : HasCoveringDimensionLE A n) :
    HasCoveringDimensionLE B n := by
  -- Pull an arbitrary open cover back to the source space.
  rw [hasCoveringDimensionLE_iff_pointwise] at h ⊢
  intro 𝒜 h𝒜open h𝒜cover
  let 𝒜' : Set (Set A) := (fun U : Set B ↦ e ⁻¹' U) '' 𝒜
  have h𝒜'open : ∀ U ∈ 𝒜', IsOpen U := by
    rintro U ⟨V, hV, rfl⟩
    exact (h𝒜open V hV).preimage e.continuous
  have h𝒜'cover : ⋃₀ 𝒜' = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : e x ∈ ⋃₀ 𝒜 := h𝒜cover.symm ▸ Set.mem_univ (e x)
    rw [Set.mem_sUnion] at hx ⊢
    obtain ⟨V, hV, hxV⟩ := hx
    exact ⟨e ⁻¹' V, ⟨V, hV, rfl⟩, hxV⟩
  obtain ⟨ℬ, hℬrefines, hℬcover, hℬorder⟩ := h 𝒜' h𝒜'open h𝒜'cover
  let ℬ' : Set (Set B) := (fun U : Set A ↦ e '' U) '' ℬ
  refine ⟨ℬ', ?_, ?_, ?_⟩
  · -- Push the source refinement forward to an open refinement of the original cover.
    rw [isOpenRefinement_iff, isRefinement_iff]
    constructor
    · rintro V ⟨U, hU, rfl⟩
      obtain ⟨W, hW, hUW⟩ := hℬrefines.subset_of_mem hU
      obtain ⟨Z, hZ, rfl⟩ := hW
      refine ⟨Z, hZ, ?_⟩
      rintro y ⟨x, hxU, rfl⟩
      exact hUW hxU
    · rintro V ⟨U, hU, rfl⟩
      exact e.isOpen_image.mpr (hℬrefines.isOpen_of_mem hU)
  · -- Surjectivity transports the fact that the refinement covers the whole space.
    apply Set.eq_univ_of_forall
    intro y
    have hy : e.symm y ∈ ⋃₀ ℬ := hℬcover.symm ▸ Set.mem_univ (e.symm y)
    rw [Set.mem_sUnion] at hy ⊢
    obtain ⟨U, hU, hyU⟩ := hy
    exact ⟨e '' U, ⟨U, hU, rfl⟩, ⟨e.symm y, hyU, e.apply_symm_apply y⟩⟩
  · -- The members through a point correspond bijectively under set image.
    intro y
    let S : Set (Set A) := {U ∈ ℬ | e.symm y ∈ U}
    have hmembers : {V ∈ ℬ' | y ∈ V} = (fun U : Set A ↦ e '' U) '' S := by
      ext V
      constructor
      · rintro ⟨⟨U, hU, rfl⟩, hyU⟩
        obtain ⟨x, hxU, hxy⟩ := hyU
        have hx : x = e.symm y := by
          simpa using congrArg e.symm hxy
        exact ⟨U, ⟨hU, hx ▸ hxU⟩, rfl⟩
      · rintro ⟨U, ⟨hU, hyU⟩, rfl⟩
        exact ⟨⟨U, hU, rfl⟩, ⟨e.symm y, hyU, e.apply_symm_apply y⟩⟩
    rw [hmembers, e.injective.image_injective.encard_image]
    exact hℬorder (e.symm y)

/-- A compact space embedded in a finite-dimensional real Euclidean space has
finite covering dimension. -/
theorem finiteCoveringDimension_of_euclideanEmbedding
    {X : Type u} [TopologicalSpace X] [CompactSpace X] {N : ℕ}
    {f : X → EuclideanSpace ℝ (Fin N)} (hf : Topology.IsEmbedding f) :
    FiniteCoveringDimension X := by
  -- Bound the compact range by its Euclidean dimension, then transport the bound to `X`.
  rw [finiteCoveringDimension_iff]
  refine ⟨N, homeomorphPreservesCoveringDimensionBound hf.toHomeomorph.symm ?_⟩
  exact compactSubset_euclideanSpace_hasCoveringDimensionLE (Set.range f)
    (isCompact_range hf.continuous)

/-- A compact metrizable space of finite covering dimension embeds in some
finite-dimensional real Euclidean space. -/
theorem existsEuclideanEmbedding_of_finiteCoveringDimension
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace.MetrizableSpace X] (hdim : FiniteCoveringDimension X) :
    ∃ (N : ℕ) (f : X → EuclideanSpace ℝ (Fin N)), Topology.IsEmbedding f := by
  rw [finiteCoveringDimension_iff] at hdim
  obtain ⟨m, hm⟩ := hdim
  obtain ⟨f, hf⟩ := existsEuclideanEmbedding_of_hasCoveringDimensionLE hm
  exact ⟨2 * m + 1, f, hf⟩

/-- Corollary 50.9. A compact metrizable space embeds in some finite-dimensional real
Euclidean space if and only if it has finite covering dimension. -/
theorem existsEuclideanEmbedding_iff_finiteCoveringDimension
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace.MetrizableSpace X] :
    (∃ (N : ℕ) (f : X → EuclideanSpace ℝ (Fin N)), Topology.IsEmbedding f) ↔
      FiniteCoveringDimension X := by
  constructor
  · rintro ⟨N, f, hf⟩
    exact finiteCoveringDimension_of_euclideanEmbedding hf
  · exact existsEuclideanEmbedding_of_finiteCoveringDimension
