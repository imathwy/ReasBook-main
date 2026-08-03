module

public import Topology_Munkres_2000.Book.Theorem_50_2
public import Mathlib.Topology.Homeomorph.Lemmas

public section

open scoped CoveringDimension

universe u v

/-- Helper for Corollary 50.3: a covering-dimension bound is preserved by a
homeomorphism. -/
private lemma hasCoveringDimensionLE_homeomorph
    {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) {n : ℕ} (h : HasCoveringDimensionLE A n) :
    HasCoveringDimensionLE B n := by
  -- Pull the target cover back to `A`, where the given bound supplies a refinement.
  rw [hasCoveringDimensionLE_iff_pointwise] at h ⊢
  intro 𝒰 h𝒰open h𝒰cover
  let 𝒰' : Set (Set A) := (fun U : Set B ↦ e ⁻¹' U) '' 𝒰
  have h𝒰'open : ∀ U ∈ 𝒰', IsOpen U := by
    rintro U ⟨V, hV, rfl⟩
    exact (h𝒰open V hV).preimage e.continuous
  have h𝒰'cover : ⋃₀ 𝒰' = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : e x ∈ ⋃₀ 𝒰 := h𝒰cover.symm ▸ Set.mem_univ (e x)
    rw [Set.mem_sUnion] at hx ⊢
    obtain ⟨V, hV, hxV⟩ := hx
    exact ⟨e ⁻¹' V, ⟨V, hV, rfl⟩, hxV⟩
  obtain ⟨𝒱, h𝒱refines, h𝒱cover, h𝒱order⟩ := h 𝒰' h𝒰'open h𝒰'cover
  let 𝒱' : Set (Set B) := (fun U : Set A ↦ e '' U) '' 𝒱
  refine ⟨𝒱', ?_, ?_, ?_⟩
  · -- Push the refinement forward; images of pulled-back parents lie in the parents.
    rw [isOpenRefinement_iff, isRefinement_iff]
    constructor
    · rintro V ⟨U, hU, rfl⟩
      obtain ⟨W, hW, hUW⟩ := h𝒱refines.subset_of_mem hU
      obtain ⟨Z, hZ, rfl⟩ := hW
      refine ⟨Z, hZ, ?_⟩
      rintro y ⟨x, hxU, rfl⟩
      exact hUW hxU
    · rintro V ⟨U, hU, rfl⟩
      exact e.isOpen_image.mpr (h𝒱refines.isOpen_of_mem hU)
  · -- Surjectivity transports the fact that the refinement covers the space.
    apply Set.eq_univ_of_forall
    intro y
    have hy : e.symm y ∈ ⋃₀ 𝒱 := h𝒱cover.symm ▸ Set.mem_univ (e.symm y)
    rw [Set.mem_sUnion] at hy ⊢
    obtain ⟨U, hU, hyU⟩ := hy
    exact ⟨e '' U, ⟨U, hU, rfl⟩, ⟨e.symm y, hyU, e.apply_symm_apply y⟩⟩
  · -- The members through a point correspond injectively under set image.
    intro y
    let incident : Set (Set A) := {U ∈ 𝒱 | e.symm y ∈ U}
    have hincident : {V ∈ 𝒱' | y ∈ V} = (fun U : Set A ↦ e '' U) '' incident := by
      ext V
      constructor
      · rintro ⟨⟨U, hU, rfl⟩, hyU⟩
        obtain ⟨x, hxU, hxy⟩ := hyU
        have hx : x = e.symm y := by
          simpa using congrArg e.symm hxy
        exact ⟨U, ⟨hU, hx ▸ hxU⟩, rfl⟩
      · rintro ⟨U, ⟨hU, hyU⟩, rfl⟩
        exact ⟨⟨U, hU, rfl⟩, ⟨e.symm y, hyU, e.apply_symm_apply y⟩⟩
    rw [hincident, e.injective.image_injective.encard_image]
    exact h𝒱order (e.symm y)

/-- Helper for Corollary 50.3: a strict covering-dimension bound is preserved
by a homeomorphism. -/
private lemma hasCoveringDimensionLT_homeomorph
    {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) {n : ℕ} (h : HasCoveringDimensionLT A n) :
    HasCoveringDimensionLT B n := by
  -- Separate the empty-space endpoint from the successor bounds.
  cases n with
  | zero =>
      constructor
      intro y
      exact h.false (e.symm y)
  | succ n =>
      exact hasCoveringDimensionLE_homeomorph e h

/-- Helper for Corollary 50.3: covering dimension is invariant under a
homeomorphism. -/
private lemma coveringDimension_homeomorph
    {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) : dim A = dim B := by
  -- Transport every strict bound in both directions, so the defining sets coincide.
  unfold coveringDimension
  apply congrArg sInf
  ext d
  constructor
  · intro hd n hdn
    exact hasCoveringDimensionLT_homeomorph e (hd n hdn)
  · intro hd n hdn
    exact hasCoveringDimensionLT_homeomorph e.symm (hd n hdn)

/-- Helper for Corollary 50.3: the copy of `A` inside a containing subtype `B`
has the same covering dimension as `A`. -/
private lemma coveringDimension_nestedSubtype
    {X : Type u} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) :
    dim ((Subtype.val : B → X) ⁻¹' A) = dim A := by
  -- Realize the nested subtype as the range of the canonical inclusion of `A` into `B`.
  let P : Set B := (Subtype.val : B → X) ⁻¹' A
  let inc : A → B := Set.inclusion hAB
  let f : A → P := fun a ↦ ⟨inc a, a.2⟩
  have hinc : Topology.IsEmbedding inc := Topology.IsEmbedding.inclusion hAB
  have hf : Topology.IsEmbedding f := hinc.codRestrict P fun a ↦ a.2
  have hfsurjective : Function.Surjective f := by
    intro p
    refine ⟨⟨p.1.1, p.2⟩, ?_⟩
    apply Subtype.ext
    exact Set.inclusion_right hAB p.1 p.2
  exact (coveringDimension_homeomorph (hf.toHomeomorphOfSurjective hfsurjective)).symm

/-- Helper for Corollary 50.3: the covering dimension of the union of two
closed subsets is the maximum of their covering dimensions. -/
private lemma coveringDimension_closedUnion
    {X : Type u} [TopologicalSpace X] {S T : Set X}
    (hS : IsClosed S) (hT : IsClosed T) :
    dim (S ∪ T : Set X) = max (dim S) (dim T) := by
  -- Apply Theorem 50.2 inside the union subtype and hide its nested-subtype pieces.
  let U : Set X := S ∪ T
  let S' : Set U := (Subtype.val : U → X) ⁻¹' S
  let T' : Set U := (Subtype.val : U → X) ⁻¹' T
  have hS' : IsClosed S' := hS.preimage continuous_subtype_val
  have hT' : IsClosed T' := hT.preimage continuous_subtype_val
  have hcover : S' ∪ T' = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    rcases x.2 with hxS | hxT
    · exact Or.inl hxS
    · exact Or.inr hxT
  have hSsub : S ⊆ U := Set.subset_union_left
  have hTsub : T ⊆ U := Set.subset_union_right
  calc
    dim (S ∪ T : Set X) = dim U := rfl
    _ = max (dim S') (dim T') := coveringDimension_union_closed hS' hT' hcover
    _ = max (dim S) (dim T) := congrArg₂ max
      (coveringDimension_nestedSubtype hSsub)
      (coveringDimension_nestedSubtype hTsub)

/-- Helper for Corollary 50.3: covering dimension turns a finite union of
closed subsets into the finite supremum of their dimensions. -/
private lemma coveringDimension_finset_iUnion_closed
    {X : Type u} [TopologicalSpace X] {I : Type v}
    (Y : I → Set X) (s : Finset I) (hclosed : ∀ i ∈ s, IsClosed (Y i)) :
    dim (⋃ i ∈ s, Y i) = s.sup fun i ↦ dim (Y i) := by
  classical
  -- Induct on the finite family, using the binary closed-union interface at each insertion.
  revert hclosed
  refine Finset.induction_on s ?_ ?_
  · intro _
    have hEmptyUnion : (⋃ i ∈ (∅ : Finset I), Y i) = (∅ : Set X) := by
      ext x
      simp
    have hempty : IsEmpty (∅ : Set X) := inferInstance
    rw [hEmptyUnion, Finset.sup_empty]
    exact (coveringDimension_eq_bot_iff (∅ : Set X)).mpr hempty
  · intro a t hat ih hclosed
    have hYa : IsClosed (Y a) := hclosed a (Finset.mem_insert_self a t)
    have htClosed : IsClosed (⋃ i ∈ t, Y i) := by
      apply isClosed_biUnion_finset
      intro i hi
      exact hclosed i (Finset.mem_insert_of_mem hi)
    have htDimension : dim (⋃ i ∈ t, Y i) = t.sup fun i ↦ dim (Y i) := by
      apply ih
      intro i hi
      exact hclosed i (Finset.mem_insert_of_mem hi)
    calc
      dim (⋃ i ∈ insert a t, Y i) = dim (Y a ∪ ⋃ i ∈ t, Y i : Set X) := by
        rw [Finset.set_biUnion_insert]
      _ = max (dim (Y a)) (dim (⋃ i ∈ t, Y i)) :=
        coveringDimension_closedUnion hYa htClosed
      _ = max (dim (Y a)) (t.sup fun i ↦ dim (Y i)) := congrArg (max (dim (Y a))) htDimension
      _ = (insert a t).sup fun i ↦ dim (Y i) := by
        rw [Finset.sup_insert]

/-- Corollary 50.3. The covering dimension of a finite closed cover is the
maximum of the covering dimensions of its members. -/
theorem coveringDimension_iUnion_closed
    {X : Type u} [TopologicalSpace X] {ι : Type v} [Fintype ι]
    (Y : ι → Set X) (hclosed : ∀ i, IsClosed (Y i))
    (hcover : (⋃ i, Y i) = Set.univ) :
    dim X = Finset.univ.sup fun i ↦ dim (Y i) := by
  -- Identify `X` with its universal subtype, then apply the finite-union formula.
  have hfiniteCover : (⋃ i ∈ (Finset.univ : Finset ι), Y i) = Set.univ := by
    simpa using hcover
  calc
    dim X = dim (Set.univ : Set X) :=
      (coveringDimension_homeomorph (Homeomorph.Set.univ X)).symm
    _ = dim (⋃ i ∈ (Finset.univ : Finset ι), Y i) :=
      congrArg (fun S : Set X ↦ dim S) hfiniteCover.symm
    _ = Finset.univ.sup fun i ↦ dim (Y i) :=
      coveringDimension_finset_iUnion_closed Y Finset.univ fun i _ ↦ hclosed i
