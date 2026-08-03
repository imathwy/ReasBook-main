module

public import Topology_Munkres_2000.Book.Exercise_31_7
public import Topology_Munkres_2000.Book.Exercise_41_7
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.Compactness.LocallyFinite

public section

universe u v w

namespace IsPerfectMap

/-- Helper for Exercise 41.8: finite unions drawn from an open cover have kernel
images that cover the codomain when every fiber is compact. -/
private lemma iUnion_kernImage_finset_eq_univ_of_isCompact_fiber
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {p : X → Y} (hp_compact : ∀ y, IsCompact (p ⁻¹' {y}))
    {I : Type w} (U : I → Set X) (hU_open : ∀ i, IsOpen (U i))
    (hU_cover : ⋃ i, U i = Set.univ) :
    ⋃ J : Finset I, Set.kernImage p (⋃ i ∈ J, U i) = Set.univ := by
  -- Compactness selects, for each fiber, one finite subfamily of the cover.
  rw [Set.eq_univ_iff_forall]
  intro y
  have hfiber_cover : p ⁻¹' {y} ⊆ ⋃ i, U i := by
    rw [hU_cover]
    exact Set.subset_univ _
  obtain ⟨J, hJ⟩ := (hp_compact y).elim_finite_subcover U hU_open hfiber_cover
  -- The selected finite union contains the whole fiber, hence its kernel image contains `y`.
  refine Set.mem_iUnion_of_mem J ?_
  intro x hxy
  exact hJ (Set.mem_singleton_iff.mpr hxy)

/-- Helper for Exercise 41.8: a closed map with compact fibers sends a locally
finite family of closed sets to a locally finite family. -/
lemma _root_.LocallyFinite.image_of_isClosedMap_of_isCompact_fiber
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {I : Type w} {p : X → Y} (hp_closed : IsClosedMap p)
    (hp_compact : ∀ y, IsCompact (p ⁻¹' {y})) {s : I → Set X}
    (hs_finite : LocallyFinite s) (hs_closed : ∀ i, IsClosed (s i)) :
    LocallyFinite (fun i ↦ p '' s i) := by
  intro y
  let active : Set I := {i | (s i ∩ p ⁻¹' {y}).Nonempty}
  have hactive : active.Finite := by
    exact hs_finite.finite_nonempty_inter_compact (hp_compact y)
  let inactive : {i // i ∉ active} → Set X := fun i ↦ s i.1
  have hinactive_finite : LocallyFinite inactive := by
    exact hs_finite.comp_injective Subtype.val_injective
  have hinactive_union_closed : IsClosed (⋃ i, inactive i) := by
    exact hinactive_finite.isClosed_iUnion fun i ↦ hs_closed i.1
  have hinactive_image_closed : IsClosed (p '' ⋃ i, inactive i) := by
    exact hp_closed _ hinactive_union_closed
  -- The complement of all inactive images is a neighborhood of the target point.
  have hy_compl : y ∈ (p '' ⋃ i, inactive i)ᶜ := by
    intro hy_image
    obtain ⟨x, hx_union, hpx⟩ := hy_image
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx_union
    apply i.property
    exact ⟨x, hxi, Set.mem_singleton_iff.mpr hpx⟩
  refine ⟨(p '' ⋃ i, inactive i)ᶜ,
    hinactive_image_closed.isOpen_compl.mem_nhds hy_compl, hactive.subset ?_⟩
  intro i hi
  obtain ⟨z, hz_image, hz_compl⟩ := hi
  obtain ⟨x, hxs, hpx⟩ := hz_image
  by_contra hi_active
  let j : {i // i ∉ active} := ⟨i, hi_active⟩
  apply hz_compl
  refine ⟨x, Set.mem_iUnion_of_mem j hxs, hpx⟩

/-- Helper for Exercise 41.8: pushing forward a refinement of a preimage
family gives a refinement of the original family. -/
lemma _root_.IsRefinement.image_preimage
    {X : Type u} {Y : Type v} {p : X → Y}
    {𝒜 : Set (Set Y)} {𝒝 : Set (Set X)}
    (hℬ : IsRefinement 𝒝 ((fun A ↦ p ⁻¹' A) '' 𝒜)) :
    IsRefinement ((fun B ↦ p '' B) '' 𝒝) 𝒜 := by
  -- Select the original set above a preimage set and push its inclusion forward.
  rw [isRefinement_iff]
  rintro C ⟨B, hB, rfl⟩
  obtain ⟨D, hD, hBD⟩ := hℬ.subset_of_mem hB
  obtain ⟨A, hA, rfl⟩ := hD
  exact ⟨A, hA, (Set.image_mono hBD).trans (Set.image_preimage_subset p A)⟩

/- Exercise 41.8: Perfect maps preserve paracompactness from codomain to domain,
and from a Hausdorff domain to the codomain. -/
mutual

/-- Exercise 41.8 (a): The domain of a perfect map with paracompact codomain is
paracompact. -/
theorem paracompactSpace_domain {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [ParacompactSpace Y] {p : X → Y}
    (hp : IsPerfectMap p) : ParacompactSpace X := by
  -- Refine the codomain cover formed by kernel images of finite source subunions.
  constructor
  intro I A hA_open hA_cover
  classical
  let kernelCover : Finset I → Set Y :=
    fun J ↦ Set.kernImage p (⋃ i ∈ J, A i)
  have hkernel_open : ∀ J, IsOpen (kernelCover J) := by
    intro J
    apply isClosedMap_iff_kernImage.mp hp.isClosedMap
    exact isOpen_biUnion fun i _ ↦ hA_open i
  have hkernel_cover : ⋃ J, kernelCover J = Set.univ := by
    exact iUnion_kernImage_finset_eq_univ_of_isCompact_fiber
      hp.isCompact_fiber A hA_open hA_cover
  obtain ⟨V, hV_open, hV_cover, hV_finite, hV_kernel⟩ :=
    precise_refinement kernelCover hkernel_open hkernel_cover
  let refinement : (Σ J : Finset I, {i // i ∈ J}) → Set X :=
    fun q ↦ p ⁻¹' V q.1 ∩ A q.2.1
  -- Each new set is open, since the perfect map is continuous.
  have hrefinement_open : ∀ q, IsOpen (refinement q) := by
    intro q
    exact (hV_open q.1).preimage hp.toIsProperMap.continuous |>.inter (hA_open q.2.1)
  -- Local finiteness comes from the outer codomain refinement and finite inner indices.
  have hpreimage_finite : LocallyFinite (fun J ↦ p ⁻¹' V J) := by
    exact hV_finite.preimage_continuous hp.toIsProperMap.continuous
  have hrefinement_finite : LocallyFinite refinement := by
    unfold refinement
    refine LocallyFinite.sigma_of_subset
      (t := fun J (i : {i // i ∈ J}) ↦ p ⁻¹' V J ∩ A i.1)
      hpreimage_finite ?_ ?_
    · intro J
      exact locallyFinite_of_finite _
    · intro J i
      exact Set.inter_subset_left
  -- A point lies over some `V J`, and the kernel-image inclusion selects an index in `J`.
  have hrefinement_cover : ⋃ q, refinement q = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    have hpx_cover : p x ∈ ⋃ J, V J := by
      rw [hV_cover]
      exact Set.mem_univ _
    obtain ⟨J, hpxV⟩ := Set.mem_iUnion.mp hpx_cover
    have hx_finite_union : x ∈ ⋃ i ∈ J, A i := hV_kernel J hpxV rfl
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx_finite_union
    obtain ⟨hiJ, hxi⟩ := Set.mem_iUnion.mp hi
    exact Set.mem_iUnion_of_mem ⟨J, ⟨i, hiJ⟩⟩ ⟨hpxV, hxi⟩
  -- Package the Sigma-indexed family as the required refinement of the source cover.
  refine ⟨Σ J : Finset I, {i // i ∈ J}, refinement,
    hrefinement_open, hrefinement_cover, hrefinement_finite, ?_⟩
  intro q
  exact ⟨q.2.1, Set.inter_subset_right⟩

/-- Exercise 41.8 (b): The codomain of a perfect map from a paracompact Hausdorff
space is paracompact. Together with `IsPerfectMap.t2Space`, this says that the
codomain is again paracompact Hausdorff. -/
theorem paracompactSpace_codomain {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [ParacompactSpace X] [T2Space X]
    {p : X → Y} (hp : IsPerfectMap p) : ParacompactSpace Y := by
  -- Regularity descends along the perfect map, allowing the closed-refinement criterion on `Y`.
  letI : T3Space Y := hp.t3Space
  apply ((_root_.openCoverRefinement_tfae Y).out 2 3).mp
  intro 𝒜 h𝒜_open h𝒜_cover
  let preimageCover : Set (Set X) := (fun A ↦ p ⁻¹' A) '' 𝒜
  have hpreimage_open : ∀ U ∈ preimageCover, IsOpen U := by
    rintro U ⟨A, hA, rfl⟩
    exact (h𝒜_open A hA).preimage hp.toIsProperMap.continuous
  have hpreimage_cover : ⋃₀ preimageCover = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    have hpx : p x ∈ ⋃₀ 𝒜 := by
      rw [h𝒜_cover]
      exact Set.mem_univ _
    obtain ⟨A, hA, hpxA⟩ := Set.mem_sUnion.mp hpx
    exact Set.mem_sUnion_of_mem hpxA ⟨A, hA, rfl⟩
  -- Pull back the cover and choose its locally finite closed refinement on `X`.
  have hclosed_refinement :
      ∀ 𝒜 : Set (Set X),
        (∀ U ∈ 𝒜, IsOpen U) → ⋃₀ 𝒜 = Set.univ →
          ∃ 𝒝 : Set (Set X),
            IsClosedRefinement 𝒝 𝒜 ∧ ⋃₀ 𝒝 = Set.univ ∧ 𝒝.LocallyFinite := by
    exact ((_root_.openCoverRefinement_tfae X).out 3 2).mp
      (inferInstance : ParacompactSpace X)
  obtain ⟨𝒝, hℬ_closed, hℬ_cover, hℬ_finite⟩ :=
    hclosed_refinement preimageCover hpreimage_open hpreimage_cover
  let imageCover : Set (Set Y) := (fun B ↦ p '' B) '' 𝒝
  have himage_refines : IsRefinement imageCover 𝒜 := by
    exact hℬ_closed.toIsRefinement.image_preimage
  have himage_closed : ∀ C ∈ imageCover, IsClosed C := by
    rintro C ⟨B, hB, rfl⟩
    exact hp.isClosedMap B (hℬ_closed.isClosed_of_mem hB)
  have himage_cover : ⋃₀ imageCover = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro y
    obtain ⟨x, rfl⟩ := hp.surjective y
    have hx : x ∈ ⋃₀ 𝒝 := by
      rw [hℬ_cover]
      exact Set.mem_univ _
    obtain ⟨B, hB, hxB⟩ := Set.mem_sUnion.mp hx
    have hpxB : p x ∈ p '' B := ⟨x, hxB, rfl⟩
    have himage_mem : p '' B ∈ imageCover := ⟨B, hB, rfl⟩
    exact Set.mem_sUnion_of_mem hpxB himage_mem
  -- Apply the image-local-finiteness helper once on the subtype-indexed family.
  have himage_indexed_finite :
      LocallyFinite (fun B : 𝒝 ↦ p '' (B : Set X)) := by
    exact hℬ_finite.image_of_isClosedMap_of_isCompact_fiber hp.isClosedMap
      hp.isCompact_fiber (fun B ↦ hℬ_closed.isClosed_of_mem B.property)
  have himage_range_eq :
      Set.range (fun B : 𝒝 ↦ p '' (B : Set X)) = imageCover := by
    ext C
    constructor
    · rintro ⟨B, rfl⟩
      exact ⟨B.1, B.2, rfl⟩
    · rintro ⟨B, hB, rfl⟩
      exact ⟨⟨B, hB⟩, rfl⟩
  have himage_finite : imageCover.LocallyFinite := by
    rw [← himage_range_eq]
    exact himage_indexed_finite.on_range
  have himage_closed_refinement : IsClosedRefinement imageCover 𝒜 := by
    rw [isClosedRefinement_iff]
    exact ⟨himage_refines, himage_closed⟩
  -- The pushed-forward family is the required locally finite closed refinement.
  exact ⟨imageCover, himage_closed_refinement, himage_cover, himage_finite⟩

end

/- The Hausdorff conclusion in Exercise 41.8 (b) is `IsPerfectMap.t2Space`. -/
#check t2Space

end IsPerfectMap
