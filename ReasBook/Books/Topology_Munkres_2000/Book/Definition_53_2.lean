module

public import Topology_Munkres_2000.Book.Definition_53_1
public import Topology_Munkres_2000.Book.Definition_53_2.Covering
import all Topology_Munkres_2000.Book.Definition_53_1
import all Topology_Munkres_2000.Book.Definition_53_1.Slices
import Mathlib.Topology.Homeomorph.Lemmas

public section

universe u v

/- Definition 53.2. Munkres calls a continuous surjection `p : E → B` a covering
map, and `E` a covering space of `B`, when every point of `B` has an evenly covered
neighborhood. -/
#check IsSurjectiveCoveringMap

/-- Helper for Definition 53.2: the canonical map from a partitioned preimage to the base
neighborhood times the discrete set of parts. -/
private def slicePartitionTrivializationMap {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B] {p : E → B} {U : Set B}
    (P : Partition (p ⁻¹' U)) :
    p ⁻¹' U → U × WithDiscreteTopology ↥P :=
  fun x ↦
    (⟨p x, x.2⟩,
      WithTopology.toTopology ⊥ ⟨P.partOf x, P.partOf_mem x.2⟩)

/-- Helper for Definition 53.2: the first coordinate of the canonical partition
trivialization is the original map. -/
private lemma slicePartitionTrivializationMap_apply_fst {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B] {p : E → B} {U : Set B}
    (P : Partition (p ⁻¹' U)) (x : p ⁻¹' U) :
    (slicePartitionTrivializationMap P x).1.1 = p x := by
  -- The computation is exposed separately so later bridges need not unfold the construction.
  rfl

/-- Helper for Definition 53.2: the inverse candidate selects the inverse of the
homeomorphism on the indicated slice. -/
private noncomputable def slicePartitionTrivializationInverse {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B] {p : E → B} {U : Set B}
    {P : Partition (p ⁻¹' U)} (hP : IsSlicePartition p U P) :
    U × WithDiscreteTopology ↥P → p ⁻¹' U :=
  fun z ↦
    let V : ↥P := z.2.ofTopology
    let q := ((hP.isHomeomorph V.2).homeomorph _).symm z.1
    ⟨q, P.le_of_mem V.2 q.2⟩

/-- Helper for Definition 53.2: a partition of a preimage into slices induces a
homeomorphism with the product by its discrete set of parts. -/
private lemma IsSlicePartition.trivializationMap_isHomeomorph {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B] {p : E → B} {U : Set B}
    {P : Partition (p ⁻¹' U)} (hP : IsSlicePartition p U P) :
    IsHomeomorph (slicePartitionTrivializationMap P) := by
  rw [isHomeomorph_iff_exists_inverse]
  constructor
  · -- On each open part, the map is the slice homeomorphism paired with a constant index.
    refine continuous_of_cover_nhds
      (s := fun V : ↥P ↦ ((↑) : p ⁻¹' U → E) ⁻¹' (V : Set E)) ?_ ?_
    · intro x
      let V : ↥P := ⟨P.partOf x, P.partOf_mem x.2⟩
      refine ⟨V, ?_⟩
      exact ((hP.isOpen V.2).preimage continuous_subtype_val).mem_nhds
        (P.mem_partOf x.2)
    · intro V
      rw [continuousOn_iff_continuous_restrict]
      have hToSlice : Continuous
          (fun x : ((↑) : p ⁻¹' U → E) ⁻¹' (V : Set E) ↦
            (⟨x.1.1, x.2⟩ : ↥(V : Set E))) :=
        (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      have hFirst : Continuous
          (fun x : ((↑) : p ⁻¹' U → E) ⁻¹' (V : Set E) ↦
            Set.MapsTo.restrict p V U (fun _ hx ↦ P.le_of_mem V.2 hx)
              ⟨x.1.1, x.2⟩) :=
        (hP.isHomeomorph V.2).continuous.comp hToSlice
      have hLocal : Continuous
          (fun x : ((↑) : p ⁻¹' U → E) ⁻¹' (V : Set E) ↦
            (Set.MapsTo.restrict p V U (fun _ hx ↦ P.le_of_mem V.2 hx)
              ⟨x.1.1, x.2⟩,
              WithTopology.toTopology ⊥ V)) :=
        hFirst.prodMk continuous_const
      refine hLocal.congr ?_
      intro x
      apply Prod.ext
      · apply Subtype.ext
        rfl
      · apply WithTopology.ext
        apply Subtype.ext
        exact P.eq_partOf_of_mem V.2 x.2
  · -- The inverse is continuous on every discrete-index fiber and is inverse on each slice.
    refine ⟨slicePartitionTrivializationInverse hP, ?_, ?_, ?_⟩
    · intro x
      apply Subtype.ext
      let e := (hP.isHomeomorph (P.partOf_mem x.2)).homeomorph _
      let xV : ↥(P.partOf x) := ⟨x, P.mem_partOf x.2⟩
      have hImage : e xV = (⟨p x, x.2⟩ : U) := by
        apply Subtype.ext
        rfl
      have hInverse : e.symm (e xV) = xV := e.symm_apply_apply xV
      calc
        ((slicePartitionTrivializationInverse hP
            (slicePartitionTrivializationMap P x) : p ⁻¹' U) : E) =
            (e.symm (⟨p x, x.2⟩ : U) : E) := by
              rfl
        _ = (e.symm (e xV) : E) :=
          congrArg (fun y : U ↦ (e.symm y : E)) hImage.symm
        _ = x := congrArg (fun q : ↥(P.partOf x) ↦ (q : E)) hInverse
    · intro z
      let V : ↥P := z.2.ofTopology
      let e := (hP.isHomeomorph V.2).homeomorph _
      apply Prod.ext
      · exact e.apply_symm_apply z.1
      · apply WithTopology.ext
        apply Subtype.ext
        exact (P.eq_partOf_of_mem V.2 (e.symm z.1).2).symm
    · rw [continuous_iff_continuousAt]
      intro z
      rw [continuousAt_prod_of_discrete_right]
      let V : ↥P := z.2.ofTopology
      let e := (hP.isHomeomorph V.2).homeomorph _
      have hContinuous : Continuous
          (fun y : U ↦
            (⟨e.symm y, P.le_of_mem V.2 (e.symm y).2⟩ : p ⁻¹' U)) :=
        (continuous_subtype_val.comp e.symm.continuous).subtype_mk _
      simpa only [slicePartitionTrivializationInverse] using hContinuous.continuousAt

namespace EvenlyCovered

/-- Helper for Definition 53.2: a Munkres-style evenly covered neighborhood gives
mathlib's pointwise evenly covered predicate at each of its points. -/
lemma to_isEvenlyCovered {E : Type u} {B : Type v} [TopologicalSpace E]
    [TopologicalSpace B] {p : E → B} {U : Set B} (hU : EvenlyCovered p U)
    {b : B} (hb : b ∈ U) : IsEvenlyCovered p b (p ⁻¹' {b}) := by
  have hUOpen := hU.isOpen
  obtain ⟨P, hP⟩ := hU.exists_slicePartition
  -- The slice partition first supplies a product trivialization with a discrete index.
  have hPreimageOpen : IsOpen (p ⁻¹' U) := by
    rw [← P.sUnion_eq]
    exact isOpen_sUnion fun V hV ↦ hP.isOpen hV
  have hAtU : IsEvenlyCovered p b (WithDiscreteTopology ↥P) := by
    refine ⟨inferInstance, U, hb, hUOpen, hPreimageOpen,
      hP.trivializationMap_isHomeomorph.homeomorph _, ?_⟩
    intro x
    exact slicePartitionTrivializationMap_apply_fst P x
  -- Finally identify the arbitrary discrete index with the canonical fiber over `b`.
  exact hAtU.to_isEvenlyCovered_preimage

end EvenlyCovered

/-- Helper for Definition 53.2: the sheet indexed by `i` is the image in the total space of
the inverse image of `U × {i}` under a product trivialization. -/
private def trivializationSheet {E : Type u} {B : Type v} [TopologicalSpace E]
    [TopologicalSpace B] {p : E → B} {U : Set B} {I : Type*} [TopologicalSpace I]
    (H : p ⁻¹' U ≃ₜ U × I) (i : I) : Set E :=
  ((↑) : p ⁻¹' U → E) '' (H ⁻¹' (Set.univ ×ˢ {i}))

/-- Helper for Definition 53.2: membership in a trivialization sheet is characterized by a
preimage point whose discrete coordinate is the sheet index. -/
private lemma mem_trivializationSheet_iff {E : Type u} {B : Type v} [TopologicalSpace E]
    [TopologicalSpace B] {p : E → B} {U : Set B} {I : Type*} [TopologicalSpace I]
    (H : p ⁻¹' U ≃ₜ U × I) (i : I) (e : E) :
    e ∈ trivializationSheet H i ↔
      ∃ x : p ⁻¹' U, x.1 = e ∧ (H x).2 = i := by
  constructor
  · -- Unpack the image and retain exactly the equality of discrete coordinates.
    rintro ⟨x, hx, hxe⟩
    exact ⟨x, hxe, Set.mem_singleton_iff.mp hx.2⟩
  · -- A point with the prescribed coordinate belongs to the corresponding product slice.
    rintro ⟨x, hxe, hxi⟩
    refine ⟨x, ⟨Set.mem_univ _, Set.mem_singleton_iff.mpr hxi⟩, hxe⟩

/-- Helper for Definition 53.2: every trivialization sheet lies in the preimage of the base
neighborhood. -/
private lemma trivializationSheet_subset {E : Type u} {B : Type v} [TopologicalSpace E]
    [TopologicalSpace B] {p : E → B} {U : Set B} {I : Type*} [TopologicalSpace I]
    (H : p ⁻¹' U ≃ₜ U × I) (i : I) :
    trivializationSheet H i ⊆ p ⁻¹' U := by
  intro e he
  -- The witnessing point already carries membership in the preimage subtype.
  obtain ⟨x, hxe, -⟩ := (mem_trivializationSheet_iff H i e).mp he
  simpa only [← hxe] using x.2

/-- Helper for Definition 53.2: membership in a sheet fixes the second coordinate of the
trivialization independently of the chosen preimage proof. -/
private lemma trivializationSheet_apply_snd {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B] {p : E → B} {U : Set B}
    {I : Type*} [TopologicalSpace I] (H : p ⁻¹' U ≃ₜ U × I) (i : I)
    {e : E} (he : e ∈ trivializationSheet H i) (heU : e ∈ p ⁻¹' U) :
    (H ⟨e, heU⟩).2 = i := by
  obtain ⟨x, hxe, hxi⟩ := (mem_trivializationSheet_iff H i e).mp he
  -- Subtype extensionality removes the irrelevant choice of the preimage proof.
  have hx : x = ⟨e, heU⟩ := Subtype.ext hxe
  exact (congrArg (fun z : p ⁻¹' U ↦ (H z).2) hx).symm.trans hxi

/-- Helper for Definition 53.2: the inverse trivialization over `(y,i)` lands in the sheet
indexed by `i`. -/
private lemma trivialization_symm_mem_sheet {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B] {p : E → B} {U : Set B}
    {I : Type*} [TopologicalSpace I] (H : p ⁻¹' U ≃ₜ U × I)
    (i : I) (y : U) : (H.symm (y, i)).1 ∈ trivializationSheet H i := by
  apply (mem_trivializationSheet_iff H i _).mpr
  -- The homeomorphism inverse gives the required witness and coordinate equation.
  refine ⟨H.symm (y, i), rfl, ?_⟩
  exact congrArg Prod.snd (H.apply_symm_apply (y, i))

/-- Helper for Definition 53.2: the inverse of the restricted projection on one
trivialization sheet. -/
private def trivializationSheetInverse {E : Type u} {B : Type v} [TopologicalSpace E]
    [TopologicalSpace B] {p : E → B} {U : Set B} {I : Type*} [TopologicalSpace I]
    (H : p ⁻¹' U ≃ₜ U × I) (i : I) : U → trivializationSheet H i :=
  fun y ↦ ⟨(H.symm (y, i)).1, trivialization_symm_mem_sheet H i y⟩

/-- Helper for Definition 53.2: distinct sheets in a product trivialization are pairwise
disjoint. -/
private lemma trivializationSheets_pairwiseDisjoint {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B] {p : E → B} {U : Set B}
    {I : Type*} [TopologicalSpace I] (H : p ⁻¹' U ≃ₜ U × I) :
    (Set.range (trivializationSheet H)).PairwiseDisjoint id := by
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
  change Disjoint (trivializationSheet H i) (trivializationSheet H j)
  rw [Set.disjoint_left]
  intro e hei hej
  -- An intersection point forces equal discrete coordinates and hence equal sheets.
  obtain ⟨x, hxe, hxi⟩ := (mem_trivializationSheet_iff H i e).mp hei
  obtain ⟨y, hye, hyj⟩ := (mem_trivializationSheet_iff H j e).mp hej
  have hxy : x = y := Subtype.ext (hxe.trans hye.symm)
  have hIndex : i = j :=
    hxi.symm.trans ((congrArg (fun z : p ⁻¹' U ↦ (H z).2) hxy).trans hyj)
  exact hij (congrArg (trivializationSheet H) hIndex)

/-- Helper for Definition 53.2: the union of all sheets of a product trivialization is the
whole preimage of its base neighborhood. -/
private lemma sUnion_range_trivializationSheet {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B] {p : E → B} {U : Set B}
    {I : Type*} [TopologicalSpace I] (H : p ⁻¹' U ≃ₜ U × I) :
    ⋃₀ Set.range (trivializationSheet H) = p ⁻¹' U := by
  ext e
  constructor
  · -- Every member of a sheet belongs to the preimage subtype used to define it.
    rintro ⟨V, ⟨i, rfl⟩, he⟩
    exact trivializationSheet_subset H i he
  · -- The second coordinate of the trivialization selects a sheet containing the point.
    intro he
    let x : p ⁻¹' U := ⟨e, he⟩
    have hx : e ∈ trivializationSheet H (H x).2 :=
      (mem_trivializationSheet_iff H (H x).2 e).mpr ⟨x, rfl, rfl⟩
    exact ⟨trivializationSheet H (H x).2, ⟨(H x).2, rfl⟩, hx⟩

/-- Helper for Definition 53.2: each sheet of a discrete product trivialization is open in
the total space. -/
private lemma trivializationSheet_isOpen {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B] {p : E → B} {U : Set B}
    {I : Type*} [TopologicalSpace I] [DiscreteTopology I]
    (hPreimageOpen : IsOpen (p ⁻¹' U)) (H : p ⁻¹' U ≃ₜ U × I) (i : I) :
    IsOpen (trivializationSheet H i) := by
  -- Pull back the open product slice and then use the open subtype inclusion.
  have hProductOpen : IsOpen ((Set.univ : Set U) ×ˢ ({i} : Set I)) :=
    isOpen_univ.prod (isOpen_discrete {i})
  have hSubtypeOpen : IsOpen (H ⁻¹' ((Set.univ : Set U) ×ˢ ({i} : Set I))) :=
    H.continuous.isOpen_preimage _ hProductOpen
  exact hPreimageOpen.isOpenMap_subtype_val _ hSubtypeOpen

/-- Helper for Definition 53.2: every sheet of a compatible discrete product
trivialization is a Munkres slice. -/
private lemma trivializationSheet_isSlice {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B] {p : E → B} {U : Set B}
    {I : Type*} [TopologicalSpace I] [DiscreteTopology I]
    (hPreimageOpen : IsOpen (p ⁻¹' U)) (H : p ⁻¹' U ≃ₜ U × I)
    (hH : ∀ x, (H x).1.1 = p x) (i : I) :
    EvenlyCovered.IsSlice p U (trivializationSheet H i) := by
  let hSubset := trivializationSheet_subset H i
  refine ⟨trivializationSheet_isOpen hPreimageOpen H i, hSubset, ?_⟩
  rw [isHomeomorph_iff_exists_inverse]
  constructor
  · -- The restricted projection is the first coordinate of `H` on the sheet.
    have hToPreimage : Continuous
        (fun x : trivializationSheet H i ↦
          (⟨x, hSubset x.2⟩ : p ⁻¹' U)) :=
      continuous_subtype_val.subtype_mk _
    have hViaH : Continuous
        (fun x : trivializationSheet H i ↦
          (H (⟨x, hSubset x.2⟩ : p ⁻¹' U)).1) :=
      continuous_fst.comp (H.continuous.comp hToPreimage)
    refine hViaH.congr ?_
    intro x
    apply Subtype.ext
    exact hH ⟨x, hSubset x.2⟩
  · refine ⟨trivializationSheetInverse H i, ?_, ?_, ?_⟩
    · intro x
      apply Subtype.ext
      let xU : p ⁻¹' U := ⟨x, hSubset x.2⟩
      have hPair : H xU =
          (Set.MapsTo.restrict p (trivializationSheet H i) U hSubset x, i) := by
        apply Prod.ext
        · apply Subtype.ext
          exact hH xU
        · exact trivializationSheet_apply_snd H i x.2 (hSubset x.2)
      have hInverse : H.symm (H xU) = xU := H.symm_apply_apply xU
      calc
        ((trivializationSheetInverse H i
            (Set.MapsTo.restrict p (trivializationSheet H i) U hSubset x) :
              trivializationSheet H i) : E) =
            (H.symm
              (Set.MapsTo.restrict p (trivializationSheet H i) U hSubset x, i) : E) := by
                rfl
        _ = (H.symm (H xU) : E) :=
          congrArg (fun z : U × I ↦ (H.symm z : E)) hPair.symm
        _ = x := congrArg (fun z : p ⁻¹' U ↦ (z : E)) hInverse
    · intro y
      apply Subtype.ext
      let z : U × I := (y, i)
      calc
        p (trivializationSheetInverse H i y) = (H (H.symm z)).1.1 :=
          (hH (H.symm z)).symm
        _ = y := congrArg (fun q : U × I ↦ q.1.1) (H.apply_symm_apply z)
    · have hPair : Continuous (fun y : U ↦ (y, i)) :=
        continuous_id.prodMk continuous_const
      have hUnderlying : Continuous (fun y : U ↦ (H.symm (y, i)).1) :=
        continuous_subtype_val.comp (H.symm.continuous.comp hPair)
      exact hUnderlying.subtype_mk _

namespace IsEvenlyCovered

/-- Helper for Definition 53.2: a mathlib product trivialization determines a Munkres-style
evenly covered neighborhood. -/
lemma exists_evenlyCovered {E : Type u} {B : Type v} [TopologicalSpace E]
    [TopologicalSpace B] {p : E → B} {b : B} {I : Type*} [TopologicalSpace I]
    (h : IsEvenlyCovered p b I) :
    ∃ U : Set B, b ∈ U ∧ EvenlyCovered p U := by
  obtain ⟨hDiscrete, U, hb, hUOpen, hPreimageOpen, H, hH⟩ := h
  letI : DiscreteTopology I := hDiscrete
  let sheets : Set (Set E) := Set.range (trivializationSheet H)
  -- Disjointness and coverage package the trivialization fibers into a partition.
  have hDisjoint : sheets.PairwiseDisjoint id :=
    trivializationSheets_pairwiseDisjoint H
  have hIndependent : sSupIndep sheets := hDisjoint.sSupIndep
  have hUnion : ⋃₀ sheets = p ⁻¹' U := sUnion_range_trivializationSheet H
  have hSupremum : sSup sheets = p ⁻¹' U := by
    simpa only [Set.sSup_eq_sUnion] using hUnion
  let P : Partition (p ⁻¹' U) :=
    Partition.removeBot sheets hIndependent hSupremum
  refine ⟨U, hb, ?_⟩
  unfold EvenlyCovered
  refine ⟨hUOpen, P, ?_⟩
  intro V hVP
  have hVData : V ∈ sheets ∧ V ≠ (⊥ : Set E) := by
    simpa only [P, Partition.mem_removeBot] using hVP
  obtain ⟨i, hi⟩ := hVData.1
  subst V
  -- Each surviving part is one of the open sheets and restricts homeomorphically onto `U`.
  exact trivializationSheet_isSlice hPreimageOpen H hH i

end IsEvenlyCovered

/-- A map is a surjective covering map exactly when it satisfies Munkres's local
description using evenly covered neighborhoods. -/
theorem isSurjectiveCoveringMap_iff_evenlyCovered {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B] (p : E → B) :
    IsSurjectiveCoveringMap p ↔ Continuous p ∧ Function.Surjective p ∧
      ∀ b : B, ∃ U : Set B, b ∈ U ∧ EvenlyCovered p U := by
  rw [isSurjectiveCoveringMap_iff]
  constructor
  · -- Convert mathlib's pointwise trivializations into Munkres slice partitions.
    rintro ⟨hp, hSurjective⟩
    refine ⟨hp.continuous, hSurjective, ?_⟩
    intro b
    exact (hp b).exists_evenlyCovered
  · -- Convert every supplied slice partition back into the canonical fiber trivialization.
    rintro ⟨_, hSurjective, hLocal⟩
    refine ⟨?_, hSurjective⟩
    intro b
    obtain ⟨U, hb, hU⟩ := hLocal b
    exact hU.to_isEvenlyCovered hb
