module

public import Topology_Munkres_2000.Book.Definition_53_1
public import Mathlib.Topology.Homeomorph.Lemmas
import all Topology_Munkres_2000.Book.Definition_53_1
import all Topology_Munkres_2000.Book.Definition_53_1.Slices

public section

universe u v

/-- Helper for Remark 53.1: restricting a homeomorphism between subspaces to the preimage of a
smaller codomain subspace is again a homeomorphism. -/
lemma restrictInterPreimage_isHomeomorph {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} {A : Set X} {B C : Set Y} (hAB : A ⊆ f ⁻¹' B)
    (hf : IsHomeomorph (Set.MapsTo.restrict f A B hAB)) (hCB : C ⊆ B) :
    IsHomeomorph
      (Set.MapsTo.restrict f (A ∩ f ⁻¹' C) C Set.inter_subset_right) := by
  rw [isHomeomorph_iff_isEmbedding_surjective]
  constructor
  · -- Pass through the old domain and codomain, then restrict the resulting embedding to `C`.
    have hIntoC : ∀ x : ↑(A ∩ f ⁻¹' C),
        ((↑) : B → Y) (Set.MapsTo.restrict f A B hAB (Set.inclusion Set.inter_subset_left x)) ∈ C :=
      fun x ↦ x.2.2
    have hEmbedding : Topology.IsEmbedding
        (fun x : ↑(A ∩ f ⁻¹' C) ↦
          ((↑) : B → Y) (Set.MapsTo.restrict f A B hAB
            (Set.inclusion Set.inter_subset_left x))) :=
      Topology.IsEmbedding.subtypeVal.comp
        (hf.isEmbedding.comp (Topology.IsEmbedding.inclusion Set.inter_subset_left))
    have hFunctionEq :
        Set.MapsTo.restrict f (A ∩ f ⁻¹' C) C Set.inter_subset_right =
          Set.codRestrict
            (fun x : ↑(A ∩ f ⁻¹' C) ↦
              ((↑) : B → Y) (Set.MapsTo.restrict f A B hAB
                (Set.inclusion Set.inter_subset_left x))) C hIntoC := by
      funext x
      apply Subtype.ext
      simp only [Set.MapsTo.val_restrict_apply, Set.val_codRestrict_apply]
    rw [hFunctionEq]
    exact hEmbedding.codRestrict C hIntoC
  · -- Lift a point of `C` through the original surjection and retain its preimage membership.
    intro y
    let yB : B := ⟨y, hCB y.2⟩
    obtain ⟨x, hx⟩ := hf.surjective yB
    have hxy : f x = y := congrArg Subtype.val hx
    have hxC : x.1 ∈ f ⁻¹' C := by
      rw [Set.mem_preimage, hxy]
      exact y.2
    have hxInter : x.1 ∈ A ∩ f ⁻¹' C := ⟨x.2, hxC⟩
    refine ⟨⟨x, hxInter⟩, ?_⟩
    exact Subtype.ext hxy

namespace EvenlyCovered

/-- Helper for Remark 53.1: an open subspace whose restricted map is a homeomorphism is a
slice. -/
lemma IsSlice.of_isOpen_isHomeomorph {E : Type u} {B : Type v} [TopologicalSpace E]
    [TopologicalSpace B] {p : E → B} {U : Set B} {V : Set E} (hVOpen : IsOpen V)
    (hVU : V ⊆ p ⁻¹' U) (hp : IsHomeomorph (Set.MapsTo.restrict p V U hVU)) :
    IsSlice p U V :=
  -- Route correction: implementation imports expose the owner definition, so its data can be
  -- assembled directly instead of relying on unavailable public introduction lemmas.
  And.intro hVOpen (Exists.intro hVU hp)

/-- Helper for Remark 53.1: an open set with a partition into slices is evenly covered. -/
lemma of_isOpen_partition {E : Type u} {B : Type v} [TopologicalSpace E]
    [TopologicalSpace B] {p : E → B} {U : Set B} (hUOpen : IsOpen U)
    (P : Partition (p ⁻¹' U)) (hP : ∀ V ∈ P, IsSlice p U V) : EvenlyCovered p U :=
  -- Package the given partition of the preimage together with the openness of the base set.
  And.intro hUOpen (Exists.intro P hP)

/-- Helper for Remark 53.1: intersecting a slice with the preimage of an open subset produces a
slice over that subset. -/
lemma IsSlice.inter_preimage_of_isOpen_isHomeomorph {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B] {p : E → B} {U W : Set B} {V : Set E}
    (hVOpen : IsOpen V) (hVU : V ⊆ p ⁻¹' U)
    (hp : IsHomeomorph (Set.MapsTo.restrict p V U hVU)) (hW : IsOpen W) (hWU : W ⊆ U) :
    IsSlice p W (V ∩ p ⁻¹' W) := by
  apply IsSlice.of_isOpen_isHomeomorph
  · -- Pull `W` back inside `V`, then use that the open subtype `V` maps openly into `E`.
    have hWInU : IsOpen (((↑) : U → B) ⁻¹' W) := hW.preimage continuous_subtype_val
    have hPreimageOpen :
        IsOpen ((Set.MapsTo.restrict p V U hVU) ⁻¹' (((↑) : U → B) ⁻¹' W)) :=
      hp.continuous.isOpen_preimage _ hWInU
    have hImageOpen := hVOpen.isOpenMap_subtype_val _ hPreimageOpen
    have hPreimageEq :
        (Set.MapsTo.restrict p V U hVU) ⁻¹' (((↑) : U → B) ⁻¹' W) =
          ((↑) : V → E) ⁻¹' (p ⁻¹' W) := by
      ext x
      rfl
    rw [hPreimageEq, Subtype.image_preimage_coe] at hImageOpen
    exact hImageOpen
  · -- The preceding generic restriction lemma supplies the homeomorphism component.
    exact restrictInterPreimage_isHomeomorph hVU hp hWU

end EvenlyCovered

namespace Partition

/-- Helper for Remark 53.1: intersecting every part of a set partition with a fixed set preserves
pairwise disjointness. -/
lemma pairwiseDisjoint_image_inter {X : Type u} {S T : Set X} (P : Partition S) :
    ((fun V : Set X ↦ V ∩ T) '' (P : Set (Set X))).PairwiseDisjoint id := by
  -- Distinct intersections arise from distinct original parts, whose disjointness descends.
  rintro _ ⟨V, hVP, rfl⟩ _ ⟨Z, hZP, rfl⟩ hVZ
  have hPartsNe : V ≠ Z := fun h ↦ hVZ (congrArg (fun R : Set X ↦ R ∩ T) h)
  exact (P.pairwiseDisjoint hVP hZP hPartsNe).mono Set.inter_subset_left Set.inter_subset_left

/-- Helper for Remark 53.1: if a set lies in the support of a partition, then the intersections
of all parts with that set have that set as their union. -/
lemma sUnion_image_inter {X : Type u} {S T : Set X} (P : Partition S) (hTS : T ⊆ S) :
    ⋃₀ ((fun V : Set X ↦ V ∩ T) '' (P : Set (Set X))) = T := by
  ext x
  constructor
  · -- Membership in any restricted part immediately gives membership in `T`.
    rintro ⟨R, ⟨V, hVP, rfl⟩, hxR⟩
    exact hxR.2
  · -- The original partition supplies the unique part containing each point of `T`.
    intro hxT
    obtain ⟨V, hVP, hxV⟩ := P.mem_iff_exists.mp (hTS hxT)
    exact ⟨V ∩ T, ⟨V, hVP, rfl⟩, hxV, hxT⟩

end Partition

namespace EvenlyCovered

/-- Remark 53.1. An open subset of an evenly covered set is evenly covered. -/
theorem of_isOpen_subset {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    {p : E → B} {U W : Set B} (hU : EvenlyCovered p U) (hW : IsOpen W) (hWU : W ⊆ U) :
    EvenlyCovered p W := by
  obtain ⟨P, hP⟩ := hU.exists_slicePartition
  let restrictedParts : Set (Set E) :=
    (fun V : Set E ↦ V ∩ p ⁻¹' W) '' (P : Set (Set E))
  -- Disjointness and coverage are inherited from `P`, giving the restricted partition.
  have hDisjoint : restrictedParts.PairwiseDisjoint id :=
    P.pairwiseDisjoint_image_inter
  have hIndependent : sSupIndep restrictedParts := hDisjoint.sSupIndep
  have hPreimageSubset : p ⁻¹' W ⊆ p ⁻¹' U := Set.preimage_mono hWU
  have hUnion : ⋃₀ restrictedParts = p ⁻¹' W :=
    P.sUnion_image_inter hPreimageSubset
  have hSupremum : sSup restrictedParts = p ⁻¹' W := by
    simpa only [Set.sSup_eq_sUnion] using hUnion
  let Q : Partition (p ⁻¹' W) :=
    Partition.removeBot restrictedParts hIndependent hSupremum
  apply of_isOpen_partition hW Q
  -- Every nonempty restricted part comes from a slice of `P` and is a slice over `W`.
  intro R hRQ
  have hRRestricted : R ∈ restrictedParts :=
    (Partition.mem_removeBot restrictedParts hIndependent hSupremum).mp hRQ |>.1
  obtain ⟨V, hVP, rfl⟩ := hRRestricted
  exact IsSlice.inter_preimage_of_isOpen_isHomeomorph (hP.isOpen hVP)
    (P.le_of_mem hVP) (hP.isHomeomorph hVP) hW hWU

end EvenlyCovered

end
