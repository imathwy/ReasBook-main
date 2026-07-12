import Mathlib
import StacksProject_2024.Chap06.Extension_by_zero_by_the_initial_object
import StacksProject_2024.Chap06.Lemma_6_21_5
import StacksProject_2024.Chap06.Definition_6_31_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopCat TopologicalSpace
open CategoryTheory.Limits
open TopologicalSpace.Opens

noncomputable section

universe w u

namespace OpenSubsetExtensionByInitial

section

variable {X : TopCat.{w}}
variable {C : Type u} [Category.{w} C] [HasInitial C] [HasColimits C]

/- Domain-style sampling for Lemma 6.31.7:
- primary domain: extension by the initial object along the open immersion `j : U ↪ X`, viewed as
  the left adjoint to restriction / pullback on presheaves and sheaves;
- sampled owner declarations:
  `openSubsetPresheafExtensionByInitialObject`,
  `openSubsetSheafExtensionByInitialObject`,
  `(U.isOpenEmbedding.functor.op).lanAdjunction`,
  `Functor.sheafPullbackConstruction.sheafAdjunctionContinuous`,
  `IsOpenMap.pullbackIso`,
  `Topology.IsOpenEmbedding.sheafPullbackIso`;
- owner abstraction: the core owners are the restriction functors
  `TopCat.Presheaf.pullback C (extensionByZeroOpenSubsetInclusion U)` and
  `TopCat.Sheaf.pullback C (extensionByZeroOpenSubsetInclusion U)`, together with their canonical
  left-adjoint constructions coming from left Kan extension on presheaves and sheaf pullback
  construction on sheaves;
- primitive data: the open subset `U` and the canonical extension-by-initial functors already
  defined upstream in `Extension_by_zero_by_the_initial_object`;
- derived API: the adjunctions, unit isomorphisms, and stalk descriptions below.

Source/core/bridge triage:
- `source-facing`: the Stacks-project adjunction, unit, and stalk statements for `j_!`;
- `core/canonical`: the owner adjunctions built from `lanAdjunction` and
  `Functor.sheafPullbackConstruction.sheafAdjunctionContinuous`, transported along the canonical
  pullback comparison isomorphisms;
- `bridge/view`: the identifications of the explicit source-facing extension-by-initial functors
  with those owner left adjoints. This file should therefore reuse those owners directly rather
  than keep parallel local wrappers around them. -/

private abbrev openSubsetOpenFunctor (U : Opens X) :
    Opens (extensionByZeroOpenSubsetSpace U) ⥤ Opens X :=
  U.isOpenEmbedding.functor

private noncomputable instance openSubsetOpenFunctor_full (U : Opens X) :
    (openSubsetOpenFunctor U).Full := by
  letI : Mono (extensionByZeroOpenSubsetInclusion U) :=
    (TopCat.mono_iff_injective _).2 Subtype.val_injective
  let h : IsOpenMap (extensionByZeroOpenSubsetInclusion U) := U.isOpenEmbedding.isOpenMap
  change h.functor.Full
  infer_instance

private theorem imageOpen_le_openSubset (U : Opens X)
    (V : Opens (extensionByZeroOpenSubsetSpace U)) :
    (openSubsetOpenFunctor U).obj V ≤ U := by
  intro x hx
  change x ∈ (((openSubsetOpenFunctor U).obj V : Opens X) : Set X) at hx
  change x ∈ (U : Set X)
  simp [openSubsetOpenFunctor, Topology.IsOpenEmbedding.functor, IsOpenMap.functor] at hx ⊢
  rcases hx with ⟨y, hy, rfl⟩
  exact y.2

private theorem preimage_imageOpen_eq (U : Opens X)
    (V : Opens (extensionByZeroOpenSubsetSpace U)) :
    openSubsetPreimageOpen U ((openSubsetOpenFunctor U).obj V) = V := by
  ext x
  simp [openSubsetPreimageOpen, openSubsetOpenFunctor, Topology.IsOpenEmbedding.functor,
    IsOpenMap.functor]

private theorem image_preimageOpen_eq_of_le (U W : Opens X) (h : W ≤ U) :
    (openSubsetOpenFunctor U).obj (openSubsetPreimageOpen U W) = W := by
  ext x
  constructor
  · intro hx
    change x ∈ (((openSubsetOpenFunctor U).obj (openSubsetPreimageOpen U W) : Opens X) : Set X) at hx
    simp [openSubsetOpenFunctor, openSubsetPreimageOpen, Topology.IsOpenEmbedding.functor,
      IsOpenMap.functor] at hx
    rcases hx with ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    change x ∈ (((openSubsetOpenFunctor U).obj (openSubsetPreimageOpen U W) : Opens X) : Set X)
    refine ⟨⟨x, h hx⟩, ?_, rfl⟩
    simpa [openSubsetPreimageOpen]

private noncomputable def openSubsetPresheafExtensionByInitialObjectIsoLanApp
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C) (W : (Opens X)ᵒᵖ) :
    ((jₚ! U).obj ℱ).obj W ≅
      (((openSubsetOpenFunctor U).op).lan.obj ℱ).obj W := by
  let L := (openSubsetOpenFunctor U).op
  by_cases hW : unop W ≤ U
  · letI : L.Full := by
      dsimp [L]
      infer_instance
    letI : L.Faithful := by
      dsimp [L]
      infer_instance
    letI : L.HasPointwiseLeftKanExtension ℱ := by
      intro Y
      infer_instance
    letI : ∀ F : (Opens (extensionByZeroOpenSubsetSpace U))ᵒᵖ ⥤ C, L.HasLeftKanExtension F := by
      intro F
      infer_instance
    let X0 := op (openSubsetPreimageOpen U (unop W))
    let eUnit : ℱ.obj X0 ≅ (L ⋙ L.lan.obj ℱ).obj X0 := by
      haveI : IsIso ((L.leftKanExtensionUnit ℱ).app X0) := by
        exact
          (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit L ℱ (L.obj X0)).isIso_hom_app
      simpa [Functor.lan] using asIso ((L.leftKanExtensionUnit ℱ).app X0)
    exact
      eqToIso (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hW) ≪≫
        eUnit ≪≫
        eqToIso (by
          simpa [L, X0, image_preimageOpen_eq_of_le U (unop W) hW] using
            congrArg op (image_preimageOpen_eq_of_le U (unop W) hW))
  · have hEmpty : IsEmpty (CostructuredArrow L W) := by
      refine ⟨fun j ↦ ?_⟩
      let f := j.hom.unop
      have hj : unop W ≤ (openSubsetOpenFunctor U).obj (unop j.left) := by
        exact f.le
      exact hW (le_trans hj (imageOpen_le_openSubset U (unop j.left)))
    let hInit : IsInitial (colimit (CostructuredArrow.proj L W ⋙ ℱ)) := by
      exact (isColimitEquivIsInitialOfIsEmpty C
        (colimit.cocone (CostructuredArrow.proj L W ⋙ ℱ))).1
        (colimit.isColimit (CostructuredArrow.proj L W ⋙ ℱ))
    exact
      eqToIso (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_not_le U ℱ hW) ≪≫
        initialIsoIsInitial hInit ≪≫
        (L.leftKanExtensionObjIsoColimit ℱ W).symm

-- Proof sketch: for an open immersion, the explicit extension-by-initial-object presheaf functor
-- agrees with the canonical left Kan extension along the induced functor on opens.
/-- The explicit presheaf extension-by-initial-object functor agrees with the owner left Kan
extension along the inclusion of opens. -/
private noncomputable def openSubsetPresheafExtensionByInitialObjectIsoLan
    (U : Opens X) :
    jₚ! U ≅
      (((openSubsetOpenFunctor U).op).lan :
        (extensionByZeroOpenSubsetSpace U).Presheaf C ⥤ X.Presheaf C) := by
  refine NatIso.ofComponents
    (fun ℱ ↦ NatIso.ofComponents
      (openSubsetPresheafExtensionByInitialObjectIsoLanApp U ℱ)
      (by
        intro V W i
        sorry))
    (by
      intro ℱ 𝒢 η
      ext W : 2
      sorry)

/-- Lemma 6.31.7 (1): extension by the initial object on presheaves is left adjoint to
restriction to the open subset `U`. -/
noncomputable abbrev presheafExtensionByInitialAdjunction (U : Opens X) :
    jₚ! U ⊣
      TopCat.Presheaf.pullback C (extensionByZeroOpenSubsetInclusion U) :=
  ((((openSubsetOpenFunctor U).op).lanAdjunction C).ofNatIsoRight
      (IsOpenMap.pullbackIso U.isOpenEmbedding.isOpenMap).symm).ofNatIsoLeft
    (openSubsetPresheafExtensionByInitialObjectIsoLan U).symm

-- Proof sketch: this is the standard fact that the unit of a fully faithful left adjoint along
-- an open immersion is invertible, transported through the canonical adjunction above.
/-- The unit of the presheaf extension-by-initial adjunction is an isomorphism on every presheaf
over `U`. -/
theorem presheafExtensionByInitialAdjunction_unit_app_isIso
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C) :
    IsIso ((presheafExtensionByInitialAdjunction U).unit.app ℱ) := sorry

private instance presheafExtensionByInitial_unit_isIso
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C) :
    IsIso ((presheafExtensionByInitialAdjunction U).unit.app ℱ) :=
  presheafExtensionByInitialAdjunction_unit_app_isIso U ℱ

/-- Lemma 6.31.7 (4): on presheaves over `U`, the unit
`\mathrm{id} \to j_p j_{p!}` is a natural isomorphism. -/
noncomputable abbrev presheafExtensionByInitialUnitIso (U : Opens X) :
    𝟭 ((extensionByZeroOpenSubsetSpace U).Presheaf C) ≅
      jₚ! U ⋙
        TopCat.Presheaf.pullback C (extensionByZeroOpenSubsetInclusion U) :=
  NatIso.ofComponents
    (fun ℱ ↦ asIso ((presheafExtensionByInitialAdjunction U).unit.app ℱ))
    (by
      intro ℱ 𝒢 f
      simpa using (presheafExtensionByInitialAdjunction U).unit.naturality f)

-- Proof sketch: `presheafExtensionByInitialUnitIso` is defined by applying `asIso` to each
-- component of the adjunction unit, so its hom component is exactly that unit map.
/-- The hom component of the presheaf unit isomorphism is the unit morphism of the adjunction. -/
theorem presheafExtensionByInitialUnitIso_hom_app
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C) :
    (presheafExtensionByInitialUnitIso U).hom.app ℱ =
      (presheafExtensionByInitialAdjunction U).unit.app ℱ := sorry

section Sheaf

variable {FC : C → C → Type w} {CC : C → Type w}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{w} C FC]
variable [HasLimits C] [PreservesLimits (CategoryTheory.forget C)]
variable [PreservesFilteredColimits (CategoryTheory.forget C)]
variable [(CategoryTheory.forget C).ReflectsIsomorphisms]
variable [HasWeakSheafify (Opens.grothendieckTopology X) C]

-- Proof sketch: sheafifying the presheaf extension-by-initial-object construction gives the same
-- left adjoint as the canonical sheaf pullback construction attached to the open inclusion.
/-- The explicit sheaf extension-by-initial-object functor agrees with the owner sheaf-pullback
construction for the inclusion of opens. -/
private noncomputable def openSubsetSheafExtensionByInitialObjectIsoSheafPullback
    (U : Opens X) :
    j! U ≅
      Functor.sheafPullbackConstruction.sheafPullback
        U.isOpenEmbedding.functor C
        (Opens.grothendieckTopology (extensionByZeroOpenSubsetSpace U))
        (Opens.grothendieckTopology X) := by
  simpa [openSubsetSheafExtensionByInitialObject,
    Functor.sheafPullbackConstruction.sheafPullback] using
    Functor.isoWhiskerLeft (TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U))
      (Functor.isoWhiskerRight (openSubsetPresheafExtensionByInitialObjectIsoLan U)
        (CategoryTheory.presheafToSheaf (Opens.grothendieckTopology X) C))

/-- Lemma 6.31.7 (2): extension by the initial object on sheaves is left adjoint to restriction
to the open subset `U`. -/
noncomputable abbrev sheafExtensionByInitialAdjunction (U : Opens X) :
    j! U ⊣
      TopCat.Sheaf.pullback C (extensionByZeroOpenSubsetInclusion U) := by
  letI := Topology.IsOpenEmbedding.functor_isContinuous U.isOpenEmbedding
  exact
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        U.isOpenEmbedding.functor C
        (Opens.grothendieckTopology (extensionByZeroOpenSubsetSpace U))
        (Opens.grothendieckTopology X)).ofNatIsoRight
      (Topology.IsOpenEmbedding.sheafPullbackIso C U.isOpenEmbedding).symm).ofNatIsoLeft
      (openSubsetSheafExtensionByInitialObjectIsoSheafPullback U).symm

-- Proof sketch: the sheaf adjunction is obtained from the canonical sheaf-pullback adjunction,
-- whose unit is invertible on the essential image determined by the open immersion.
/-- The unit of the sheaf extension-by-initial adjunction is an isomorphism on every sheaf over
`U`. -/
theorem sheafExtensionByInitialAdjunction_unit_app_isIso
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Sheaf C) :
    IsIso ((sheafExtensionByInitialAdjunction U).unit.app ℱ) := sorry

private instance sheafExtensionByInitial_unit_isIso
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Sheaf C) :
    IsIso ((sheafExtensionByInitialAdjunction U).unit.app ℱ) :=
  sheafExtensionByInitialAdjunction_unit_app_isIso U ℱ

/-- Lemma 6.31.7 (5): on sheaves over `U`, the unit
`\mathrm{id} \to j^{-1} j_!` is a natural isomorphism. -/
noncomputable abbrev sheafExtensionByInitialUnitIso (U : Opens X) :
    𝟭 ((extensionByZeroOpenSubsetSpace U).Sheaf C) ≅
      j! U ⋙
        TopCat.Sheaf.pullback C (extensionByZeroOpenSubsetInclusion U) :=
  NatIso.ofComponents
    (fun ℱ ↦ asIso ((sheafExtensionByInitialAdjunction U).unit.app ℱ))
    (by
      intro ℱ 𝒢 f
      simpa using (sheafExtensionByInitialAdjunction U).unit.naturality f)

-- Proof sketch: `sheafExtensionByInitialUnitIso` is assembled from the adjunction unit by
-- applying `asIso` componentwise, so its hom component is the unit map.
/-- The hom component of the sheaf unit isomorphism is the unit morphism of the adjunction. -/
theorem sheafExtensionByInitialUnitIso_hom_app
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Sheaf C) :
    (sheafExtensionByInitialUnitIso U).hom.app ℱ =
      (sheafExtensionByInitialAdjunction U).unit.app ℱ := sorry

section Stalks

private noncomputable def outsideNeighbourhoodDiagramIsoConstInitial
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C) {x : X}
    (hx : x ∉ (U : Set X)) :
    (OpenNhds.inclusion x).op ⋙ ((jₚ! U).obj ℱ) ≅
      (Functor.const (OpenNhds x)ᵒᵖ).obj (⊥_ C) :=
  NatIso.ofComponents
    (fun V ↦
      eqToIso (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_not_le U ℱ
        (show ¬ unop (op (unop V).1) ≤ U from by
          intro h
          exact hx (h (unop V).2))))
    (by
      intro V W i
      sorry)

private noncomputable def openSubsetPresheafExtensionByInitialObject_stalk_isInitial_of_not_mem
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C) {x : X}
    (hx : x ∉ (U : Set X)) :
    IsInitial (((jₚ! U).obj ℱ).stalk x) := by
  refine IsInitial.ofIso initialIsInitial ?_
  exact (CategoryTheory.Limits.colimitConstInitial).symm ≪≫
    (HasColimit.isoOfNatIso (outsideNeighbourhoodDiagramIsoConstInitial U ℱ hx)).symm

-- Proof sketch: outside `U`, every sufficiently small neighbourhood still misses `U`, so the
-- extension-by-initial presheaf is constantly the initial object on the filtered diagram defining
-- the stalk.
/-- If `x ∉ U`, then the stalk of `j_! ℱ` at `x` is an initial object of `C`. -/
noncomputable def sheafExtensionByInitial_stalk_isInitial_of_not_mem
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Sheaf C) {x : X}
    (hx : x ∉ (U : Set X)) :
    IsInitial (((j! U).obj ℱ).presheaf.stalk x) := by
  let m := (TopCat.Presheaf.stalkFunctor C x).map
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      ((jₚ! U).obj ℱ.1))
  have hm : IsIso m := by
    simpa [m] using
      (TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x C
        ((jₚ! U).obj ℱ.1))
  change IsInitial
    (TopCat.Presheaf.stalk
      (CategoryTheory.sheafify (Opens.grothendieckTopology X)
        ((jₚ! U).obj ℱ.1))
      x)
  let e :
      TopCat.Presheaf.stalk ((jₚ! U).obj ℱ.1) x ≅
        TopCat.Presheaf.stalk
          (CategoryTheory.sheafify (Opens.grothendieckTopology X)
            ((jₚ! U).obj ℱ.1))
          x := by
    exact @CategoryTheory.asIso _ _ _ _ m hm
  exact IsInitial.ofIso
    (openSubsetPresheafExtensionByInitialObject_stalk_isInitial_of_not_mem U ℱ.1 hx)
    e

-- Proof sketch: the unit `ℱ ⟶ j^{-1} j_! ℱ` is an isomorphism, and taking stalks preserves this;
-- for an open inclusion, the stalk of the pullback sheaf is the stalk of `j_! ℱ` at the
-- corresponding point of `X`.
/-- At a point of `U`, the stalk of `j_! ℱ` at the corresponding point of `X` is canonically
isomorphic to the stalk of `ℱ`. -/
private noncomputable def sheafExtensionByInitial_stalkIsoAtPoint
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Sheaf C)
    (x : extensionByZeroOpenSubsetSpace U) :
    (((j! U).obj ℱ).presheaf.stalk
      (extensionByZeroOpenSubsetInclusion U x)) ≅
      ℱ.presheaf.stalk x := by
  let e :
      (((j! U).obj ℱ).presheaf.stalk
        (extensionByZeroOpenSubsetInclusion U x)) ≅
        (((TopCat.Sheaf.pullback C (extensionByZeroOpenSubsetInclusion U)).obj
          ((j! U).obj ℱ)).presheaf.stalk x) :=
    TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U)
      ((j! U).obj ℱ) x
  exact
    e ≪≫
    ((TopCat.Presheaf.stalkFunctor C x).mapIso
      ((TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)).mapIso
        (asIso ((sheafExtensionByInitialAdjunction U).unit.app ℱ)))).symm

open Classical in
/-- Lemma 6.31.7 (3): for a point `x` of `X`, the stalk of `j_! ℱ` is canonically identified
with the stalk of `ℱ` when `x ∈ U`, and with the initial object of `C` when `x ∉ U`. -/
noncomputable def sheafExtensionByInitial_stalkIso
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Sheaf C) (x : X) :
    (((j! U).obj ℱ).presheaf.stalk x) ≅
      if hx : x ∈ (U : Set X) then
        ℱ.presheaf.stalk ⟨x, hx⟩
      else
        ⊥_ C := by
  by_cases hx : x ∈ (U : Set X)
  · simpa [hx] using sheafExtensionByInitial_stalkIsoAtPoint U ℱ ⟨x, hx⟩
  · simpa [hx] using
      (initialIsoIsInitial
        (sheafExtensionByInitial_stalk_isInitial_of_not_mem U ℱ hx)).symm

-- Proof sketch: compose the by-cases isomorphism `sheafExtensionByInitial_stalkIso` with the
-- canonical identification of the inside branch of the `if`, then compare with the explicit stalk
-- isomorphism at the corresponding point of the open subspace.
/-- On the branch `x ∈ U`, the global stalk comparison agrees with the explicit stalk
identification at the corresponding point of the open subspace. -/
theorem sheafExtensionByInitial_stalkIso_comp_eq_of_mem
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Sheaf C)
    (x : X) (hx : x ∈ (U : Set X)) :
    sheafExtensionByInitial_stalkIso U ℱ x ≪≫
        eqToIso (by simp [hx]) =
      sheafExtensionByInitial_stalkIsoAtPoint U ℱ ⟨x, hx⟩ := sorry

-- Proof sketch: compose the by-cases isomorphism `sheafExtensionByInitial_stalkIso` with the
-- canonical identification of the outside branch of the `if`, then compare with the unique
-- isomorphism coming from the initiality of the stalk.
/-- On the branch `x ∉ U`, the global stalk comparison agrees with the canonical isomorphism from
the stalk to the initial object. -/
theorem sheafExtensionByInitial_stalkIso_comp_eq_of_not_mem
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Sheaf C)
    (x : X) (hx : x ∉ (U : Set X)) :
    sheafExtensionByInitial_stalkIso U ℱ x ≪≫
        eqToIso (by simp [hx]) =
      (initialIsoIsInitial
        (sheafExtensionByInitial_stalk_isInitial_of_not_mem U ℱ hx)).symm := sorry

end Stalks
end Sheaf
end

end OpenSubsetExtensionByInitial

section SubobjectRestriction

variable {X : TopCat.{w}}

namespace CategoryTheory.Subobject

private theorem restrict_mono {𝒢 : X.Sheaf AddCommGrpCat.{w}} (H : Subobject 𝒢) (U : Opens X) :
    Mono ((TopCat.Sheaf.pullback AddCommGrpCat.{w} (Opens.inclusion' U)).map H.arrow) := by
  let h :=
    OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction (C := AddCommGrpCat.{w}) U
  let F := TopCat.Sheaf.pullback AddCommGrpCat.{w} (extensionByZeroOpenSubsetInclusion U)
  have hF : PreservesLimitsOfSize.{w, w} F := h.rightAdjoint_preservesLimits
  letI : PreservesLimitsOfSize.{w, w} F := hF
  simpa [F, extensionByZeroOpenSubsetInclusion] using
    (Functor.map_mono F H.arrow : Mono (F.map H.arrow))

/-- Restrict a subsheaf along the inclusion of an open subset. -/
abbrev restrict {𝒢 : X.Sheaf AddCommGrpCat.{w}} (H : Subobject 𝒢) (U : Opens X) :
    Subobject ((TopCat.Sheaf.pullback AddCommGrpCat.{w} (Opens.inclusion' U)).obj 𝒢) := by
  letI := restrict_mono H U
  exact Subobject.mk ((TopCat.Sheaf.pullback AddCommGrpCat.{w} (Opens.inclusion' U)).map H.arrow)

end CategoryTheory.Subobject

end SubobjectRestriction
