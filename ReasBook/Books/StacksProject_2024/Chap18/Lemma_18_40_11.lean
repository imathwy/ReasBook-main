import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap07.Lemma_7_44_2
import StacksProject_2024.Chap18.Definition_18_32_1
import StacksProject_2024.Chap18.Definition_18_40_9
import StacksProject_2024.Chap18.Lemma_18_40_8
import StacksProject_2024.Chap18.Lemma_18_40_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

noncomputable section

universe u v

namespace CategoryTheory

/- Domain-style sampling for Lemma 18.40.11:
- primary domain: inverse image for locally ringed sites, with the units construction tracked at
  the source-facing units subsheaf level before passing to the Chapter 18 cartesian-units owner;
- sampled owner declarations:
  `inverseImageStructureSheafForLocallyRingedMorphism`,
  `ringedSiteUnitsSubsheaf`,
  `sheaf_pullback_forget`,
  `unitsSquareCartesianForLocallyRingedMorphism`,
  `pullback_isLocallyRingedSite`;
- best owner abstractions:
  the inverse-image structure sheaf itself should be spoken about through the Chapter 18 owner
  `inverseImageStructureSheafForLocallyRingedMorphism`;
  clause `(1)` is source-facing and should compare the actual inverse-image units sheaf
  `F^{-1}(\mathcal O^*)` with the units subsheaf `(F^{-1}\mathcal O)^*` of the inverse-image
  structure sheaf, using the Chapter 7 forget-compatibility owner `sheaf_pullback_forget` to
  interpret sections of `F^{-1}\mathcal O` as sections of the underlying sheaf of
  `F^{-1}\mathcal O`;
  the Chapter 18 cartesian-units owner
  `inverseImageUnitsCartesianForLocallyRingedMorphism`, specialized to the identity map on
  `F^{-1}\mathcal O`, is only a bridge/view reformulation of that comparison;
  clause `(2)` is already exactly the canonical preservation theorem
  `pullback_isLocallyRingedSite`;
- primitive data:
  the continuous functor `F` presenting the inverse-image functor and the commutative structure
  sheaf `𝒪`;
- derived API:
  the inverse-image comparison between units sheaves, the corresponding cartesian-units
  reformulation for the identity map on `F^{-1}\mathcal O`, and the pullback preservation of
  local ringedness.

Source/core/bridge triage:
- `source-facing`: the claim that inverse image carries the units subsheaf of `𝒪` to the units
  subsheaf of `F^{-1}\mathcal O`, i.e. `F^{-1}(\mathcal O^*) ≅ (F^{-1}\mathcal O)^*`;
- `core/canonical`: `inverseImageStructureSheafForLocallyRingedMorphism`,
  `ringedSiteUnitsSubsheaf`, and
  `pullback_isLocallyRingedSite`;
- `bridge/view`: `sheaf_pullback_forget`, identifying the pullback of the underlying sheaf of
  sets with the underlying sheaf of the pulled-back structure sheaf, and
  `inverseImageUnitsCartesianForLocallyRingedMorphism` for the later locally ringed-morphism
  reformulation.
-/

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (F : C ⥤ D) [Functor.IsContinuous F J K]
variable [((F.sheafPushforwardContinuous CommRingCat.{max u v} J K).IsRightAdjoint)]
variable (𝒪 : Sheaf J CommRingCat.{max u v})

local notation "f⁻¹𝒪" => inverseImageStructureSheafForLocallyRingedMorphism F 𝒪

section UnitsComparison

variable [∀ P : Cᵒᵖ ⥤ CommRingCat.{max u v}, F.op.HasLeftKanExtension P]
variable [(forget CommRingCat.{max u v}).PreservesLeftKanExtensions F.op]

private noncomputable def pullbackInverseImageUnitsUnderlying :
    (F.sheafPullback (Type (max u v)) J K).obj (ringedSiteUnitsSubsheaf 𝒪) ⟶
      (sheafCompose K (forget CommRingCat.{max u v})).obj
        (f⁻¹𝒪 : Sheaf K CommRingCat.{max u v}) :=
  (F.sheafPullback (Type (max u v)) J K).map (ringedSiteUnitsSubsheafι 𝒪) ≫
    (((sheaf_pullback_forget J K F).app 𝒪).inv)

private noncomputable def pullbackInverseImageUnitsApp (U : D) :
    ((F.sheafPullback (Type (max u v)) J K).obj (ringedSiteUnitsSubsheaf 𝒪)).1.obj (op U) →
      (f⁻¹𝒪 : Sheaf K CommRingCat.{max u v}).1.obj (op U) :=
  fun s ↦ (pullbackInverseImageUnitsUnderlying F 𝒪).1.app (op U) s

-- Proof sketch: pull back the inclusion `\mathcal O^* \hookrightarrow \mathcal O` as a morphism
-- of sheaves of sets and transport its target across the canonical Chapter 7 forget/pullback
-- comparison; sections of `F^{-1}(\mathcal O^*)` therefore land in unit sections of
-- `F^{-1}\mathcal O`.
private theorem pullback_inverseImageUnitsApp_isUnit
    (U : D)
    (s : ((F.sheafPullback (Type (max u v)) J K).obj (ringedSiteUnitsSubsheaf 𝒪)).1.obj (op U)) :
    IsUnit (pullbackInverseImageUnitsApp F 𝒪 U s) := by
  sorry

private noncomputable def pullbackInverseImageUnitsComparison (U : D) :
    ((F.sheafPullback (Type (max u v)) J K).obj (ringedSiteUnitsSubsheaf 𝒪)).1.obj (op U) →
      (ringedSiteUnitsSubsheaf (f⁻¹𝒪 : Sheaf K CommRingCat.{max u v})).1.obj (op U) :=
  fun s ↦
    ⟨pullbackInverseImageUnitsApp F 𝒪 U s,
      pullback_inverseImageUnitsApp_isUnit F 𝒪 U s⟩

-- Proof sketch: the objectwise comparison maps above assemble into a morphism of sheaves because
-- their underlying sections are the components of the natural transformation obtained by composing
-- the pulled-back inclusion `F^{-1}(\mathcal O^*) → F^{-1}\mathcal O` with the canonical
-- forget/pullback comparison from Chapter 7.
private noncomputable def pullback_inverseImageUnitsHom :
    (F.sheafPullback (Type (max u v)) J K).obj (ringedSiteUnitsSubsheaf 𝒪) ⟶
      ringedSiteUnitsSubsheaf (f⁻¹𝒪 : Sheaf K CommRingCat.{max u v}) :=
  ⟨
    { app := fun U ↦ pullbackInverseImageUnitsComparison F 𝒪 U.unop
      naturality := by
        intro U V f
        funext s
        apply Subtype.ext
        exact congr_fun ((pullbackInverseImageUnitsUnderlying F 𝒪).hom.naturality f) s }⟩

private theorem pullback_inverseImageUnitsHom_app_bijective (U : D) :
    Function.Bijective
      (((pullback_inverseImageUnitsHom F 𝒪 :
          (F.sheafPullback (Type (max u v)) J K).obj (ringedSiteUnitsSubsheaf 𝒪) ⟶
            ringedSiteUnitsSubsheaf (f⁻¹𝒪 : Sheaf K CommRingCat.{max u v})).hom.app
        (op U))) := by
  sorry

-- Proof sketch: the forgetful functor from sheaves to presheaves reflects isomorphisms, and a
-- natural transformation between `Type`-valued presheaves is an isomorphism exactly when each
-- component is bijective. Apply the previous objectwise bijectivity theorem.
private theorem pullback_inverseImageUnitsHom_isIso :
    IsIso
      (pullback_inverseImageUnitsHom F 𝒪 :
        (F.sheafPullback (Type (max u v)) J K).obj (ringedSiteUnitsSubsheaf 𝒪) ⟶
          ringedSiteUnitsSubsheaf (f⁻¹𝒪 : Sheaf K CommRingCat.{max u v})) := by
  rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf K (Type (max u v))),
    NatTrans.isIso_iff_isIso_app]
  intro U
  rw [isIso_iff_bijective]
  simpa using pullback_inverseImageUnitsHom_app_bijective F 𝒪 U.unop

/-- Lemma 18.40.11 (1), isomorphism form: the actual inverse image of the units subsheaf
`F^{-1}(\mathcal O^*)` is canonically identified with the units subsheaf
`ringedSiteUnitsSubsheaf f⁻¹𝒪` of the inverse-image structure sheaf. -/
noncomputable def pullback_inverseImageUnitsIso :
    (F.sheafPullback (Type (max u v)) J K).obj (ringedSiteUnitsSubsheaf 𝒪) ≅
      ringedSiteUnitsSubsheaf (f⁻¹𝒪 : Sheaf K CommRingCat.{max u v}) := by
  let α :
      (F.sheafPullback (Type (max u v)) J K).obj (ringedSiteUnitsSubsheaf 𝒪) ⟶
        ringedSiteUnitsSubsheaf (f⁻¹𝒪 : Sheaf K CommRingCat.{max u v}) :=
    pullback_inverseImageUnitsHom F 𝒪
  let _ : IsIso α := pullback_inverseImageUnitsHom_isIso F 𝒪
  exact asIso α

end UnitsComparison

attribute [local instance] pullback_isLocallyRingedSite

/-- Companion bridge to the Chapter 18 owner: for the identity map
`f^\sharp : F^{-1}\mathcal O \to F^{-1}\mathcal O`, the inverse-image units square is cartesian. -/
theorem pullback_inverseImageUnitsCartesian :
    inverseImageUnitsCartesianForLocallyRingedMorphism
      F
      (f⁻¹𝒪 : Sheaf K CommRingCat.{max u v})
      𝒪
      (𝟙 _) := by
  intro U
  change
    unitsSquareCartesianForLocallyRingedMorphism
      (RingHom.id ((f⁻¹𝒪 : Sheaf K CommRingCat.{max u v}).1.obj (op U)))
  rw [unitsSquareCartesian_iff_isLocalHom]
  exact isLocalHom_id _

-- Proof sketch: clause `(1)` identifies the inverse image of the units subsheaf with the units
-- subsheaf of the pulled-back structure sheaf, while Lemma `18.40.5` supplies that
-- `F^{-1}\mathcal O` is locally ringed whenever `\mathcal O` is. Thus the site-presented
-- morphism of topoi with `f^\sharp = \mathrm{id}` satisfies the Chapter 18 locally ringed
-- morphism owner.
/-- Lemma 18.40.11 (2): if `(\mathcal C, \mathcal O)` is locally ringed, then the morphism of
topoi induced by `F` together with the identity map
`f^\sharp : F^{-1}\mathcal O \to F^{-1}\mathcal O` is a morphism of locally ringed topoi. -/
theorem pullback_isMorphismOfLocallyRingedTopoi
    [IsLocallyRingedSite 𝒪] :
    IsMorphismOfLocallyRingedTopoi
      F
      (f⁻¹𝒪 : Sheaf K CommRingCat.{max u v})
      𝒪
      (𝟙 _) := by
  exact ⟨pullback_inverseImageUnitsCartesian F 𝒪⟩

end CategoryTheory
