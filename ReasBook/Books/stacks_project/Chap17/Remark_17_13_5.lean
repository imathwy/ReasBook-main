import Mathlib
import stacks_project.Chap06.ClosedSubsetInclusion
import stacks_project.Chap17.Definition_17_5_1
import stacks_project.Chap06.Restriction_and_extension_by_zero_for_module_valued_sheaves
import stacks_project.Chap06.Definition_6_26_1
import stacks_project.Chap17.Definition_17_13_1
import stacks_project.Chap17.Lemma_17_13_4

open CategoryTheory Opposite TopologicalSpace
open CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-
Domain-style sampling for Remark 17.13.5:
- primary domain: `\mathcal O_X`-modules on a ringed space `X`, sections with support in a closed
  subset `Z ⊆ X`, and the induced functor with values in `\operatorname{Mod}(\mathcal O_X|_Z)`;
- inspected owner declarations:
  `RingedSpace.Modules`,
  `RingedSpace.Hom.pushforward`,
  `TopCat.closedSubsetInclusion`,
  `SheafOfModules.pullback`,
  `SheafOfModules.pushforward`;
- best owner abstraction: the neutral ambient owner layer is the closed-subset module category
  `RingedSpace.closedSubsetModuleCategory X Z` together with the canonical functors
  `RingedSpace.closedSubsetModulePullback X Z` and
  `RingedSpace.closedSubsetModulePushforward X Z`; the source-facing owner is the closed-subset
  kernel model
  `RingedSpace.ClosedSubsetSectionsWithSupport.subsheaf hZ ℱ ⊆ ℱ`, together with the induced
  module sheaf `𝓗[hZ](ℱ)` on the closed subset with restricted structure sheaf
  `\mathcal O_X|_Z`; the adjunction with closed-subset pushforward is the next numbered companion
  item, and the closed-immersion presentation is only a bridge/view obtained by pulling this
  source-facing object back along a closed immersion whose image is `Z`;
- primitive data: a ringed space `X`, a closed subset `Z ⊆ X`, a proof `hZ : IsClosed Z`, and an
  `\mathcal O_X`-module `ℱ`;
- derived API: the kernel-model subsheaf on `X`, the restricted module sheaf on `Z`, the functor
  `𝓗[hZ] = \mathcal H_Z`, and its support/maximality and left-exactness properties.

Source/core/bridge triage:
- `core/canonical`: `RingedSpace.closedSubsetModuleCategory`,
  `RingedSpace.closedSubsetModulePullback`, and `RingedSpace.closedSubsetModulePushforward`;
- `source-facing`: `RingedSpace.ClosedSubsetSectionsWithSupport.subsheaf`,
  `RingedSpace.ClosedSubsetSectionsWithSupport.sheaf`,
  `RingedSpace.ClosedSubsetSectionsWithSupport.functor`;
- `bridge/internal`: `RingedSpace.closedSubsetStructureSheafHom`, the unit of
  `TopCat.Sheaf.pullbackPushforwardAdjunction` for `RingedSpace.closedSubsetInclusion`, together
  with the adjunction recorded as the next numbered item;
- `bridge/view`: the minimal closed-immersion specialization obtained by pulling the support
  subsheaf back along a closed immersion, used only internally to produce the induced
  left-adjoint structure on `i _*`.
-/

namespace RingedSpace

section

variable {X : RingedSpace.{u}} {Z : Set X}

/-- The inclusion of a closed subset into the ambient ringed space. -/
abbrev closedSubsetInclusion (X : RingedSpace.{u}) (Z : Set X) : TopCat.of Z ⟶ X :=
  TopCat.closedSubsetInclusion (X : TopCat) Z

/-- The inverse-image map on opens induced by the closed-subset inclusion is continuous for the
canonical Grothendieck topologies. -/
instance closedSubsetInclusion_opensMap_isContinuous (X : RingedSpace.{u}) (Z : Set X) :
    (Opens.map (closedSubsetInclusion X Z)).IsContinuous
      (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology (TopCat.of Z)) := sorry

/-- The restricted structure sheaf `\mathcal O_X|_Z` on the closed subset `Z`. -/
abbrev closedSubsetRestrictedRingCatSheaf (X : RingedSpace.{u}) (Z : Set X) :
    TopCat.Sheaf RingCat.{u} (TopCat.of Z) :=
  (TopCat.Sheaf.pullback RingCat.{u} (closedSubsetInclusion X Z)).obj X.ringCatSheaf

/-- The category of `\mathcal O_X|_Z`-modules on the closed subset `Z`. -/
abbrev closedSubsetModuleCategory (X : RingedSpace.{u}) (Z : Set X) :=
  SheafOfModules (closedSubsetRestrictedRingCatSheaf X Z)

/-- The canonical structure-sheaf map `\mathcal O_X \to i_* \mathcal O_X|_Z` attached to the
closed-subset inclusion `i : Z ↪ X`. -/
abbrev closedSubsetStructureSheafHom (X : RingedSpace.{u}) (Z : Set X) :
    X.ringCatSheaf ⟶
      (TopCat.Sheaf.pushforward RingCat.{u}
        (closedSubsetInclusion X Z)).obj (closedSubsetRestrictedRingCatSheaf X Z) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u}
    (closedSubsetInclusion X Z)).unit.app X.ringCatSheaf

/-- Restriction of `\mathcal O_X`-modules to the closed subset `Z`. -/
abbrev closedSubsetModulePullback (X : RingedSpace.{u}) (Z : Set X) :
    X.Modules ⥤ closedSubsetModuleCategory X Z :=
  SheafOfModules.pullback (closedSubsetStructureSheafHom X Z)

/-- Pushforward of `\mathcal O_X|_Z`-modules from the closed subset `Z` back to `X`. -/
noncomputable abbrev closedSubsetModulePushforward (X : RingedSpace.{u}) (Z : Set X) :
    closedSubsetModuleCategory X Z ⥤ X.Modules :=
  SheafOfModules.pushforward (closedSubsetStructureSheafHom X Z)

end

namespace ClosedSubsetSectionsWithSupport

section

variable {X : RingedSpace.{u}} {Z : Set X}

section

variable {X : RingedSpace.{u}} {Z : Set X} (hZ : IsClosed Z)

/-- The open complement of a closed subset of a ringed space. -/
private abbrev openComplement : Opens X :=
  ⟨Zᶜ, hZ.isOpen_compl⟩

/-- The structural ring-sheaf morphism attached to the open complement of a closed subset. -/
private abbrev openComplementStructureSheafHom :
    X.ringCatSheaf ⟶
      (TopCat.Sheaf.pushforward RingCat.{u} (openComplement hZ).inclusion').obj
        ((TopCat.Sheaf.pullback RingCat.{u} (openComplement hZ).inclusion').obj X.ringCatSheaf) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u}
    (openComplement hZ).inclusion').unit.app X.ringCatSheaf

/-- Restriction of `\mathcal O_X`-modules to the open complement of a closed subset. -/
private abbrev openComplementRestrictionFunctor :
    X.Modules ⥤
      SheafOfModules
        ((TopCat.Sheaf.pullback RingCat.{u} (openComplement hZ).inclusion').obj X.ringCatSheaf) :=
  moduleSheafRestrictionToOpen (openComplement hZ) X.ringCatSheaf

/-- Pushforward from the open complement back to `X`. -/
private abbrev openComplementPushforwardFunctor :
    SheafOfModules
        ((TopCat.Sheaf.pullback RingCat.{u} (openComplement hZ).inclusion').obj X.ringCatSheaf) ⥤
      X.Modules :=
  SheafOfModules.pushforward (openComplementStructureSheafHom hZ)

/-- The canonical restriction map from an `\mathcal O_X`-module to the pushforward of its
restriction to the open complement of a closed subset. -/
abbrev openComplementRestriction (ℱ : X.Modules) :
    ℱ ⟶
      (openComplementPushforwardFunctor hZ).obj
        ((openComplementRestrictionFunctor hZ).obj ℱ) :=
  (SheafOfModules.pullbackPushforwardAdjunction (openComplementStructureSheafHom hZ)).unit.app ℱ

/-- The source-facing subsheaf of `\mathcal F` consisting of sections whose support lies in the
closed subset `Z`. -/
def subsheaf (ℱ : X.Modules) : Subobject ℱ :=
  kernelSubobject (openComplementRestriction hZ ℱ)

/-- The sections-with-support subsheaf is the kernel of the canonical restriction map to the open
complement. -/
theorem subsheaf_eq_kernel (ℱ : X.Modules) :
    subsheaf hZ ℱ = kernelSubobject (openComplementRestriction hZ ℱ) :=
  rfl

private abbrev object (ℱ : X.Modules) : X.Modules :=
  ((subsheaf hZ ℱ : Subobject ℱ) : X.Modules)

/-- The sheaf on the closed subset `Z` obtained by restricting the subsheaf of sections of `ℱ`
supported on `Z`. -/
def sheaf (ℱ : X.Modules) : RingedSpace.closedSubsetModuleCategory X Z :=
  (RingedSpace.closedSubsetModulePullback X Z).obj (object hZ ℱ)

-- Proof sketch: this is the naturality of the unit of the adjunction `j^* ⊣ j_*` for the open
-- complement inclusion `j : X \ Z ↪ X`.
/-- Naturality of the restriction map to the open complement of a closed subset. -/
private theorem subsheafMap_w {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) :
    φ ≫ openComplementRestriction hZ 𝒢 =
      openComplementRestriction hZ ℱ ≫
        (openComplementPushforwardFunctor hZ).map
          ((openComplementRestrictionFunctor hZ).map φ) := sorry

/-- The morphism on closed-support subsheaves induced by a morphism of `\mathcal O_X`-modules. -/
def subsheafMap {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) :
    ((subsheaf hZ ℱ : Subobject ℱ) : X.Modules) ⟶
      ((subsheaf hZ 𝒢 : Subobject 𝒢) : X.Modules) :=
  kernelSubobjectMap <|
    Arrow.homMk'
      φ
      ((openComplementPushforwardFunctor hZ).map
        ((openComplementRestrictionFunctor hZ).map φ))
      (subsheafMap_w hZ φ)

-- Proof sketch: the induced map on kernels is functorial, and restriction to the closed subset
-- preserves identity morphisms.
/-- The induced morphism on sections-with-support sheaves respects identity morphisms. -/
private theorem functor_map_id (ℱ : X.Modules) :
    (RingedSpace.closedSubsetModulePullback X Z).map (subsheafMap hZ (𝟙 ℱ)) =
      𝟙 (sheaf hZ ℱ) := sorry

-- Proof sketch: compose the naturality squares for `φ` and `ψ`, then use functoriality of
-- `kernelSubobjectMap` and restriction to the closed subset.
/-- The induced morphism on sections-with-support sheaves respects composition. -/
private theorem functor_map_comp
    {ℱ 𝒢 𝒦 : X.Modules} (φ : ℱ ⟶ 𝒢) (ψ : 𝒢 ⟶ 𝒦) :
    (RingedSpace.closedSubsetModulePullback X Z).map (subsheafMap hZ (φ ≫ ψ)) =
      (RingedSpace.closedSubsetModulePullback X Z).map (subsheafMap hZ φ) ≫
        (RingedSpace.closedSubsetModulePullback X Z).map (subsheafMap hZ ψ) := sorry

/-- Remark 17.13.5: the functor `𝓗[hZ] = \mathcal H_Z` sending an `\mathcal O_X`-module to its
sheaf of sections supported on the closed subset `Z`, viewed as an `\mathcal O_X|_Z`-module. -/
def functor : X.Modules ⥤ RingedSpace.closedSubsetModuleCategory X Z where
  obj ℱ := sheaf hZ ℱ
  map φ := (RingedSpace.closedSubsetModulePullback X Z).map (subsheafMap hZ φ)
  map_id := functor_map_id hZ
  map_comp := functor_map_comp hZ

end

open RingedSpace.ClosedSubsetSectionsWithSupport (functor)

@[inherit_doc]
scoped[RingedSpaceClosedSubsetSectionsWithSupport] notation "𝓗[" hZ "]" =>
  functor hZ

open scoped RingedSpaceClosedSubsetSectionsWithSupport

section

variable {X : RingedSpace.{u}} {Z : Set X} (hZ : IsClosed Z)

private theorem subsheaf_pushforward_eq_top
    (ℱ : RingedSpace.closedSubsetModuleCategory X Z) :
    subsheaf hZ ((RingedSpace.closedSubsetModulePushforward X Z).obj ℱ) = ⊤ := sorry

private theorem restriction_pushforward_counitApp_isIso
    (ℱ : RingedSpace.closedSubsetModuleCategory X Z) :
    IsIso
      ((SheafOfModules.pullbackPushforwardAdjunction
        (RingedSpace.closedSubsetStructureSheafHom X Z)).counit.app ℱ) := sorry

private theorem object_restriction_pushforward_unitApp_isIso (ℱ : X.Modules) :
    IsIso
      ((SheafOfModules.pullbackPushforwardAdjunction
        (RingedSpace.closedSubsetStructureSheafHom X Z)).unit.app (object hZ ℱ)) := sorry

private noncomputable abbrev pushforwardSectionsWithSupportAdjunctionUnitApp
    (ℱ : RingedSpace.closedSubsetModuleCategory X Z) :
    ℱ ⟶
      (𝓗[hZ]).obj ((RingedSpace.closedSubsetModulePushforward X Z).obj ℱ) :=
  @inv _ _ _ _
      ((SheafOfModules.pullbackPushforwardAdjunction
          (RingedSpace.closedSubsetStructureSheafHom X Z)).counit.app ℱ)
      (restriction_pushforward_counitApp_isIso ℱ) ≫
    (RingedSpace.closedSubsetModulePullback X Z).map
      ((asIso ((⊤ : Subobject
          ((RingedSpace.closedSubsetModulePushforward X Z).obj ℱ)).arrow)).inv ≫
        (Subobject.isoOfEq
          (subsheaf hZ ((RingedSpace.closedSubsetModulePushforward X Z).obj ℱ))
          ⊤
          (subsheaf_pushforward_eq_top hZ ℱ)).symm.hom)

private noncomputable abbrev pushforwardSectionsWithSupportAdjunctionCounitApp
    (ℱ : X.Modules) :
    (RingedSpace.closedSubsetModulePushforward X Z).obj ((𝓗[hZ]).obj ℱ) ⟶ ℱ :=
  @inv _ _ _ _
      ((SheafOfModules.pullbackPushforwardAdjunction
          (RingedSpace.closedSubsetStructureSheafHom X Z)).unit.app (object hZ ℱ))
      (object_restriction_pushforward_unitApp_isIso hZ ℱ) ≫
    (subsheaf hZ ℱ).arrow

-- Proof sketch: the explicit sections-with-support construction on `X` yields the canonical
-- closed-subset adjunction used in Lemma 17.13.6.
/-- The canonical adjunction between pushforward from the closed subset `Z` and the explicit
sections-with-support functor `𝓗[hZ] = \mathcal H_Z`. -/
noncomputable def pushforwardSectionsWithSupportAdjunction :
    RingedSpace.closedSubsetModulePushforward X Z ⊣ 𝓗[hZ] where
  unit :=
    { app := pushforwardSectionsWithSupportAdjunctionUnitApp hZ
      naturality := sorry }
  counit :=
    { app := pushforwardSectionsWithSupportAdjunctionCounitApp hZ
      naturality := sorry }
  left_triangle_components := by sorry
  right_triangle_components := by sorry

end

/-- For an open set `U ⊆ X`, the image of the canonical inclusion
`\mathcal H_Z(\mathcal F)_X(U) \hookrightarrow \mathcal F(U)` is exactly the set of sections whose
support is contained in `Z ∩ U`. -/
theorem subsheaf_app_range
    {X : RingedSpace.{u}} {Z : Set X} (hZ : IsClosed Z)
    (ℱ : X.Modules) (U : Opens X) :
    Set.range ((subsheaf hZ ℱ).arrow.val.app (op U)) =
      { s | moduleSectionSupport s ⊆ { x : U | x.1 ∈ Z } } := sorry

/-- A section of `\mathcal F(U)` lies in the image of `\mathcal H_Z(\mathcal F)(U)` exactly when
its support is contained in `Z ∩ U`. -/
theorem subsheaf_app_iff
    {X : RingedSpace.{u}} {Z : Set X} (hZ : IsClosed Z)
    (ℱ : X.Modules) (U : Opens X) (s : ℱ.val.obj (op U)) :
    s ∈ Set.range ((subsheaf hZ ℱ).arrow.val.app (op U)) ↔
      moduleSectionSupport s ⊆ { x : U | x.1 ∈ Z } := by
  simpa using
    congrArg (fun S : Set (ℱ.val.obj (op U)) ↦ s ∈ S) (subsheaf_app_range hZ ℱ U)

-- Proof sketch: the sectionwise support description forces every stalk outside `Z` to vanish.
/-- The sections-with-support subsheaf has support contained in the closed subset `Z`. -/
theorem subsheaf_support_subset
    {X : RingedSpace.{u}} {Z : Set X} (hZ : IsClosed Z)
    (ℱ : X.Modules) :
    moduleSupport (subsheaf hZ ℱ) ⊆ Z := sorry

-- Proof sketch: any subsheaf whose support is contained in `Z` has all of its local sections
-- supported there, so it factors through the sections-with-support subsheaf.
/-- Among subsheaves of `\mathcal F`, the sections-with-support subsheaf is the largest one whose
support is contained in `Z`. -/
theorem le_subsheaf_of_support_subset
    {X : RingedSpace.{u}} {Z : Set X} (hZ : IsClosed Z)
    {ℱ : X.Modules} (𝒢 : Subobject ℱ) (h𝒢 : moduleSupport 𝒢 ⊆ Z) :
    𝒢 ≤ subsheaf hZ ℱ := sorry

end

end ClosedSubsetSectionsWithSupport
end RingedSpace

section

variable {X : RingedSpace.{u}} {Z : Set X} (hZ : IsClosed Z)

open RingedSpace.ClosedSubsetSectionsWithSupport
open scoped RingedSpaceClosedSubsetSectionsWithSupport

/- Remark 17.13.5: for a closed subset `Z ⊆ X`, the owner functor of sections with support is the
explicit functor `𝓗[hZ] = \mathcal H_Z` valued in `\operatorname{Mod}(\mathcal O_X|_Z)`. -/
#check (𝓗[hZ] :
  X.Modules ⥤ RingedSpace.closedSubsetModuleCategory X Z)

local instance : Functor.IsRightAdjoint (𝓗[hZ]) :=
  (pushforwardSectionsWithSupportAdjunction hZ).isRightAdjoint

/- Remark 17.13.5: the sections-with-support functor `\mathcal H_Z` is left exact because right
adjoints preserve finite limits. -/
#synth PreservesFiniteLimits (𝓗[hZ])

end

section

variable {X Z : RingedSpace.{u}} (i : Z ⟶ X)
variable [RingedSpace.IsClosedImmersion i]

/-- The closed image of a closed immersion of ringed spaces. -/
private abbrev closedImmersionImage : Set X :=
  Set.range i.hom.base

/-- The closed image of a closed immersion is a closed subset of the target. -/
private theorem closedImmersionImage_isClosed : IsClosed (closedImmersionImage i) := by
  let hi : RingedSpace.IsClosedImmersion i := inferInstance
  exact hi.isClosedEmbedding.isClosed_range

/-- Closed-immersion bridge/view: the support subsheaf on `X` is the source-facing closed-subset
owner specialized to the closed image of `i`. -/
private abbrev ringedSpaceModuleSectionsWithSupportSubsheaf (ℱ : X.Modules) : Subobject ℱ :=
  RingedSpace.ClosedSubsetSectionsWithSupport.subsheaf (closedImmersionImage_isClosed i) ℱ

/-- The underlying `\mathcal O_X`-module sheaf of the sections-with-support subsheaf. -/
private abbrev ringedSpaceModuleSectionsWithSupportObject (ℱ : X.Modules) :
    X.Modules :=
  ((ringedSpaceModuleSectionsWithSupportSubsheaf i ℱ : Subobject ℱ) : X.Modules)

/-- Closed-immersion bridge/view: pull back the closed-subset support subsheaf to the source
ringed space `Z`. -/
private abbrev ringedSpaceModuleSectionsWithSupportSheaf (ℱ : X.Modules) : Z.Modules :=
  (i^*).obj (ringedSpaceModuleSectionsWithSupportObject i ℱ)

/-- The morphism on sections-with-support subsheaves induced by a morphism of
`\mathcal O_X`-modules. -/
private def ringedSpaceModuleSectionsWithSupportSubsheafMap
    {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) :
    ringedSpaceModuleSectionsWithSupportObject i ℱ ⟶
      ringedSpaceModuleSectionsWithSupportObject i 𝒢 :=
  RingedSpace.ClosedSubsetSectionsWithSupport.subsheafMap
    (closedImmersionImage_isClosed i) φ

-- Proof sketch: the closed-immersion bridge functor is obtained by pulling back the
-- source-facing support object along `i`.
/-- The induced morphism on sections-with-support sheaves respects identity morphisms. -/
private theorem ringedSpaceModuleSectionsWithSupportFunctor_map_id
    (ℱ : X.Modules) :
    (i^*).map (ringedSpaceModuleSectionsWithSupportSubsheafMap i (𝟙 ℱ)) =
      𝟙 (ringedSpaceModuleSectionsWithSupportSheaf i ℱ) := sorry

-- Proof sketch: combine the functoriality of the closed-subset support object with the
-- functoriality of pullback along `i`.
/-- The induced morphism on sections-with-support sheaves respects composition. -/
private theorem ringedSpaceModuleSectionsWithSupportFunctor_map_comp
    {ℱ 𝒢 𝒦 : X.Modules} (φ : ℱ ⟶ 𝒢) (ψ : 𝒢 ⟶ 𝒦) :
    (i^*).map (ringedSpaceModuleSectionsWithSupportSubsheafMap i (φ ≫ ψ)) =
      (i^*).map (ringedSpaceModuleSectionsWithSupportSubsheafMap i φ) ≫
        (i^*).map (ringedSpaceModuleSectionsWithSupportSubsheafMap i ψ) := sorry

private def closedImmersionSectionsWithSupportFunctor :
    X.Modules ⥤ Z.Modules where
  obj ℱ := ringedSpaceModuleSectionsWithSupportSheaf i ℱ
  map φ := (i^*).map (ringedSpaceModuleSectionsWithSupportSubsheafMap i φ)
  map_id := ringedSpaceModuleSectionsWithSupportFunctor_map_id i
  map_comp := ringedSpaceModuleSectionsWithSupportFunctor_map_comp i

private theorem ringedSpaceModuleSectionsWithSupportSubsheaf_pushforward_eq_top
    (ℱ : Z.Modules) :
    ringedSpaceModuleSectionsWithSupportSubsheaf i ((i _*).obj ℱ) = ⊤ := sorry

private theorem ringedSpaceModuleSectionsWithSupportObject_mem_essImage
    (ℱ : X.Modules) :
    (i _*).essImage (ringedSpaceModuleSectionsWithSupportObject i ℱ) := sorry

private theorem ringedSpaceModulePullbackPushforwardCounitApp_isIso
    (ℱ : Z.Modules) :
    IsIso ((SheafOfModules.pullbackPushforwardAdjunction
      (RingedSpace.Hom.toRingCatSheafHom i)).counit.app ℱ) := by
  let hFF : (SheafOfModules.pushforward
      (RingedSpace.Hom.toRingCatSheafHom i)).FullyFaithful := by
    change (i _*).FullyFaithful
    exact ringedSpaceModulePushforward_fullyFaithful_of_isClosedImmersion i
  letI : (SheafOfModules.pushforward
      (RingedSpace.Hom.toRingCatSheafHom i)).Full := hFF.full
  letI : (SheafOfModules.pushforward
      (RingedSpace.Hom.toRingCatSheafHom i)).Faithful := hFF.faithful
  infer_instance

private theorem ringedSpaceModulePullbackPushforwardUnitApp_isIso
    (ℱ : X.Modules) :
    IsIso
      ((SheafOfModules.pullbackPushforwardAdjunction
        (RingedSpace.Hom.toRingCatSheafHom i)).unit.app
          (ringedSpaceModuleSectionsWithSupportObject i ℱ)) := by
  let hFF : (SheafOfModules.pushforward
      (RingedSpace.Hom.toRingCatSheafHom i)).FullyFaithful := by
    change (i _*).FullyFaithful
    exact ringedSpaceModulePushforward_fullyFaithful_of_isClosedImmersion i
  letI : (SheafOfModules.pushforward
      (RingedSpace.Hom.toRingCatSheafHom i)).Full := hFF.full
  letI : (SheafOfModules.pushforward
      (RingedSpace.Hom.toRingCatSheafHom i)).Faithful := hFF.faithful
  let adj := SheafOfModules.pullbackPushforwardAdjunction
    (RingedSpace.Hom.toRingCatSheafHom i)
  exact
    (adj.isIso_unit_app_iff_mem_essImage).2
      (ringedSpaceModuleSectionsWithSupportObject_mem_essImage i ℱ)

private noncomputable abbrev ringedSpaceModuleSectionsWithSupportAdjunctionUnitApp
    (ℱ : Z.Modules) :
    ℱ ⟶
      (closedImmersionSectionsWithSupportFunctor i).obj ((i _*).obj ℱ) :=
  @inv _ _ _ _
      ((SheafOfModules.pullbackPushforwardAdjunction
          (RingedSpace.Hom.toRingCatSheafHom i)).counit.app ℱ)
      (ringedSpaceModulePullbackPushforwardCounitApp_isIso i ℱ) ≫
    (i^*).map
      ((asIso ((⊤ : Subobject ((i _*).obj ℱ)).arrow)).inv ≫
        (Subobject.isoOfEq
          (ringedSpaceModuleSectionsWithSupportSubsheaf i ((i _*).obj ℱ))
          ⊤
          (ringedSpaceModuleSectionsWithSupportSubsheaf_pushforward_eq_top i ℱ)).symm.hom)

private noncomputable abbrev ringedSpaceModuleSectionsWithSupportAdjunctionCounitApp
    (ℱ : X.Modules) :
    (i _*).obj ((closedImmersionSectionsWithSupportFunctor i).obj ℱ) ⟶
      ℱ :=
  @inv _ _ _ _
      ((SheafOfModules.pullbackPushforwardAdjunction
          (RingedSpace.Hom.toRingCatSheafHom i)).unit.app
            (ringedSpaceModuleSectionsWithSupportObject i ℱ))
      (ringedSpaceModulePullbackPushforwardUnitApp_isIso i ℱ) ≫
    (ringedSpaceModuleSectionsWithSupportSubsheaf i ℱ).arrow

private noncomputable def closedImmersionPushforwardSectionsWithSupportAdjunction :
    i _* ⊣ closedImmersionSectionsWithSupportFunctor i where
  unit :=
    { app := ringedSpaceModuleSectionsWithSupportAdjunctionUnitApp i
      naturality := sorry }
  counit :=
    { app := ringedSpaceModuleSectionsWithSupportAdjunctionCounitApp i
      naturality := sorry }
  left_triangle_components := by sorry
  right_triangle_components := by sorry

end

/-- Closed-immersion bridge/view: pushforward along a closed immersion is a left adjoint. -/
noncomputable instance ringedSpaceModulePushforward_isLeftAdjoint_of_isClosedImmersion
    {X Z : RingedSpace.{u}} (i : Z ⟶ X) [RingedSpace.IsClosedImmersion i] :
    (i _*).IsLeftAdjoint :=
  (closedImmersionPushforwardSectionsWithSupportAdjunction i).isLeftAdjoint

end AlgebraicGeometry
