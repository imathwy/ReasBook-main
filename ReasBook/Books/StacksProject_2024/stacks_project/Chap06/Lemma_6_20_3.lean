import Mathlib
import StacksProject_2024.stacks_project.Chap06.Lemma_6_14_2

open CategoryTheory TopCat TopologicalSpace
open TopCat.Presheaf

noncomputable section

universe u

section

variable {X : TopCat.{u}} {𝒪 𝒪' : X.Sheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
variable
  (ℱ : SheafOfModules
    ((CategoryTheory.sheafCompose (Opens.grothendieckTopology X)
      (CategoryTheory.forget₂ CommRingCat RingCat)).obj 𝒪))
variable (x : X)

local notation "J" => Opens.grothendieckTopology X

/- Domain-style sampling for Lemma 6.20.3:
- primary domain: stalkwise base change for pullback of sheaves of modules over sheaves of
  commutative rings on a topological space;
- sampled owner API:
  `TopCat.Presheaf.stalkBaseChangeComparison`,
  `TopCat.Presheaf.stalkBaseChangeComparison_isIso`,
  `SheafOfModules.pullbackIso`,
  `PresheafOfModules.sheafificationAdjunction`,
  `TopCat.Sheaf.stalkPullbackIso`;
- source/core/bridge triage:
  `source-facing`: the textbook stalkwise base-change isomorphism for sheaf pullback;
  `core/canonical`: the presheaf-level base-change owner
    `TopCat.Presheaf.stalkBaseChangeComparison`;
  `bridge/view`: the comparison from the sheaf pullback to the sheafification of the presheaf
    pullback, plus the resulting stalk comparison.

Primitive data are the morphism of sheaves of commutative rings `p : 𝒪 ⟶ 𝒪'` and the
`𝒪`-module sheaf `ℱ`. The presheaf-level stalk base-change map is already owned upstream, so this
file should reuse that owner directly and keep only the sheafification/pullback bridge local.
-/

/-- The underlying sheaf of rings obtained by forgetting commutativity. -/
private abbrev ringSheafOfComm (𝒪 : X.Sheaf CommRingCat.{u}) : X.Sheaf RingCat.{u} :=
  CategoryTheory.sheafCompose J (CategoryTheory.forget₂ CommRingCat RingCat) |>.obj 𝒪

/-- The forgotten ring-sheaf morphism induced by `p`, in the identity-on-opens shape consumed by
`SheafOfModules.pullback`. -/
private noncomputable abbrev ringSheafHomOverId :
    ringSheafOfComm 𝒪 ⟶
      (Functor.sheafPushforwardContinuous (𝟭 (Opens X)) RingCat J J).obj
        (ringSheafOfComm 𝒪') :=
  (CategoryTheory.sheafCompose J (CategoryTheory.forget₂ CommRingCat RingCat)).map p ≫
    (Functor.sheafPushforwardContinuousId RingCat J).inv.app (ringSheafOfComm 𝒪')

/-- The forgotten ring-presheaf morphism induced by `p`, in the shape consumed by
`PresheafOfModules.pullback`. -/
private abbrev ringPresheafHomOverId :
    (ringSheafOfComm 𝒪).obj ⟶ (𝟭 (Opens X)).op ⋙ (ringSheafOfComm 𝒪').obj :=
  show (ringSheafOfComm 𝒪).obj ⟶ (𝟭 (Opens X)).op ⋙ (ringSheafOfComm 𝒪').obj from
    Functor.whiskerRight p.hom (CategoryTheory.forget₂ CommRingCat RingCat)

local notation "sheafModulePullback" =>
  SheafOfModules.pullback (ringSheafHomOverId p)
local notation "presheafModulePullback" =>
  PresheafOfModules.pullback (ringPresheafHomOverId p)

private noncomputable abbrev presheafPullbackObj :=
  (presheafModulePullback).obj ℱ.val

private noncomputable abbrev commRingStalkToRingStalkIso (x : X) (𝒪 : X.Sheaf CommRingCat.{u}) :
    (forget₂ CommRingCat RingCat).obj (TopCat.Presheaf.stalk 𝒪.obj x) ≅
      (ringSheafOfComm 𝒪).presheaf.stalk x :=
  CategoryTheory.preservesColimitIso (forget₂ CommRingCat RingCat)
    ((OpenNhds.inclusion x).op ⋙ 𝒪.obj)

private local instance :
    Module ↑(TopCat.Presheaf.stalk 𝒪.obj x) ↑(TopCat.Presheaf.stalk ℱ.val.presheaf x) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier ℱ.val x

private noncomputable instance
    : Module ↑(TopCat.Presheaf.stalk 𝒪'.obj x)
        ↑(TopCat.Presheaf.stalk (presheafPullbackObj p ℱ).presheaf x) := by
  let restricted : ModuleCat ↑(TopCat.Presheaf.stalk 𝒪'.obj x) :=
    (ModuleCat.restrictScalars (commRingStalkToRingStalkIso x 𝒪').hom.hom).obj
      (ModuleCat.of ↑((ringSheafOfComm 𝒪').presheaf.stalk x)
        ↑(TopCat.Presheaf.stalk (presheafPullbackObj p ℱ).presheaf x))
  change Module ↑(TopCat.Presheaf.stalk 𝒪'.obj x) ↑restricted
  infer_instance

private noncomputable instance
    : Module ↑(TopCat.Presheaf.stalk 𝒪'.obj x)
        ↑(TopCat.Presheaf.stalk ((sheafModulePullback).obj ℱ).val.presheaf x) := by
  let restricted : ModuleCat ↑(TopCat.Presheaf.stalk 𝒪'.obj x) :=
    (ModuleCat.restrictScalars (commRingStalkToRingStalkIso x 𝒪').hom.hom).obj
      (ModuleCat.of ↑((ringSheafOfComm 𝒪').presheaf.stalk x)
        ↑(TopCat.Presheaf.stalk ((sheafModulePullback).obj ℱ).val.presheaf x))
  change Module ↑(TopCat.Presheaf.stalk 𝒪'.obj x) ↑restricted
  infer_instance

/-- The stalk map induced by a morphism of module presheaves over a fixed ring sheaf. -/
private noncomputable abbrev stalkUnderlyingMap
    {R : X.Sheaf RingCat.{u}} {ℱ 𝒢 : PresheafOfModules R.obj} (x : X) (φ : ℱ ⟶ 𝒢) :
    TopCat.Presheaf.stalk ℱ.presheaf x ⟶ TopCat.Presheaf.stalk 𝒢.presheaf x :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
    ((PresheafOfModules.toPresheaf R.obj).map φ)

/-- The stalk map induced by a morphism of module presheaves is linear over the stalk ring. -/
private theorem stalkUnderlyingMap_smul
    {R : X.Sheaf RingCat.{u}} {ℱ 𝒢 : PresheafOfModules R.obj} (x : X) (φ : ℱ ⟶ 𝒢) :
    ∀ (r : R.presheaf.stalk x) (m : ↑(TopCat.Presheaf.stalk ℱ.presheaf x)),
      stalkUnderlyingMap x φ (r • m) = r • stalkUnderlyingMap x φ m := sorry

/-- The stalk map induced by a morphism of module presheaves, packaged as a module homomorphism. -/
private noncomputable def stalkModuleMap
    {R : X.Sheaf RingCat.{u}} {ℱ 𝒢 : PresheafOfModules R.obj} (x : X) (φ : ℱ ⟶ 𝒢) :
    ModuleCat.of (R.presheaf.stalk x) ↑(TopCat.Presheaf.stalk ℱ.presheaf x) ⟶
      ModuleCat.of (R.presheaf.stalk x) ↑(TopCat.Presheaf.stalk 𝒢.presheaf x) :=
  ModuleCat.ofHom
    { toFun := stalkUnderlyingMap x φ
      map_add' := by
        intro m n
        exact (stalkUnderlyingMap x φ).hom.map_add m n
      map_smul' := stalkUnderlyingMap_smul x φ }

/-- If the underlying additive stalk map is an isomorphism, then the corresponding packaged
module-valued stalk map is also an isomorphism. -/
private theorem stalkModuleMap_isIso
    {R : X.Sheaf RingCat.{u}} {ℱ 𝒢 : PresheafOfModules R.obj} (x : X) (φ : ℱ ⟶ 𝒢)
    [IsIso (stalkUnderlyingMap x φ)] :
    IsIso (stalkModuleMap x φ) := by
  let F := forget₂ (ModuleCat (R.presheaf.stalk x)) AddCommGrpCat
  haveI : IsIso (F.map (stalkModuleMap x φ)) := by
    change IsIso (stalkUnderlyingMap x φ)
    infer_instance
  exact isIso_of_reflects_iso (stalkModuleMap x φ) F

/-- The stalk map on the unit of module sheafification for the presheaf pullback. -/
private noncomputable def presheafPullbackSheafificationUnitStalkHom :
    ModuleCat.of ((ringSheafOfComm 𝒪').presheaf.stalk x)
        ↑(TopCat.Presheaf.stalk (presheafPullbackObj p ℱ).presheaf x) ⟶
      ModuleCat.of ((ringSheafOfComm 𝒪').presheaf.stalk x)
        ↑(TopCat.Presheaf.stalk
          (((PresheafOfModules.sheafification (𝟙 (ringSheafOfComm 𝒪').obj)).obj
            (presheafPullbackObj p ℱ)).val.presheaf) x) := by
  simpa using
    stalkModuleMap x
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheafOfComm 𝒪').obj)).unit.app
        (presheafPullbackObj p ℱ))

private instance presheafPullbackSheafificationUnitStalkHom_isIso :
    IsIso (presheafPullbackSheafificationUnitStalkHom p ℱ x) := by
  let φ :=
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheafOfComm 𝒪').obj)).unit.app
      (presheafPullbackObj p ℱ))
  haveI : IsIso (stalkUnderlyingMap x φ) := by
    change IsIso
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        (CategoryTheory.toSheafify J (presheafPullbackObj p ℱ).presheaf))
    simpa [φ, stalkUnderlyingMap] using
      (TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
        (presheafPullbackObj p ℱ).presheaf)
  simpa [presheafPullbackSheafificationUnitStalkHom, φ] using stalkModuleMap_isIso x φ

/-- The stalk map on the canonical identification between sheaf pullback and sheafified presheaf
pullback. -/
private noncomputable def sheafPullbackIsoStalkHom :
    ModuleCat.of ((ringSheafOfComm 𝒪').presheaf.stalk x)
        ↑(TopCat.Presheaf.stalk ((sheafModulePullback).obj ℱ).val.presheaf x) ⟶
      ModuleCat.of ((ringSheafOfComm 𝒪').presheaf.stalk x)
        ↑(TopCat.Presheaf.stalk
          (((PresheafOfModules.sheafification (𝟙 (ringSheafOfComm 𝒪').obj)).obj
            (presheafPullbackObj p ℱ)).val.presheaf) x) := by
  simpa using
    stalkModuleMap x (((SheafOfModules.pullbackIso
      (ringSheafHomOverId p)).app ℱ).hom.val)

private instance sheafPullbackIsoStalkHom_isIso :
    IsIso (sheafPullbackIsoStalkHom p ℱ x) := by
  sorry

/-- The stalk isomorphism identifying the stalk of the underlying presheaf pullback with the stalk
of the sheaf pullback. This is the private comparison used in the sheaf-level base-change
statement. -/
private noncomputable abbrev sheafOfModules_pullbackPresheafStalkIso := by
  exact asIso (presheafPullbackSheafificationUnitStalkHom p ℱ x) ≪≫
    (asIso (sheafPullbackIsoStalkHom p ℱ x)).symm

private noncomputable def presheafPullbackStalkRestrictedHom :
    ModuleCat.of ↑(TopCat.Presheaf.stalk (𝒪'.obj) x)
        ↑(TopCat.Presheaf.stalk
          ((PresheafOfModules.pullback
            (show (𝒪.obj ⋙ forget₂ CommRingCat RingCat) ⟶
                (𝟭 (Opens X)).op ⋙ (𝒪'.obj ⋙ forget₂ CommRingCat RingCat) from
              Functor.whiskerRight p.hom (forget₂ CommRingCat RingCat))).obj
            ℱ.val).presheaf x) ⟶
      (ModuleCat.restrictScalars ((commRingStalkToRingStalkIso x 𝒪').hom.hom)).obj
        (ModuleCat.of ↑((ringSheafOfComm 𝒪').presheaf.stalk x)
          ↑(TopCat.Presheaf.stalk ((presheafPullbackObj p ℱ).presheaf) x)) := by
  exact ModuleCat.ofHom
    { toFun := fun m ↦ m
      map_add' := by
        intro m n
        rfl
      map_smul' := by
        sorry }

private instance presheafPullbackStalkRestrictedHom_isIso :
    IsIso (presheafPullbackStalkRestrictedHom p ℱ x) := by
  sorry

private noncomputable abbrev presheafPullbackStalkRestrictedIso :
    ModuleCat.of ↑(TopCat.Presheaf.stalk (𝒪'.obj) x)
        ↑(TopCat.Presheaf.stalk
          ((PresheafOfModules.pullback
            (show (𝒪.obj ⋙ forget₂ CommRingCat RingCat) ⟶
                (𝟭 (Opens X)).op ⋙ (𝒪'.obj ⋙ forget₂ CommRingCat RingCat) from
              Functor.whiskerRight p.hom (forget₂ CommRingCat RingCat))).obj
            ℱ.val).presheaf x) ≅
      (ModuleCat.restrictScalars ((commRingStalkToRingStalkIso x 𝒪').hom.hom)).obj
        (ModuleCat.of ↑((ringSheafOfComm 𝒪').presheaf.stalk x)
          ↑(TopCat.Presheaf.stalk ((presheafPullbackObj p ℱ).presheaf) x)) :=
  asIso (presheafPullbackStalkRestrictedHom p ℱ x)

private noncomputable abbrev sheafPullbackStalkRestrictedIso :
    ModuleCat.of ↑(TopCat.Presheaf.stalk (𝒪'.obj) x)
        ↑(TopCat.Presheaf.stalk ((sheafModulePullback).obj ℱ).val.presheaf x) ≅
      (ModuleCat.restrictScalars ((commRingStalkToRingStalkIso x 𝒪').hom.hom)).obj
        (ModuleCat.of ↑((ringSheafOfComm 𝒪').presheaf.stalk x)
          ↑(TopCat.Presheaf.stalk ((sheafModulePullback).obj ℱ).val.presheaf x)) := by
  exact Iso.refl _

/-- The stalk of the presheaf pullback identifies canonically with the stalk of the sheaf pullback.
-/
private noncomputable abbrev pullbackStalkComparisonIso :
    ModuleCat.of ↑(TopCat.Presheaf.stalk (𝒪'.obj) x)
        ↑(TopCat.Presheaf.stalk
          ((PresheafOfModules.pullback
            (show (𝒪.obj ⋙ forget₂ CommRingCat RingCat) ⟶
                (𝟭 (Opens X)).op ⋙ (𝒪'.obj ⋙ forget₂ CommRingCat RingCat) from
              Functor.whiskerRight p.hom (forget₂ CommRingCat RingCat))).obj
            ℱ.val).presheaf x) ≅
      ModuleCat.of ↑(TopCat.Presheaf.stalk (𝒪'.obj) x)
        ↑(TopCat.Presheaf.stalk ((sheafModulePullback).obj ℱ).val.presheaf x) := by
  letI :
      Module ↑(TopCat.Presheaf.stalk 𝒪'.obj x)
        ↑(TopCat.Presheaf.stalk
          ((PresheafOfModules.pullback
            (show (𝒪.obj ⋙ forget₂ CommRingCat RingCat) ⟶
                (𝟭 (Opens X)).op ⋙ (𝒪'.obj ⋙ forget₂ CommRingCat RingCat) from
              Functor.whiskerRight p.hom (forget₂ CommRingCat RingCat))).obj
            ℱ.val).presheaf x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      ((PresheafOfModules.pullback
        (show (𝒪.obj ⋙ forget₂ CommRingCat RingCat) ⟶
            (𝟭 (Opens X)).op ⋙ (𝒪'.obj ⋙ forget₂ CommRingCat RingCat) from
          Functor.whiskerRight p.hom (forget₂ CommRingCat RingCat))).obj
        ℱ.val) x
  have hsource :
      ModuleCat.of ↑(TopCat.Presheaf.stalk (𝒪'.obj) x)
          ↑(TopCat.Presheaf.stalk
            ((PresheafOfModules.pullback
              (show (𝒪.obj ⋙ forget₂ CommRingCat RingCat) ⟶
                  (𝟭 (Opens X)).op ⋙ (𝒪'.obj ⋙ forget₂ CommRingCat RingCat) from
                Functor.whiskerRight p.hom (forget₂ CommRingCat RingCat))).obj
              ℱ.val).presheaf x) ≅
        (ModuleCat.restrictScalars ((commRingStalkToRingStalkIso x 𝒪').hom.hom)).obj
          (ModuleCat.of ↑((ringSheafOfComm 𝒪').presheaf.stalk x)
            ↑(TopCat.Presheaf.stalk (((presheafModulePullback).obj ℱ.val).presheaf) x)) := by
    simpa [ringPresheafHomOverId, ringSheafOfComm] using
      presheafPullbackStalkRestrictedIso p ℱ x
  exact
    hsource ≪≫
      (ModuleCat.restrictScalars ((commRingStalkToRingStalkIso x 𝒪').hom.hom)).mapIso
        (sheafOfModules_pullbackPresheafStalkIso p ℱ x) ≪≫
      (sheafPullbackStalkRestrictedIso p ℱ x).symm

/-- Lemma 6.20.3 (Tag 008B): for a morphism `p : 𝒪 ⟶ 𝒪'` of sheaves of commutative rings on `X`,
an `𝒪`-module sheaf `ℱ`, and `x : X`, the canonical base-change map on stalks
`ℱ_x ⊗[𝒪_x] 𝒪'_x ≅ (ℱ ⊗_𝒪 𝒪')_x` is an isomorphism. -/
noncomputable abbrev sheafOfModules_pullback_stalkIso :
      (ModuleCat.extendScalars (((TopCat.Presheaf.stalkFunctor CommRingCat x).map p.hom).hom)).obj
      (ModuleCat.of ↑(TopCat.Presheaf.stalk (𝒪.obj) x) ↑(TopCat.Presheaf.stalk ℱ.val.presheaf x)) ≅
        ModuleCat.of ↑(TopCat.Presheaf.stalk (𝒪'.obj) x)
          ↑(TopCat.Presheaf.stalk ((sheafModulePullback).obj ℱ).val.presheaf x) := by
  exact
    (by
      letI :
          Module ↑(TopCat.Presheaf.stalk 𝒪'.obj x)
            ↑(TopCat.Presheaf.stalk
              ((PresheafOfModules.pullback
                (show (𝒪.obj ⋙ forget₂ CommRingCat RingCat) ⟶
                    (𝟭 (Opens X)).op ⋙ (𝒪'.obj ⋙ forget₂ CommRingCat RingCat) from
                  Functor.whiskerRight p.hom (forget₂ CommRingCat RingCat))).obj
                ℱ.val).presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          ((PresheafOfModules.pullback
            (show (𝒪.obj ⋙ forget₂ CommRingCat RingCat) ⟶
                (𝟭 (Opens X)).op ⋙ (𝒪'.obj ⋙ forget₂ CommRingCat RingCat) from
              Functor.whiskerRight p.hom (forget₂ CommRingCat RingCat))).obj
            ℱ.val) x
      simpa [ringPresheafHomOverId, ringSheafOfComm] using
        asIso (TopCat.Presheaf.stalkBaseChangeComparison p.hom ℱ.val x)) ≪≫
      pullbackStalkComparisonIso p ℱ x

end
