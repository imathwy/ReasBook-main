import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import StacksProject_2024.Chap12.Remark_12_29_2
import StacksProject_2024.Chap13.Lemma_13_14_16
import StacksProject_2024.Chap18.Lemma_18_41_3
import StacksProject_2024.Chap21.Lemma_21_20_5_core

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open Opposite
open scoped RingedSiteDerived
open scoped RingedSiteDerivedSections

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard
set_option checkBinderAnnotations false

namespace RingedSite.Hom

local notation "Mod(" X ")" => ModuleCat X
local notation "DMod(" X ")" => ModuleDerived X
local notation "Qis(" X ")" => ModuleQis X

/- Domain-style sampling for Lemma 21.20.5:
- primary domain: unbounded derived direct image and derived sections on ringed sites;
- sampled owner declarations:
  `RingedSite.Hom.modulePushforwardDerived`,
  `RingedSite.Hom.moduleGlobalSectionsAdditiveFunctor`,
  `RingedSite.Hom.moduleGlobalSectionsDerived`,
  `RingedSite.Hom.moduleSectionsDerived`,
  `RingedSite.Hom.moduleSectionsToDerived`,
  `SheafOfModules.evaluation`,
  `_root_.ModuleCat.restrictScalars`,
  `Functor.mapDerivedCategory`,
  `Functor.rightDerivedCompComparison`;
- best owner abstraction: the source-facing content here is the comparison between `Rf_*` and the
  canonical derived sections owners `RΓ[X]` and `RΓ[X](U)`, while the
  supporting owner data is the unbounded direct-image owner from `Lemma 21.19.1`, the evaluation
  functor at an object, and the exact restriction-of-scalars functor on section rings;
- primitive data: a morphism of ringed sites `f : X ⟶ Y`, the evaluation functor at an object,
  and the restriction-of-scalars functor induced by
  `f.structureSheafMap.1.app (op V) : Γ(V, 𝒪_Y) → Γ(f(V), 𝒪_X)`;
- derived API: the derived global/objectwise sections owners below together with the two
  source-facing comparison isomorphism statements and their objectwise companions.

Source/core/bridge triage:
- `source-facing`: the two comparison isomorphisms of Lemma 21.20.5;
- `core/canonical`: `modulePushforwardDerived`, `moduleGlobalSectionsAdditiveFunctor`,
  `moduleGlobalSectionsDerived`, `moduleSectionsDerived`, `moduleSectionsToDerived`,
  `SheafOfModules.evaluation`, `_root_.ModuleCat.restrictScalars`,
  `Functor.mapDerivedCategory`, and `Functor.rightDerivedCompComparison`;
- `bridge/view`: the exact derived restriction-of-scalars comparison used to express the second
  source-facing comparison in the ring `Γ(V, 𝒪_Y)`.
-/
section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)

variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{max u v}]
variable [HasWeakSheafify Y.siteTopology AddCommGrpCat.{max u v}]
variable [HasGlobalSectionsFunctor Y.siteTopology AddCommGrpCat.{max u v}]
variable [f.modulePushforward.Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (Qis(X))]
variable [Functor.HasRightDerivedFunctor (moduleGlobalSectionsToDerived X) (Qis(X))]
variable [Functor.HasRightDerivedFunctor (moduleGlobalSectionsToDerived Y) (Qis(Y))]

private noncomputable def globalSectionsLimitPreNat :
    (lim : (Xᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ AddCommGrpCat.{max u v}) ⟶
      (Functor.whiskeringLeft Yᵒᵖ Xᵒᵖ AddCommGrpCat.{max u v}).obj f.base.op ⋙
        (lim : (Yᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ AddCommGrpCat.{max u v}) :=
  NatTrans.mk
    (fun F ↦ limit.pre F f.base.op)
    (by
      intro F G α
      change lim.map α ≫ limit.pre G f.base.op =
        limit.pre F f.base.op ≫
          lim.map
            (((Functor.whiskeringLeft Yᵒᵖ Xᵒᵖ AddCommGrpCat.{max u v}).obj f.base.op).map α)
      exact limit.map_pre α f.base.op)

private noncomputable def sheafGlobalSections_pushforwardNat :
    Sheaf.Γ X.siteTopology AddCommGrpCat.{max u v} ⟶
      f.base.sheafPushforwardContinuous AddCommGrpCat.{max u v} Y.siteTopology X.siteTopology ⋙
        Sheaf.Γ Y.siteTopology AddCommGrpCat.{max u v} :=
  (Sheaf.ΓNatIsoLim X.siteTopology AddCommGrpCat.{max u v}).hom ≫
    Functor.whiskerLeft
      (sheafToPresheaf X.siteTopology AddCommGrpCat.{max u v})
      (globalSectionsLimitPreNat f) ≫
    (Functor.associator
      (sheafToPresheaf X.siteTopology AddCommGrpCat.{max u v})
      ((Functor.whiskeringLeft Yᵒᵖ Xᵒᵖ AddCommGrpCat.{max u v}).obj f.base.op)
      (lim : (Yᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ AddCommGrpCat.{max u v})).inv ≫
    Functor.whiskerRight
      ((f.base.sheafPushforwardContinuousCompSheafToPresheafIso
          AddCommGrpCat.{max u v}
          Y.siteTopology
          X.siteTopology).symm.hom)
      (lim : (Yᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ AddCommGrpCat.{max u v}) ≫
    (Functor.associator
      (f.base.sheafPushforwardContinuous AddCommGrpCat.{max u v} Y.siteTopology X.siteTopology)
      (sheafToPresheaf Y.siteTopology AddCommGrpCat.{max u v})
      (lim : (Yᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ AddCommGrpCat.{max u v})).hom ≫
    Functor.whiskerLeft
      (f.base.sheafPushforwardContinuous AddCommGrpCat.{max u v} Y.siteTopology X.siteTopology)
      (Sheaf.ΓNatIsoLim Y.siteTopology AddCommGrpCat.{max u v}).inv

/-- The underived global-sections comparison
`moduleGlobalSectionsAdditiveFunctor X ⟶ f.modulePushforward ⋙ moduleGlobalSectionsAdditiveFunctor Y`. -/
private noncomputable def moduleGlobalSectionsFunctor_pushforwardNat :
    moduleGlobalSectionsAdditiveFunctor X ⟶
      f.modulePushforward ⋙ moduleGlobalSectionsAdditiveFunctor Y := by
  simpa [moduleGlobalSectionsAdditiveFunctor] using
    Functor.whiskerLeft (SheafOfModules.toSheaf X.structureSheaf)
      (sheafGlobalSections_pushforwardNat f)

private noncomputable def moduleGlobalSectionsToDerived_pushforwardNat :
    moduleGlobalSectionsToDerived X ⟶
      f.modulePushforward.mapHomotopyCategory (up ℤ) ⋙ moduleGlobalSectionsToDerived Y := by
  simpa [moduleGlobalSectionsToDerived, mapHomotopyCategoryToDerived] using
    Functor.whiskerRight
      (NatTrans.mapHomotopyCategory
        (moduleGlobalSectionsFunctor_pushforwardNat f) (up ℤ))
      DerivedCategory.Qh ≫
    Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso
        f.modulePushforward
        (moduleGlobalSectionsAdditiveFunctor Y)).hom
      DerivedCategory.Qh ≫
    (Functor.associator
      (f.modulePushforward.mapHomotopyCategory (up ℤ))
      ((moduleGlobalSectionsAdditiveFunctor Y).mapHomotopyCategory (up ℤ))
      DerivedCategory.Qh).hom

private noncomputable def modulePushforwardDerived_globalSectionsTargetNat :
    f.modulePushforward.mapHomotopyCategory (up ℤ) ⋙ moduleGlobalSectionsToDerived Y ⟶
      (DerivedCategory.Qh : HomotopyCategory (Mod(X)) (up ℤ) ⥤ DMod(X)) ⋙
        R(f)_* ⋙ RΓ[Y] :=
  Functor.whiskerLeft
      (f.modulePushforward.mapHomotopyCategory (up ℤ))
      (Functor.totalRightDerivedUnit
        (moduleGlobalSectionsToDerived Y)
        (DerivedCategory.Qh : HomotopyCategory (Mod(Y)) (up ℤ) ⥤ DMod(Y))
        (Qis(Y))) ≫
    (Functor.associator
      (f.modulePushforward.mapHomotopyCategory (up ℤ))
      (DerivedCategory.Qh : HomotopyCategory (Mod(Y)) (up ℤ) ⥤ DMod(Y))
      RΓ[Y]).inv ≫
    Functor.whiskerRight
      (Functor.totalRightDerivedUnit
        (modulePushforwardToDerived f)
        (DerivedCategory.Qh : HomotopyCategory (Mod(X)) (up ℤ) ⥤ DMod(X))
        (Qis(X)))
      RΓ[Y] ≫
    (Functor.associator
      (DerivedCategory.Qh : HomotopyCategory (Mod(X)) (up ℤ) ⥤ DMod(X))
      R(f)_*
      RΓ[Y]).hom

-- Proof sketch: this is the unbounded Leray comparison from the underived global-sections
-- comparison and the canonical total right derived structure.
private noncomputable def modulePushforwardDerived_globalSectionsComparisonHom :
    RΓ[X] ⟶ R(f)_* ⋙ RΓ[Y] :=
  Functor.rightDerivedNatTrans
    (RΓ[X])
    (R(f)_* ⋙ RΓ[Y])
    (Functor.totalRightDerivedUnit
      (moduleGlobalSectionsToDerived X)
      (DerivedCategory.Qh : HomotopyCategory (Mod(X)) (up ℤ) ⥤ DMod(X))
      (Qis(X)))
    (modulePushforwardDerived_globalSectionsTargetNat f)
    (Qis(X))
    (moduleGlobalSectionsToDerived_pushforwardNat f)

-- Proof sketch: this is the unbounded Leray comparison isomorphism from Lemma 21.20.5 (1).
/-- Lemma 21.20.5 (1): the canonical comparison `RΓ[X] ⟶ R(f)_* ⋙ RΓ[Y]` is an
isomorphism. -/
@[stacks 0D6H]
instance modulePushforwardDerived_globalSectionsComparison :
    IsIso
      (Functor.rightDerivedNatTrans
        (RΓ[X])
        (R(f)_* ⋙ RΓ[Y])
        (Functor.totalRightDerivedUnit
          (moduleGlobalSectionsToDerived X)
          (DerivedCategory.Qh : HomotopyCategory (Mod(X)) (up ℤ) ⥤ DMod(X))
          (Qis(X)))
        (modulePushforwardDerived_globalSectionsTargetNat f)
        (Qis(X))
        (moduleGlobalSectionsToDerived_pushforwardNat f)) := by
  change IsIso (modulePushforwardDerived_globalSectionsComparisonHom f)
  sorry

/-- Lemma 21.20.5 (1), theorem-form companion to
`modulePushforwardDerived_globalSectionsComparison`. -/
@[stacks 0D6H]
theorem modulePushforwardDerived_globalSectionsComparison_isIso :
    IsIso
      (Functor.rightDerivedNatTrans
        (RΓ[X])
        (R(f)_* ⋙ RΓ[Y])
        (Functor.totalRightDerivedUnit
          (moduleGlobalSectionsToDerived X)
          (DerivedCategory.Qh : HomotopyCategory (Mod(X)) (up ℤ) ⥤ DMod(X))
          (Qis(X)))
        (modulePushforwardDerived_globalSectionsTargetNat f)
        (Qis(X))
        (moduleGlobalSectionsToDerived_pushforwardNat f)) := by
  infer_instance

/-- Lemma 21.20.5 (1), objectwise companion: the canonical comparison morphism on `K` is an
isomorphism. -/
@[stacks 0D6H]
theorem modulePushforwardDerived_globalSectionsComparison_app_isIso
    (K : DMod(X)) :
    IsIso
      ((Functor.rightDerivedNatTrans
          (RΓ[X])
          (R(f)_* ⋙ RΓ[Y])
          (Functor.totalRightDerivedUnit
            (moduleGlobalSectionsToDerived X)
            (DerivedCategory.Qh : HomotopyCategory (Mod(X)) (up ℤ) ⥤ DMod(X))
            (Qis(X)))
          (modulePushforwardDerived_globalSectionsTargetNat f)
          (Qis(X))
          (moduleGlobalSectionsToDerived_pushforwardNat f)).app K) := by
  change IsIso ((modulePushforwardDerived_globalSectionsComparisonHom f).app K)
  let _ : IsIso (modulePushforwardDerived_globalSectionsComparisonHom f) := by
    change IsIso
      (Functor.rightDerivedNatTrans
        (RΓ[X])
        (R(f)_* ⋙ RΓ[Y])
        (Functor.totalRightDerivedUnit
          (moduleGlobalSectionsToDerived X)
          (DerivedCategory.Qh : HomotopyCategory (Mod(X)) (up ℤ) ⥤ DMod(X))
          (Qis(X)))
        (modulePushforwardDerived_globalSectionsTargetNat f)
        (Qis(X))
        (moduleGlobalSectionsToDerived_pushforwardNat f))
    infer_instance
  infer_instance

end

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
variable [IsGrothendieckAbelian.{max u v} (Mod(X))]
variable [IsGrothendieckAbelian.{max u v} (Mod(Y))]
variable [f.modulePushforward.Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (Qis(X))]

variable (V : Y)
private instance :
    (_root_.ModuleCat.restrictScalars.{max u v}
      (f.structureSheafMap.1.app (op V)).hom).Additive := by
  infer_instance

private instance :
    (pushforward f).Additive := by
  simpa using (inferInstance : f.modulePushforward.Additive)

private instance :
    PreservesFiniteLimits
      (_root_.ModuleCat.restrictScalars.{max u v}
        (f.structureSheafMap.1.app (op V)).hom) := by
  let hExact :
      exactFunctor
        (_root_.ModuleCat (X.structureSheaf.1.obj (op (f.base.obj V))))
        (_root_.ModuleCat (Y.structureSheaf.1.obj (op V)))
        (_root_.ModuleCat.restrictScalars.{max u v}
          (f.structureSheafMap.1.app (op V)).hom) :=
    restrictScalars_exact (f.structureSheafMap.1.app (op V)).hom
  exact ((exactFunctor_iff _).1 hExact).1

private instance :
    PreservesFiniteColimits
      (_root_.ModuleCat.restrictScalars.{max u v}
        (f.structureSheafMap.1.app (op V)).hom) := by
  let hExact :
      exactFunctor
        (_root_.ModuleCat (X.structureSheaf.1.obj (op (f.base.obj V))))
        (_root_.ModuleCat (Y.structureSheaf.1.obj (op V)))
        (_root_.ModuleCat.restrictScalars.{max u v}
          (f.structureSheafMap.1.app (op V)).hom) :=
    restrictScalars_exact (f.structureSheafMap.1.app (op V)).hom
  exact ((exactFunctor_iff _).1 hExact).2

private abbrev moduleRestrictionAlongObjectToDerived :
    HomotopyCategory (_root_.ModuleCat (X.structureSheaf.1.obj (op (f.base.obj V)))) (up ℤ) ⥤
      DerivedCategory (_root_.ModuleCat (Y.structureSheaf.1.obj (op V))) :=
  mapHomotopyCategoryToDerived
    (_root_.ModuleCat.restrictScalars (f.structureSheafMap.1.app (op V)).hom)

omit [IsGrothendieckAbelian.{max u v} (Mod(X))]
  [IsGrothendieckAbelian.{max u v} (Mod(Y))] in
private theorem moduleSectionsFunctor_eq_pushforwardComp
    (f : RingedSite.Hom X Y) (V : Y) :
    SheafOfModules.evaluation X.structureSheaf (op (f.base.obj V)) ⋙
        _root_.ModuleCat.restrictScalars (f.structureSheafMap.1.app (op V)).hom =
      f.modulePushforward ⋙ SheafOfModules.evaluation Y.structureSheaf (op V) := by
  rfl

private abbrev moduleSectionsAlongObjectToDerived (f : RingedSite.Hom X Y) (V : Y) :
    HomotopyCategory (Mod(X)) (up ℤ) ⥤
      DerivedCategory (_root_.ModuleCat (Y.structureSheaf.1.obj (op V))) :=
  (SheafOfModules.evaluation X.structureSheaf (op (f.base.obj V))).mapHomotopyCategory (up ℤ) ⋙
    moduleRestrictionAlongObjectToDerived f V

private noncomputable def moduleSectionsToDerived_restrictScalarsCompIso :
    moduleSectionsAlongObjectToDerived f V ≅
      moduleSectionsToDerived X (f.base.obj V) ⋙
        (_root_.ModuleCat.restrictScalars
          (f.structureSheafMap.1.app (op V)).hom).mapDerivedCategory := by
  let evalX :=
    (SheafOfModules.evaluation X.structureSheaf (op (f.base.obj V))).mapHomotopyCategory (up ℤ)
  simpa [moduleSectionsAlongObjectToDerived, moduleSectionsToDerived,
      moduleRestrictionAlongObjectToDerived, mapHomotopyCategoryToDerived, evalX] using
    Functor.isoWhiskerLeft
        evalX
        (_root_.ModuleCat.restrictScalars
          (f.structureSheafMap.1.app (op V)).hom).mapDerivedCategoryFactorsh.symm ≪≫
      (Functor.associator
        evalX
        DerivedCategory.Qh
        (_root_.ModuleCat.restrictScalars
          (f.structureSheafMap.1.app (op V)).hom).mapDerivedCategory).symm

private noncomputable def moduleSectionsToDerived_pushforwardCompIso :
    moduleSectionsAlongObjectToDerived f V ≅
      f.modulePushforward.mapHomotopyCategory (up ℤ) ⋙ moduleSectionsToDerived Y V := by
  let evalX :=
    (SheafOfModules.evaluation X.structureSheaf (op (f.base.obj V))).mapHomotopyCategory (up ℤ)
  let evalY :=
    (SheafOfModules.evaluation Y.structureSheaf (op V)).mapHomotopyCategory (up ℤ)
  let restrictH :=
    (_root_.ModuleCat.restrictScalars (f.structureSheafMap.1.app (op V)).hom)
      |>.mapHomotopyCategory (up ℤ)
  simpa [moduleSectionsAlongObjectToDerived, moduleSectionsToDerived,
      moduleRestrictionAlongObjectToDerived,
      moduleSectionsFunctor_eq_pushforwardComp f V, mapHomotopyCategoryToDerived,
      evalX, evalY, restrictH] using
    (Functor.associator evalX restrictH DerivedCategory.Qh).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomotopyCategoryCompIso
          (SheafOfModules.evaluation X.structureSheaf (op (f.base.obj V)))
          (_root_.ModuleCat.restrictScalars
            (f.structureSheafMap.1.app (op V)).hom)).symm
        DerivedCategory.Qh ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomotopyCategoryIso
          (eqToIso (moduleSectionsFunctor_eq_pushforwardComp f V)))
        DerivedCategory.Qh ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomotopyCategoryCompIso
          f.modulePushforward
          (SheafOfModules.evaluation Y.structureSheaf (op V)))
        DerivedCategory.Qh ≪≫
      (Functor.associator
        (f.modulePushforward.mapHomotopyCategory (up ℤ))
        evalY
        DerivedCategory.Qh).symm

private noncomputable def moduleSectionsAlongObjectSourceNat :
    moduleSectionsAlongObjectToDerived f V ⟶
      (DerivedCategory.Qh : HomotopyCategory (Mod(X)) (up ℤ) ⥤ DMod(X)) ⋙
        (RΓ[X](f.base.obj V) ⋙
          (_root_.ModuleCat.restrictScalars
            (f.structureSheafMap.1.app (op V)).hom).mapDerivedCategory) :=
  (moduleSectionsToDerived_restrictScalarsCompIso f V).hom ≫
    Functor.whiskerRight
      (Functor.totalRightDerivedUnit
        (moduleSectionsToDerived X (f.base.obj V))
        (DerivedCategory.Qh : HomotopyCategory (Mod(X)) (up ℤ) ⥤ DMod(X))
        (Qis(X)))
      (_root_.ModuleCat.restrictScalars
        (f.structureSheafMap.1.app (op V)).hom).mapDerivedCategory ≫
    (Functor.associator
      (DerivedCategory.Qh : HomotopyCategory (Mod(X)) (up ℤ) ⥤ DMod(X))
      RΓ[X](f.base.obj V)
      (_root_.ModuleCat.restrictScalars
        (f.structureSheafMap.1.app (op V)).hom).mapDerivedCategory).hom

private noncomputable def moduleSectionsAlongObjectTargetNat :
    moduleSectionsAlongObjectToDerived f V ⟶
      (DerivedCategory.Qh : HomotopyCategory (Mod(X)) (up ℤ) ⥤ DMod(X)) ⋙
        R(f)_* ⋙ RΓ[Y](V) :=
  (moduleSectionsToDerived_pushforwardCompIso f V).hom ≫
    Functor.whiskerLeft
      (f.modulePushforward.mapHomotopyCategory (up ℤ))
      (Functor.totalRightDerivedUnit
        (moduleSectionsToDerived Y V)
        (DerivedCategory.Qh : HomotopyCategory (Mod(Y)) (up ℤ) ⥤ DMod(Y))
        (Qis(Y))) ≫
    (Functor.associator
      (f.modulePushforward.mapHomotopyCategory (up ℤ))
      (DerivedCategory.Qh : HomotopyCategory (Mod(Y)) (up ℤ) ⥤ DMod(Y))
      RΓ[Y](V)).inv ≫
    Functor.whiskerRight
      (Functor.totalRightDerivedUnit
        (modulePushforwardToDerived f)
        (DerivedCategory.Qh : HomotopyCategory (Mod(X)) (up ℤ) ⥤ DMod(X))
        (Qis(X)))
      RΓ[Y](V) ≫
    (Functor.associator
      (DerivedCategory.Qh : HomotopyCategory (Mod(X)) (up ℤ) ⥤ DMod(X))
      R(f)_*
      RΓ[Y](V)).hom

private instance moduleSectionsAlongObjectSource_isRightDerivedFunctor
    (f : RingedSite.Hom X Y) (V : Y) :
    (RΓ[X](f.base.obj V) ⋙
      (_root_.ModuleCat.restrictScalars
        (f.structureSheafMap.1.app (op V)).hom).mapDerivedCategory).IsRightDerivedFunctor
      (moduleSectionsAlongObjectSourceNat f V)
      (Qis(X)) := by
  dsimp
  sorry

private noncomputable def modulePushforwardDerived_sectionsOverObjectComparisonHom :
    RΓ[X](f.base.obj V) ⋙
        (_root_.ModuleCat.restrictScalars
          (f.structureSheafMap.1.app (op V)).hom).mapDerivedCategory ⟶
      R(f)_* ⋙ RΓ[Y](V) :=
  Functor.rightDerivedNatTrans
    (RΓ[X](f.base.obj V) ⋙
      (_root_.ModuleCat.restrictScalars
        (f.structureSheafMap.1.app (op V)).hom).mapDerivedCategory)
    (R(f)_* ⋙ RΓ[Y](V))
    (moduleSectionsAlongObjectSourceNat f V)
    (moduleSectionsAlongObjectTargetNat f V)
    (Qis(X))
    (𝟙 _)

/-- Lemma 21.20.5 (2): the canonical comparison from `RΓ[X](f.base.obj V)`, followed by
derived restriction of scalars along
`f.structureSheafMap.1.app (op V) : Γ(V, 𝒪_Y) ⟶ Γ(f(V), 𝒪_X)`, to `R(f)_* ⋙ RΓ[Y](V)` is an
isomorphism. -/
@[stacks 0D6H]
instance modulePushforwardDerived_sectionsOverObjectComparison :
    IsIso
      (Functor.rightDerivedNatTrans
        (RΓ[X](f.base.obj V) ⋙
          (_root_.ModuleCat.restrictScalars
            (f.structureSheafMap.1.app (op V)).hom).mapDerivedCategory)
        (R(f)_* ⋙ RΓ[Y](V))
        (moduleSectionsAlongObjectSourceNat f V)
        (moduleSectionsAlongObjectTargetNat f V)
        (Qis(X))
        (𝟙 _)) := by
  change IsIso (modulePushforwardDerived_sectionsOverObjectComparisonHom f V)
  sorry

/-- Lemma 21.20.5 (2), theorem-form companion to
`modulePushforwardDerived_sectionsOverObjectComparison`. -/
@[stacks 0D6H]
theorem modulePushforwardDerived_sectionsOverObjectComparison_isIso :
    IsIso
      (Functor.rightDerivedNatTrans
        (RΓ[X](f.base.obj V) ⋙
          (_root_.ModuleCat.restrictScalars
            (f.structureSheafMap.1.app (op V)).hom).mapDerivedCategory)
        (R(f)_* ⋙ RΓ[Y](V))
        (moduleSectionsAlongObjectSourceNat f V)
        (moduleSectionsAlongObjectTargetNat f V)
        (Qis(X))
        (𝟙 _)) := by
  infer_instance

/-- Lemma 21.20.5 (2), objectwise companion: the canonical comparison morphism on `K` is an
isomorphism. -/
@[stacks 0D6H]
theorem modulePushforwardDerived_sectionsOverObjectComparison_app_isIso
    (K : DMod(X)) :
    IsIso
      ((Functor.rightDerivedNatTrans
          (RΓ[X](f.base.obj V) ⋙
            (_root_.ModuleCat.restrictScalars
              (f.structureSheafMap.1.app (op V)).hom).mapDerivedCategory)
          (R(f)_* ⋙ RΓ[Y](V))
          (moduleSectionsAlongObjectSourceNat f V)
          (moduleSectionsAlongObjectTargetNat f V)
          (Qis(X))
          (𝟙 _)).app K) := by
  change IsIso ((modulePushforwardDerived_sectionsOverObjectComparisonHom f V).app K)
  let _ : IsIso (modulePushforwardDerived_sectionsOverObjectComparisonHom f V) := by
    change IsIso
      (Functor.rightDerivedNatTrans
        (RΓ[X](f.base.obj V) ⋙
          (_root_.ModuleCat.restrictScalars
            (f.structureSheafMap.1.app (op V)).hom).mapDerivedCategory)
        (R(f)_* ⋙ RΓ[Y](V))
        (moduleSectionsAlongObjectSourceNat f V)
        (moduleSectionsAlongObjectTargetNat f V)
        (Qis(X))
        (𝟙 _))
    infer_instance
  infer_instance

end

end RingedSite.Hom
