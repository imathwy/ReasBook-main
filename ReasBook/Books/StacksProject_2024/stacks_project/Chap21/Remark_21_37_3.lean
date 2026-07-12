import Mathlib.CategoryTheory.Adjunction.Mates
import StacksProject_2024.Chap18.Lemma_18_15_3
import StacksProject_2024.Chap21.SiteAbelianDerived
import StacksProject_2024.Chap21.Lemma_21_37_1
import StacksProject_2024.Chap21.Lemma_21_20_7

open CategoryTheory
open CategoryTheory.Limits
open RingedSite.Hom

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace CategoryTheory

private instance sheafPushforward_mapHomotopyCategoryToDerived_hasRightDerivedFunctor
    {C : Type u} [Category.{u} C]
    {D : Type u} [Category.{u} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    (u : C ⥤ D) [Functor.IsContinuous u JC JD] [Functor.IsCocontinuous u JC JD]
    [HasWeakSheafify JC AddCommGrpCat.{u}]
    [HasWeakSheafify JD AddCommGrpCat.{u}]
    [HasSheafify JC AddCommGrpCat.{u}]
    [HasSheafify JD AddCommGrpCat.{u}]
    [Functor.Additive (u.sheafPushforwardContinuous AddCommGrpCat.{u} JC JD)]
    [IsGrothendieckAbelian.{u} (SiteAbelianSheafCat JD)] :
    Functor.HasRightDerivedFunctor
      (mapHomotopyCategoryToDerived (u.sheafPushforwardContinuous AddCommGrpCat.{u} JC JD))
      (HomotopyCategory.quasiIso (SiteAbelianSheafCat JD) (ComplexShape.up ℤ)) := by
  let F : SiteAbelianSheafCat JD ⥤ SiteAbelianSheafCat JC :=
    u.sheafPushforwardContinuous AddCommGrpCat.{u} JC JD
  let _ : F.Additive := inferInstance
  change Functor.HasRightDerivedFunctor (mapHomotopyCategoryToDerived F)
    (HomotopyCategory.quasiIso (SiteAbelianSheafCat JD) (ComplexShape.up ℤ))
  refine hasRightDerivedFunctor_of_kInjective_resolutions (mapHomotopyCategoryToDerived F) ?_
  intro K
  obtain ⟨J, _, hKinj⟩ := CochainComplex.exists_functorial_kInjective_resolution
    (SiteAbelianSheafCat JD)
  exact ⟨J.toFunctor.obj K, hKinj K, J.ι.app K, J.quasiIso_app K⟩

section

variable {C : Type u} [Category.{u} C]
variable {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable (u : C ⥤ D) [Functor.IsContinuous u JC JD] [Functor.IsCocontinuous u JC JD]
variable (𝒪D : Sheaf JD RingCat.{u})

local notation "XD" => RingedSite.ofRingSheaf JD 𝒪D
local notation "XC" => RingedSite.ofRingSheaf JC (inverseImageRingSheaf JC JD u 𝒪D)

/- Domain-style sampling for Remark 21.37.3:
- primary domain: derived inverse image for sheaves of modules and abelian sheaves on sites,
  compared after forgetting module structure to the derived category of abelian sheaves;
- sampled owner declarations:
  `modulePushforwardDerived`,
  `siteAbelianInverseImageDerived`,
  `Functor.mapDerivedCategory`,
  `mateEquiv`;
- best owner abstraction: this remark is a `bridge/view` item. Its mathematical content is the
  comparison morphism between the left adjoints of the canonical derived inverse-image owners;
- primitive data: the continuous and cocontinuous functor of sites `u`, the sheaf of rings
  `𝒪D`, the canonical derived inverse-image owners
  `modulePushforwardDerived (moduleInverseImageHom JC JD u 𝒪D)` and
  `siteAbelianInverseImageDerived JC JD u`, together with the exact abelian pushforward
  `(u.sheafPushforwardContinuous AddCommGrpCat.{u} JC JD).mapDerivedCategory` used only as an
  internal bridge and the derived forgetful functors on the source and target ringed sites;
- derived API: the mate of the specialized right-side square, whose underlying natural
  transformation is the canonical lower-shriek/forget comparison
  `Lg_!^{Ab} \circ forget ⟶ forget \circ Lg_!`.

Source/core/bridge triage:
- `source-facing`: Remark `21.37.3`, asserting the existence of the comparison morphism
  `Lg_!^{Ab} \circ forget ⟶ forget \circ Lg_!`;
- `core/canonical`: `modulePushforwardDerived`, `siteAbelianInverseImageDerived`, and
  `Functor.leftAdjoint`;
- `bridge/view`: the mate construction specialized to the right-side inverse-image/forget square,
  with the exact-functor owner
  `(u.sheafPushforwardContinuous AddCommGrpCat.{u} JC JD).mapDerivedCategory` used only to
  identify the homotopy right-derived model with the canonical owner
  `siteAbelianInverseImageDerived`.
-/

variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [HasWeakSheafify JD AddCommGrpCat.{u}]
variable [HasSheafify JC AddCommGrpCat.{u}]
variable [HasSheafify JD AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [Functor.Additive (u.sheafPushforwardContinuous AddCommGrpCat.{u} JC JD)]
variable [Functor.Additive ((moduleInverseImageHom JC JD u 𝒪D).modulePushforward)]
variable [IsGrothendieckAbelian.{u} (SiteAbelianSheafCat JD)]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived (moduleInverseImageHom JC JD u 𝒪D))
  (ModuleQis (RingedSite.ofRingSheaf JD 𝒪D))]

private local instance : Abelian (ModuleCat XD) := SheafOfModules.instAbelian 𝒪D
private local instance : Abelian (ModuleCat XC) :=
  SheafOfModules.instAbelian (inverseImageRingSheaf JC JD u 𝒪D)

local notation "forgetModD" =>
  (Functor.mapDerivedCategory (underlyingAbelianSheafFunctor XD) :
    ModuleDerived XD ⥤ DerivedCategory (SiteAbelianSheafCat JD))
local notation "forgetModC" =>
  (Functor.mapDerivedCategory (underlyingAbelianSheafFunctor XC) :
    ModuleDerived XC ⥤ DerivedCategory (SiteAbelianSheafCat JC))
local notation "QisAb" =>
  HomologicalComplex.quasiIso (SiteAbelianSheafCat JD) (ComplexShape.up ℤ)
local notation "QishAb" =>
  HomotopyCategory.quasiIso (SiteAbelianSheafCat JD) (ComplexShape.up ℤ)
local notation "g" => moduleInverseImageHom JC JD u 𝒪D

private noncomputable abbrev pushAbDerived :
    DerivedCategory (SiteAbelianSheafCat JD) ⥤
      DerivedCategory (SiteAbelianSheafCat JC) :=
  let F : SiteAbelianSheafCat JD ⥤ SiteAbelianSheafCat JC :=
    u.sheafPushforwardContinuous AddCommGrpCat.{u} JC JD
  let hExact :
      exactFunctor (SiteAbelianSheafCat JD) (SiteAbelianSheafCat JC) F :=
    Functor.sheafPushforwardContinuous_exact_of_isAlmostCocontinuous u
  letI : PreservesFiniteLimits F := (CategoryTheory.exactFunctor_iff F).1 hExact |>.1
  letI : PreservesFiniteColimits F := (CategoryTheory.exactFunctor_iff F).1 hExact |>.2
  F.mapDerivedCategory

variable [Functor.IsRightAdjoint
  (modulePushforwardDerived (moduleInverseImageHom JC JD u 𝒪D))]
variable [Functor.IsRightAdjoint (siteAbelianInverseImageDerived JC JD u)]

private noncomputable def siteAbelianInverseImageDerived_toMapDerivedCategory :
    siteAbelianInverseImageDerived JC JD u ≅ pushAbDerived u := by
  let pushAb : SiteAbelianSheafCat JD ⥤ SiteAbelianSheafCat JC :=
    u.sheafPushforwardContinuous AddCommGrpCat.{u} JC JD
  let hExact :
      exactFunctor (SiteAbelianSheafCat JD) (SiteAbelianSheafCat JC) pushAb :=
    Functor.sheafPushforwardContinuous_exact_of_isAlmostCocontinuous u
  letI : PreservesFiniteLimits pushAb := (CategoryTheory.exactFunctor_iff pushAb).1 hExact |>.1
  letI : PreservesFiniteColimits pushAb := (CategoryTheory.exactFunctor_iff pushAb).1 hExact |>.2
  letI :
      (pushAb.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).HasRightDerivedFunctor
        QisAb :=
    CategoryTheory.mapHomologicalComplexQ_hasRightDerivedFunctor pushAb
  letI : pushAb.mapDerivedCategory.IsRightDerivedFunctor pushAb.mapDerivedCategoryFactors.inv QisAb :=
    by
      simpa using
        (Functor.isRightDerivedFunctor_of_inverts
          QisAb
          pushAb.mapDerivedCategory
          pushAb.mapDerivedCategoryFactors)
  let F :
      DerivedCategory (SiteAbelianSheafCat JD) ⥤
        DerivedCategory (SiteAbelianSheafCat JC) :=
    siteAbelianInverseImageDerived JC JD u
  exact
    F.rightDerivedUnique
      (pushAbDerived u)
      (show
        pushAb.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
          DerivedCategory.Q ⋙ siteAbelianInverseImageDerived JC JD u
       from
        Functor.totalRightDerivedUnit
          (pushAb.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
          DerivedCategory.Q
          QisAb)
      (show
        pushAb.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
          DerivedCategory.Q ⋙ pushAbDerived u
       from
        pushAb.mapDerivedCategoryFactors.inv)
      QisAb

private noncomputable def pushAbRightDerived_toMapDerivedCategory :
    Functor.totalRightDerived
        (mapHomotopyCategoryToDerived
          (u.sheafPushforwardContinuous AddCommGrpCat.{u} JC JD))
        (DerivedCategory.Qh :
          HomotopyCategory (SiteAbelianSheafCat JD) (ComplexShape.up ℤ) ⥤
            DerivedCategory (SiteAbelianSheafCat JD))
        QishAb ≅
      pushAbDerived u := by
  let pushAb : SiteAbelianSheafCat JD ⥤ SiteAbelianSheafCat JC :=
    u.sheafPushforwardContinuous AddCommGrpCat.{u} JC JD
  let hExact :
      exactFunctor (SiteAbelianSheafCat JD) (SiteAbelianSheafCat JC) pushAb :=
    Functor.sheafPushforwardContinuous_exact_of_isAlmostCocontinuous u
  letI : PreservesFiniteLimits pushAb := (CategoryTheory.exactFunctor_iff pushAb).1 hExact |>.1
  letI : PreservesFiniteColimits pushAb := (CategoryTheory.exactFunctor_iff pushAb).1 hExact |>.2
  letI : pushAb.mapDerivedCategory.IsRightDerivedFunctor pushAb.mapDerivedCategoryFactorsh.inv QishAb :=
    by
      simpa [mapHomotopyCategoryToDerived] using
        (Functor.isRightDerivedFunctor_of_inverts
          QishAb
          pushAb.mapDerivedCategory
          pushAb.mapDerivedCategoryFactorsh)
  let G :
      DerivedCategory (SiteAbelianSheafCat JD) ⥤
        DerivedCategory (SiteAbelianSheafCat JC) :=
    pushAbDerived u
  exact
    (Functor.totalRightDerived
      (mapHomotopyCategoryToDerived pushAb)
      (DerivedCategory.Qh :
        HomotopyCategory (SiteAbelianSheafCat JD) (ComplexShape.up ℤ) ⥤
          DerivedCategory (SiteAbelianSheafCat JD))
      QishAb).rightDerivedUnique
      G
      (Functor.totalRightDerivedUnit
        (mapHomotopyCategoryToDerived pushAb)
        (DerivedCategory.Qh :
          HomotopyCategory (SiteAbelianSheafCat JD) (ComplexShape.up ℤ) ⥤
            DerivedCategory (SiteAbelianSheafCat JD))
        QishAb)
      pushAb.mapDerivedCategoryFactorsh.inv
      QishAb

private noncomputable def pushAbRightDerived_toOwner :
    Functor.totalRightDerived
        (mapHomotopyCategoryToDerived
          (u.sheafPushforwardContinuous AddCommGrpCat.{u} JC JD))
        (DerivedCategory.Qh :
          HomotopyCategory (SiteAbelianSheafCat JD) (ComplexShape.up ℤ) ⥤
            DerivedCategory (SiteAbelianSheafCat JD))
        QishAb ≅
      siteAbelianInverseImageDerived JC JD u := by
  let e₁ :
      Functor.totalRightDerived
          (mapHomotopyCategoryToDerived
            (u.sheafPushforwardContinuous AddCommGrpCat.{u} JC JD))
          (DerivedCategory.Qh :
            HomotopyCategory (SiteAbelianSheafCat JD) (ComplexShape.up ℤ) ⥤
              DerivedCategory (SiteAbelianSheafCat JD))
          QishAb ≅
        pushAbDerived u :=
    pushAbRightDerived_toMapDerivedCategory u
  let e₂ : siteAbelianInverseImageDerived JC JD u ≅ pushAbDerived u :=
    siteAbelianInverseImageDerived_toMapDerivedCategory u
  exact e₁ ≪≫ e₂.symm

private abbrev inverseImageAbelianPushforwardToDerived :
    HomotopyCategory (SiteAbelianSheafCat JD) (ComplexShape.up ℤ) ⥤
      DerivedCategory (SiteAbelianSheafCat JC) :=
  mapHomotopyCategoryToDerived
    (u.sheafPushforwardContinuous AddCommGrpCat.{u} JC JD)

private noncomputable def abelianPushforwardDerived_toOwner :
    abelianPushforwardDerived g ≅ siteAbelianInverseImageDerived JC JD u := by
  simpa [abelianPushforwardDerived, inverseImageAbelianPushforwardToDerived,
    mapHomotopyCategoryToDerived] using
    (pushAbRightDerived_toOwner u)

private noncomputable abbrev modulePushforwardDerived_underlyingAbelianComparison_toOwner :
    modulePushforwardDerived g ⋙ forgetModC ⟶
      forgetModD ⋙ siteAbelianInverseImageDerived JC JD u :=
  modulePushforwardDerived_underlyingAbelianComparison g ≫
    Functor.whiskerLeft forgetModD
      (abelianPushforwardDerived_toOwner u 𝒪D).hom

end

section

variable {C : Type u} [Category.{u} C]
variable {D : Type u} [Category.{u} D]
variable (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
variable (u : C ⥤ D) [Functor.IsContinuous u JC JD] [Functor.IsCocontinuous u JC JD]
variable (𝒪D : Sheaf JD RingCat.{u})

variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [HasWeakSheafify JD AddCommGrpCat.{u}]
variable [HasSheafify JC AddCommGrpCat.{u}]
variable [HasSheafify JD AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [Functor.Additive (u.sheafPushforwardContinuous AddCommGrpCat.{u} JC JD)]
variable [Functor.Additive ((moduleInverseImageHom JC JD u 𝒪D).modulePushforward)]
variable [IsGrothendieckAbelian.{u} (SiteAbelianSheafCat JD)]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived (moduleInverseImageHom JC JD u 𝒪D))
  (ModuleQis (RingedSite.ofRingSheaf JD 𝒪D))]
variable [Functor.IsRightAdjoint
  (modulePushforwardDerived (moduleInverseImageHom JC JD u 𝒪D))]
variable [Functor.IsRightAdjoint (siteAbelianInverseImageDerived JC JD u)]

local notation "XD" => RingedSite.ofRingSheaf JD 𝒪D
local notation "XC" => RingedSite.ofRingSheaf JC (inverseImageRingSheaf JC JD u 𝒪D)
local notation "g" => moduleInverseImageHom JC JD u 𝒪D

private local instance : Abelian (ModuleCat XD) := SheafOfModules.instAbelian 𝒪D
private local instance : Abelian (ModuleCat XC) :=
  SheafOfModules.instAbelian (inverseImageRingSheaf JC JD u 𝒪D)

local notation "forgetModD" =>
  (Functor.mapDerivedCategory (underlyingAbelianSheafFunctor XD) :
    ModuleDerived XD ⥤ DerivedCategory (SiteAbelianSheafCat JD))
local notation "forgetModC" =>
  (Functor.mapDerivedCategory (underlyingAbelianSheafFunctor XC) :
    ModuleDerived XC ⥤ DerivedCategory (SiteAbelianSheafCat JC))
local notation "LgAb" => Functor.leftAdjoint (siteAbelianInverseImageDerived JC JD u)
local notation "LgMod" => Functor.leftAdjoint (modulePushforwardDerived g)

/-- Remark 21.37.3: for a continuous and cocontinuous functor of sites
`u : C ⥤ D` and a sheaf of rings `𝒪D`, the comparison
`forgetModC ⋙ LgAb ⟶ LgMod ⋙ forgetModD` is obtained by applying `mateEquiv` directly to the
specialized right-side square on the canonical module-derived inverse image,
the canonical abelian-derived inverse image `siteAbelianInverseImageDerived JC JD u`, and the
derived forgetful functors `forgetModC` and `forgetModD`; the right-side square is built from the
canonical right-adjoint comparison between the module-derived inverse image and the forgetful
composite, followed by the canonical identification of the abelian pushforward owner with
`siteAbelianInverseImageDerived JC JD u`. -/
@[stacks 07AE]
noncomputable abbrev derivedLowerShriek_forget_comparison :
    forgetModC ⋙ LgAb ⟶ LgMod ⋙ forgetModD :=
  let square :
        TwoSquare
          (modulePushforwardDerived g)
          forgetModD
          forgetModC
          (siteAbelianInverseImageDerived JC JD u) :=
      TwoSquare.mk
        (modulePushforwardDerived g)
        forgetModD
        forgetModC
        (siteAbelianInverseImageDerived JC JD u)
        (modulePushforwardDerived_underlyingAbelianComparison_toOwner u 𝒪D)
  ((mateEquiv
        (Adjunction.ofIsRightAdjoint
          (modulePushforwardDerived g))
        (Adjunction.ofIsRightAdjoint
          (siteAbelianInverseImageDerived JC JD u))).symm
        square).natTrans

end

end CategoryTheory
