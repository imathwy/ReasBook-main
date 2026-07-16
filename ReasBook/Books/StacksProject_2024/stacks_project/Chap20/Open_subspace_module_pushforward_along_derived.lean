import StacksProject_2024.stacks_project.Chap20.Global_sections_module_owners_core
import StacksProject_2024.stacks_project.Chap20.Lemma_20_31_8
import StacksProject_2024.stacks_project.Chap20.Open_subspace_module_pushforward_core

open CategoryTheory
open TopologicalSpace
open AlgebraicGeometry
open scoped RingedSpace.Hom RingedSpaceDerivedPushforward

noncomputable section

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.mapHomologicalComplexQ_hasRightDerivedFunctor
attribute [local instance] DerivedCategory.instIsLocalizationCochainComplexIntQQuasiIsoUp

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The underived pushforward after restriction to an open subspace is additive. -/
instance modulePushforwardFromOpenAlong_additive
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) [(f _*).Additive] (U : Opens X.carrier) :
    (modulePushforwardFromOpenAlong f U).Additive := by
  simpa [modulePushforwardFromOpenAlong] using
    (inferInstance :
      (moduleRestrictionToOpen X U ⋙ modulePushforwardFromOpen U ⋙ (f _*)).Additive)

/-- The derived direct image to `Y` of an object of `D(\mathcal O_X)` after restricting it to the
open subspace `U ⊆ X`. This is the total right derived functor of the canonical underived owner
`modulePushforwardFromOpenAlong f U`.
-/
abbrev modulePushforwardFromOpenAlongDerived
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) [(f _*).Additive] (U : Opens X.carrier) :
    ModuleDerived X ⥤ ModuleDerived Y :=
  letI : IsGrothendieckAbelian.{u} (RingedSpace.Modules X) :=
    sheafModules_isGrothendieckAbelian X
  letI : Abelian (RingedSpace.Modules X) := RingedSpace.modules_abelian X
  letI : CategoryWithHomology (RingedSpace.Modules X) :=
    CategoryTheory.categoryWithHomology_of_abelian
  let hLoc :
      Functor.IsLocalization
        (DerivedCategory.Q :
          CochainComplex (RingedSpace.Modules X) ℤ ⥤
            DerivedCategory (RingedSpace.Modules X))
        (HomologicalComplex.quasiIso (RingedSpace.Modules X) (ComplexShape.up ℤ)) :=
    DerivedCategory.instIsLocalizationCochainComplexIntQQuasiIsoUp
  let F : RingedSpace.Modules X ⥤ RingedSpace.Modules Y :=
    modulePushforwardFromOpenAlong f U
  let hAdd : F.Additive :=
    modulePushforwardFromOpenAlong_additive f U
  let hDeriv :
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).HasRightDerivedFunctor
        (HomologicalComplex.quasiIso (RingedSpace.Modules X) (ComplexShape.up ℤ)) :=
    @CategoryTheory.mapHomologicalComplexQ_hasRightDerivedFunctor
      (RingedSpace.Modules X)
      (RingedSpace.Modules Y)
      _ _ _ _
      F
      hAdd
      (sheafModules_isGrothendieckAbelian X)
  @Functor.totalRightDerived _ _ _ _ _ _
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    DerivedCategory.Q
    (HomologicalComplex.quasiIso (RingedSpace.Modules X) (ComplexShape.up ℤ))
    hLoc
    hDeriv

section

variable {X Y : RingedSpace.{u}}
variable (f : X ⟶ Y)
variable [(f _*).Additive]

local notation "ModX" => RingedSpace.Modules X
local notation "ModY" => RingedSpace.Modules Y
local notation "DModX" => DerivedCategory ModX
local notation "DModY" => DerivedCategory ModY
local notation "CpxX" => CochainComplex ModX ℤ
local notation "CpxY" => CochainComplex ModY ℤ
local notation "QX" => (DerivedCategory.Q : CpxX ⥤ DModX)
local notation "QisX" => HomologicalComplex.quasiIso ModX (ComplexShape.up ℤ)
local notation "QY" => (DerivedCategory.Q : CpxY ⥤ DModY)
local notation "QisY" => HomologicalComplex.quasiIso ModY (ComplexShape.up ℤ)

local instance : Abelian ModX := RingedSpace.modules_abelian X
local instance : CategoryWithHomology ModX :=
  CategoryTheory.categoryWithHomology_of_abelian
local instance : Abelian ModY := RingedSpace.modules_abelian Y
local instance : CategoryWithHomology ModY :=
  CategoryTheory.categoryWithHomology_of_abelian
local instance :
    Functor.IsLocalization (DerivedCategory.Q : CpxX ⥤ DModX) QisX :=
  DerivedCategory.instIsLocalizationCochainComplexIntQQuasiIsoUp
local instance :
    Functor.IsLocalization (DerivedCategory.Q : CpxY ⥤ DModY) QisY :=
  DerivedCategory.instIsLocalizationCochainComplexIntQQuasiIsoUp
local instance :
    Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) QisX :=
  modulePushforwardToDerived_hasRightDerivedFunctor f

private abbrev modulePushforwardFromOpenAlongToDerived
    (U : Opens X.carrier) :
    CpxX ⥤ DModY :=
  (modulePushforwardFromOpenAlong f U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q

private theorem modulePushforwardFromOpenAlongToDerived_hasRightDerivedFunctor
    (U : Opens X.carrier) :
    (modulePushforwardFromOpenAlongToDerived f U).HasRightDerivedFunctor
      QisX := by
  simpa [modulePushforwardFromOpenAlongToDerived] using
    (@CategoryTheory.mapHomologicalComplexQ_hasRightDerivedFunctor
      ModX
      ModY
      _ _ _ _
      (modulePushforwardFromOpenAlong f U)
      (modulePushforwardFromOpenAlong_additive f U)
      (sheafModules_isGrothendieckAbelian X))

attribute [local instance] modulePushforwardFromOpenAlongToDerived_hasRightDerivedFunctor

private abbrev modulePushforwardFromOpenAlongDerivedUnit
    (U : Opens X.carrier) :
    modulePushforwardFromOpenAlongToDerived f U ⟶
      QX ⋙ modulePushforwardFromOpenAlongDerived f U := by
  let hLocX :
      Functor.IsLocalization (DerivedCategory.Q : CpxX ⥤ DModX) QisX :=
    DerivedCategory.instIsLocalizationCochainComplexIntQQuasiIsoUp
  let hDerivF :
      Functor.HasRightDerivedFunctor (modulePushforwardFromOpenAlongToDerived f U) QisX :=
    modulePushforwardFromOpenAlongToDerived_hasRightDerivedFunctor (f := f) U
  dsimp [modulePushforwardFromOpenAlongDerived, modulePushforwardFromOpenAlongToDerived]
  exact
    @Functor.totalRightDerivedUnit _ _ _ _ _ _
      (modulePushforwardFromOpenAlongToDerived f U)
      (DerivedCategory.Q : CpxX ⥤ DModX)
      QisX
      hLocX
      hDerivF

instance moduleDerivedPushforward_isRightDerivedFunctor :
    @Functor.IsRightDerivedFunctor
      CpxX
      DModX
      DModY
      _
      _
      _
      (R(f)_*)
      (modulePushforwardToDerived f)
      (DerivedCategory.Q : CpxX ⥤ DModX)
      (moduleDerivedPushforwardUnit (f := f))
      QisX
      DerivedCategory.instIsLocalizationCochainComplexIntQQuasiIsoUp := by
  sorry

private theorem modulePushforwardFromOpenAlongDerived_isRightDerivedFunctor
    (U : Opens X.carrier) :
    @Functor.IsRightDerivedFunctor
      CpxX
      DModX
      DModY
      _
      _
      _
      (modulePushforwardFromOpenAlongDerived f U)
      (modulePushforwardFromOpenAlongToDerived f U)
      (DerivedCategory.Q : CpxX ⥤ DModX)
      (modulePushforwardFromOpenAlongDerivedUnit (f := f) U)
      QisX
      DerivedCategory.instIsLocalizationCochainComplexIntQQuasiIsoUp := by
  sorry

/-- The canonical derived restriction natural transformation
`R(f)_* ⟶ modulePushforwardFromOpenAlongDerived f U`. -/
noncomputable def modulePushforwardFromOpenAlongDerivedUnitNatTrans
    (U : Opens X.carrier) :
    R(f)_* ⟶ modulePushforwardFromOpenAlongDerived f U :=
  letI : Functor.IsLocalization (DerivedCategory.Q : CpxX ⥤ DModX) QisX :=
    DerivedCategory.instIsLocalizationCochainComplexIntQQuasiIsoUp
  @CategoryTheory.Functor.rightDerivedNatTrans
    CpxX
    DModX
    DModY
    _
    _
    _
    (R(f)_*)
    (modulePushforwardFromOpenAlongDerived f U)
    (modulePushforwardToDerived f)
    (modulePushforwardFromOpenAlongToDerived f U)
    (DerivedCategory.Q : CpxX ⥤ DModX)
    (moduleDerivedPushforwardUnit (f := f))
    (modulePushforwardFromOpenAlongDerivedUnit (f := f) U)
    QisX
    DerivedCategory.instIsLocalizationCochainComplexIntQQuasiIsoUp
    (moduleDerivedPushforward_isRightDerivedFunctor (f := f))
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex
        (modulePushforwardFromOpenAlongUnitNatTrans (f := f) U)
        (ComplexShape.up ℤ))
      DerivedCategory.Q)

/-- The canonical derived restriction map induced by an inclusion `W ⊆ U`. -/
noncomputable def modulePushforwardFromOpenAlongDerivedRestrictionNatTrans
    {W U : Opens X.carrier} (h : W ≤ U) :
    modulePushforwardFromOpenAlongDerived f U ⟶
      modulePushforwardFromOpenAlongDerived f W :=
  letI : Functor.IsLocalization (DerivedCategory.Q : CpxX ⥤ DModX) QisX :=
    DerivedCategory.instIsLocalizationCochainComplexIntQQuasiIsoUp
  @CategoryTheory.Functor.rightDerivedNatTrans
    CpxX
    DModX
    DModY
    _
    _
    _
    (modulePushforwardFromOpenAlongDerived f U)
    (modulePushforwardFromOpenAlongDerived f W)
    (modulePushforwardFromOpenAlongToDerived f U)
    (modulePushforwardFromOpenAlongToDerived f W)
    (DerivedCategory.Q : CpxX ⥤ DModX)
    (modulePushforwardFromOpenAlongDerivedUnit (f := f) U)
    (modulePushforwardFromOpenAlongDerivedUnit (f := f) W)
    QisX
    DerivedCategory.instIsLocalizationCochainComplexIntQQuasiIsoUp
    (modulePushforwardFromOpenAlongDerived_isRightDerivedFunctor (f := f) (U := U))
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex
        (modulePushforwardFromOpenAlongRestrictionNatTrans (f := f) h)
        (ComplexShape.up ℤ))
      DerivedCategory.Q)

end

end AlgebraicGeometry.RingedSpace
