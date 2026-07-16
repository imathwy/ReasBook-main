import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import StacksProject_2024.stacks_project.Chap18.Definition_18_13_1
import StacksProject_2024.stacks_project.Chap18.Definition_18_19_1
import StacksProject_2024.stacks_project.Chap18.RingedSiteModuleCategory
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open scoped RingedSite.Hom

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard
set_option checkBinderAnnotations false

namespace RingedSite.Hom

/-- The abelian category of sheaves of modules on the ringed site `X`. -/
abbrev ModuleCat (X : RingedSite.{u, v}) :=
  _root_.SheafOfModules.{max u v} X.structureSheaf

instance moduleCatAbelian (X : RingedSite.{u, v}) :
    Abelian (ModuleCat X) :=
  SheafOfModules.instAbelian X.structureSheaf

instance localizedModuleCatAbelian (X : RingedSite.{u, v}) (U : X) :
    Abelian (ModuleCat (X.localization U)) :=
  moduleCatAbelian (X.localization U)

/-- Restriction of `\mathcal O_X`-modules from a ringed site `X` to the localized ringed site
`(X/U, \mathcal O_U)`. -/
abbrev localizedRestriction (X : RingedSite.{u, v}) (U : X)
    [HasBinaryProducts X.carrier] :
    ModuleCat X ⥤ ModuleCat (X.localization U) :=
  show ModuleCat X ⥤ SheafOfModules (X.structureSheaf.over U) from
    _root_.SheafOfModules.pushforward (𝟙 (X.structureSheaf.over U))

instance localizedRestriction_additive
    (X : RingedSite.{u, v}) (U : X)
    [HasBinaryProducts X.carrier]
    [Abelian (ModuleCat X)] [Abelian (ModuleCat (X.localization U))] :
    (localizedRestriction X U).Additive := by
  refine ⟨?_⟩
  intro M N f g
  ext V x
  rfl

instance localizedRestriction_preservesZeroMorphisms
    (X : RingedSite.{u, v}) (U : X)
    [HasBinaryProducts X.carrier] :
    (localizedRestriction X U).PreservesZeroMorphisms := by
  exact Functor.preservesZeroMorphisms_of_additive (localizedRestriction X U)

/-- The induced functor on cochain complexes of module sheaves for restriction to the localized
ringed site `(X/U, \mathcal O_U)`. -/
abbrev localizedRestrictionComplex
    (X : RingedSite.{u, v}) (U : X)
    [HasBinaryProducts X.carrier] :
    CochainComplex (ModuleCat X) ℤ ⥤ CochainComplex (ModuleCat (X.localization U)) ℤ :=
  (localizedRestriction X U).mapHomologicalComplex (up ℤ)

/-- The unbounded derived category `D(\mathcal O_X)` of module sheaves on `X`. -/
abbrev ModuleDerived (X : RingedSite.{u, v}) :=
  DerivedCategory (ModuleCat X)

local instance moduleCat_hasDerivedCategory (X : RingedSite.{u, v}) :
    HasDerivedCategory (ModuleCat X) :=
  HasDerivedCategory.standard (ModuleCat X)

/-- The class of quasi-isomorphisms used to localize the homotopy category of module sheaves on
`X`. -/
abbrev ModuleQis (X : RingedSite.{u, v}) [CategoryWithHomology (ModuleCat X)] :=
  HomotopyCategory.quasiIso (ModuleCat X) (up ℤ)

/-- The functor on homotopy categories induced by direct image on module sheaves. -/
abbrev modulePushforwardToDerived {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [CategoryWithHomology (ModuleCat X)]
    [CategoryWithHomology (ModuleCat Y)]
    [(pushforward f).Additive] :=
  (pushforward f).mapHomotopyCategory (up ℤ) ⋙
    (show HomotopyCategory (ModuleCat Y) (up ℤ) ⥤ ModuleDerived Y from
      DerivedCategory.Qh)

/-- The unbounded right derived direct-image functor on module sheaves. -/
noncomputable abbrev modulePushforwardDerived {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [CategoryWithHomology (ModuleCat X)]
    [CategoryWithHomology (ModuleCat Y)]
    [(pushforward f).Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)] :
    ModuleDerived X ⥤ ModuleDerived Y :=
  Functor.totalRightDerived (modulePushforwardToDerived f)
    (show HomotopyCategory (ModuleCat X) (up ℤ) ⥤ ModuleDerived X from
      DerivedCategory.Qh)
    (ModuleQis X)

/-- The functor on homotopy categories induced by pullback on module sheaves. -/
abbrev modulePullbackToDerived {X Y : RingedSite.{u, v}} (f : X ⟶ Y)
    [CategoryWithHomology (ModuleCat X)]
    [CategoryWithHomology (ModuleCat Y)]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [(PresheafOfModules.pushforward.{max u v} f.structureSheafMap.hom).IsRightAdjoint]
    [Functor.Additive (SheafOfModules.pullback.{max u v} f.structureSheafMap)] :
    HomotopyCategory (ModuleCat Y) (up ℤ) ⥤ ModuleDerived X :=
  (SheafOfModules.pullback.{max u v} f.structureSheafMap).mapHomotopyCategory (up ℤ) ⋙
    (show HomotopyCategory (ModuleCat X) (up ℤ) ⥤ ModuleDerived X from
      DerivedCategory.Qh)

/-- The unbounded left derived pullback functor on module sheaves. -/
noncomputable abbrev modulePullbackDerived {X Y : RingedSite.{u, v}} (f : X ⟶ Y)
    [CategoryWithHomology (ModuleCat X)]
    [CategoryWithHomology (ModuleCat Y)]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [(PresheafOfModules.pushforward.{max u v} f.structureSheafMap.hom).IsRightAdjoint]
    [Functor.Additive (SheafOfModules.pullback.{max u v} f.structureSheafMap)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)] :
    ModuleDerived Y ⥤ ModuleDerived X :=
  Functor.totalLeftDerived (modulePullbackToDerived f)
    (show HomotopyCategory (ModuleCat Y) (up ℤ) ⥤ ModuleDerived Y from
      DerivedCategory.Qh)
    (ModuleQis Y)

end RingedSite.Hom

namespace RingedSiteDerived

/- Lean surface notation for the unbounded derived pushforward functor `Rf_*`. -/
scoped[RingedSiteDerived] notation:max "R(" f:max ")_*" =>
  RingedSite.Hom.modulePushforwardDerived f

/- Lean surface notation for the unbounded derived pullback functor `Lf^*`. -/
scoped[RingedSiteDerived] notation:max "L(" f:max ")" "^*" =>
  RingedSite.Hom.modulePullbackDerived f

end RingedSiteDerived
