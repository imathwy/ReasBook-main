import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import stacks_project.Chap21.Remark_21_14_4

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open Opposite

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard
set_option checkBinderAnnotations false

namespace RingedSite.Hom

/-- The abelian category of sheaves of modules on the ringed site `X`. -/
abbrev ModuleCat (X : RingedSite.{u, v}) :=
  SheafOfModules X.structureSheaf

/-- The unbounded derived category `D(\mathcal O_X)` of module sheaves on `X`. -/
abbrev ModuleDerived (X : RingedSite.{u, v}) :=
  DerivedCategory (ModuleCat X)

/-- The homotopy-to-derived functor induced by pushforward on module sheaves. -/
abbrev modulePushforwardToDerived {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [f.modulePushforward.Additive] :
    HomotopyCategory (ModuleCat X) (up ℤ) ⥤ ModuleDerived Y :=
  mapHomotopyCategoryToDerived f.modulePushforward

/-- The unbounded derived direct-image functor `Rf_*` on module sheaves. -/
noncomputable abbrev modulePushforwardDerived {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [f.modulePushforward.Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)] :
    ModuleDerived X ⥤ ModuleDerived Y :=
  Functor.totalRightDerived (modulePushforwardToDerived f)
    (DerivedCategory.Qh : HomotopyCategory (ModuleCat X) (up ℤ) ⥤ ModuleDerived X)
    (ModuleQis X)

/-- The complex-level global-sections functor on `\mathcal O_X`-modules, viewed on underlying
abelian groups. -/
abbrev moduleGlobalSectionsToDerived (X : RingedSite.{u, v})
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{max u v}]
    [(moduleGlobalSectionsFunctor X).Additive] :
    HomotopyCategory (ModuleCat X) (up ℤ) ⥤ DerivedCategory AddCommGrpCat.{max u v} :=
  mapHomotopyCategoryToDerived (moduleGlobalSectionsFunctor X)

/-- The chosen unbounded derived global-sections functor on a ringed site, formalized on
underlying additive groups. -/
noncomputable abbrev moduleGlobalSectionsDerived (X : RingedSite.{u, v})
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{max u v}]
    [(moduleGlobalSectionsFunctor X).Additive]
    [Functor.HasRightDerivedFunctor (moduleGlobalSectionsToDerived X) (ModuleQis X)] :
    ModuleDerived X ⥤ DerivedCategory AddCommGrpCat.{max u v} :=
  Functor.totalRightDerived (moduleGlobalSectionsToDerived X)
    (DerivedCategory.Qh : HomotopyCategory (ModuleCat X) (up ℤ) ⥤ ModuleDerived X)
    (ModuleQis X)

/-- The ring of sections `\Gamma(U, \mathcal O_X)` on an object `U` of the ringed site `X`. -/
abbrev sectionsRingOnObject (X : RingedSite.{u, v}) (U : X) : RingCat.{max u v} :=
  X.structureSheaf.1.obj (op U)

/-- The sections functor `\Gamma(U,-)` on `\mathcal O_X`-modules over the fixed object `U`. -/
abbrev moduleSectionsFunctorAtObject (X : RingedSite.{u, v}) (U : X) :
    ModuleCat X ⥤ _root_.ModuleCat (sectionsRingOnObject X U) :=
  SheafOfModules.evaluation X.structureSheaf (op U)

/-- The map on section rings induced by a morphism of ringed sites at an object `V` of the target.
-/
abbrev sectionsMapOnObject {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y) (V : Y) :
    sectionsRingOnObject Y V ⟶ sectionsRingOnObject X (f.base.obj V) :=
  f.structureSheafMap.1.app (op V)

/-- Restriction of scalars along the map
`\Gamma(V, \mathcal O_Y) \to \Gamma(f(V), \mathcal O_X)`. -/
abbrev moduleSectionsRestrictionFunctor {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    (V : Y) :
    _root_.ModuleCat (sectionsRingOnObject X (f.base.obj V)) ⥤
      _root_.ModuleCat (sectionsRingOnObject Y V) :=
  _root_.ModuleCat.restrictScalars (sectionsMapOnObject f V).hom

/-- The complex-level sections functor over a fixed object of a ringed site. -/
abbrev moduleSectionsToDerived (X : RingedSite.{u, v}) (U : X)
    [(moduleSectionsFunctorAtObject X U).Additive] :
    HomotopyCategory (ModuleCat X) (up ℤ) ⥤
      DerivedCategory (_root_.ModuleCat (sectionsRingOnObject X U)) :=
  mapHomotopyCategoryToDerived (moduleSectionsFunctorAtObject X U)

/-- The chosen unbounded derived sections functor `R\Gamma(U,-)` on `D(\mathcal O_X)`. -/
noncomputable abbrev moduleSectionsDerived (X : RingedSite.{u, v}) (U : X)
    [(moduleSectionsFunctorAtObject X U).Additive]
    [Functor.HasRightDerivedFunctor (moduleSectionsToDerived X U) (ModuleQis X)] :
    ModuleDerived X ⥤ DerivedCategory (_root_.ModuleCat (sectionsRingOnObject X U)) :=
  Functor.totalRightDerived (moduleSectionsToDerived X U)
    (DerivedCategory.Qh : HomotopyCategory (ModuleCat X) (up ℤ) ⥤ ModuleDerived X)
    (ModuleQis X)

/-- The derived restriction-of-scalars functor on section rings attached to `f` and `V`. -/
abbrev moduleSectionsRestrictionDerived {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    (V : Y)
    [(moduleSectionsRestrictionFunctor f V).Additive]
    [PreservesFiniteLimits (moduleSectionsRestrictionFunctor f V)]
    [PreservesFiniteColimits (moduleSectionsRestrictionFunctor f V)] :
    DerivedCategory (_root_.ModuleCat (sectionsRingOnObject X (f.base.obj V))) ⥤
      DerivedCategory (_root_.ModuleCat (sectionsRingOnObject Y V)) :=
  Functor.mapDerivedCategory (moduleSectionsRestrictionFunctor f V)

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)

variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{max u v}]
variable [HasWeakSheafify Y.siteTopology AddCommGrpCat.{max u v}]
variable [HasGlobalSectionsFunctor Y.siteTopology AddCommGrpCat.{max u v}]

variable [f.modulePushforward.Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]

variable [(moduleGlobalSectionsFunctor X).Additive]
variable [(moduleGlobalSectionsFunctor Y).Additive]
variable [Functor.HasRightDerivedFunctor (moduleGlobalSectionsToDerived X) (ModuleQis X)]
variable [Functor.HasRightDerivedFunctor (moduleGlobalSectionsToDerived Y) (ModuleQis Y)]

-- Proof sketch: let `g : Y ⟶ pt` be the canonical morphism to the punctual ringed topos whose
-- structure sheaf is `Γ(Y, \mathcal O_Y)`. Then `RΓ(Y,-)` is the derived pushforward `Rg_*`.
-- Apply Lemma `21.19.2` to the composite `X ⟶ Y ⟶ pt`, and use the identification of the
-- composite pushforward with global sections. This formalization records the resulting objectwise
-- isomorphism after forgetting to underlying additive groups.
/-- Lemma 21.20.5 (1): after forgetting the natural module structure to underlying abelian groups,
derived global sections on `Y` applied to `Rf_* K` are isomorphic to derived global sections on
`X` applied to `K`. This is the objectwise form of
`R\Gamma(\mathcal D,-) \circ Rf_* = R\Gamma(\mathcal C,-)`. -/
theorem modulePushforwardDerived_globalSections_isIsomorphic
    (K : ModuleDerived X) :
    IsIsomorphic
      ((moduleGlobalSectionsDerived Y).obj ((modulePushforwardDerived f).obj K))
      ((moduleGlobalSectionsDerived X).obj K) := sorry

variable (V : Y)

variable [(moduleSectionsFunctorAtObject X (f.base.obj V)).Additive]
variable [(moduleSectionsFunctorAtObject Y V).Additive]
variable [Functor.HasRightDerivedFunctor
  (moduleSectionsToDerived X (f.base.obj V)) (ModuleQis X)]
variable [Functor.HasRightDerivedFunctor (moduleSectionsToDerived Y V) (ModuleQis Y)]
variable [(moduleSectionsRestrictionFunctor f V).Additive]
variable [PreservesFiniteLimits (moduleSectionsRestrictionFunctor f V)]
variable [PreservesFiniteColimits (moduleSectionsRestrictionFunctor f V)]

-- Proof sketch: identify `RΓ(U,-)` with derived global sections on the localized ringed site
-- `X/U` via Lemma `21.20.2`, identify `RΓ(V,-)` with derived global sections on `Y/V`, and then
-- use Lemma `21.20.4` to commute localized restriction with `Rf_*`. The resulting comparison is
-- expressed in the target ring `Γ(V, \mathcal O_Y)` by explicit restriction of scalars along
-- `Γ(V, \mathcal O_Y) → Γ(U, \mathcal O_X)`.
/-- Lemma 21.20.5 (2): for `V : Y` and `U = f(V)`, derived sections over `U` on `X`, viewed in
`D(\Gamma(V,\mathcal O_Y))` by restriction of scalars along
`\Gamma(V,\mathcal O_Y) \to \Gamma(U,\mathcal O_X)`, are isomorphic to derived sections over `V`
of `Rf_* K`. This is the objectwise form of
`R\Gamma(U,-) = R\Gamma(V,-) \circ Rf_*`. -/
theorem modulePushforwardDerived_sectionsOverObject_isIsomorphic
    (K : ModuleDerived X) :
    IsIsomorphic
      ((moduleSectionsRestrictionDerived f V).obj
        ((moduleSectionsDerived X (f.base.obj V)).obj K))
      ((moduleSectionsDerived Y V).obj ((modulePushforwardDerived f).obj K)) := sorry

end

end RingedSite.Hom
