import Mathlib
import StacksProject_2024.Chap19.Lemma_19_13_6
import StacksProject_2024.Chap20.«20_14_1_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/-- The abelian category of sheaves of abelian groups on the underlying topological space of a
ringed space. -/
abbrev AbelianSheafCat (X : RingedSpace.{u}) :=
  Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}

/-- The forgetful functor from `\mathcal O_X`-modules to their underlying abelian sheaves. -/
abbrev underlyingAbelianSheafFunctor (X : RingedSpace.{u}) :
    (RingedSpace.Modules X) ⥤ AbelianSheafCat X :=
  SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)

/-- The derived functor sending a derived `\mathcal O_X`-module to its underlying derived abelian
sheaf. -/
abbrev underlyingAbelianSheafDerived (X : RingedSpace.{u})
    [IsGrothendieckAbelian.{u} (RingedSpace.Modules X)] :
    DerivedCategory (RingedSpace.Modules X) ⥤ DerivedCategory (AbelianSheafCat X) :=
  CategoryTheory.additiveFunctorTotalRightDerived (underlyingAbelianSheafFunctor X)

/-- The underived sections functor `\Gamma(U,-)` on `\mathcal O_X`-modules, viewed in abelian
groups. -/
abbrev moduleSectionsAsAbelianFunctor (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (RingedSpace.Modules X) ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X) ⋙
    sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} ⋙
      (evaluation (Opens X.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op U)

/-- The derived sections functor `R\Gamma(U,-)` on `D(\mathcal O_X)`, viewed in
`D(\operatorname{Ab})`. -/
abbrev moduleSectionsAsAbelianDerived (X : RingedSpace.{u}) (U : Opens X.carrier)
    [(moduleSectionsAsAbelianFunctor X U).Additive]
    [IsGrothendieckAbelian.{u} (RingedSpace.Modules X)] :
    DerivedCategory (RingedSpace.Modules X) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  CategoryTheory.additiveFunctorTotalRightDerived (moduleSectionsAsAbelianFunctor X U)

/-- The underived sections functor `\Gamma(U,-)` on abelian sheaves over the underlying space of
`X`. -/
abbrev abelianSectionsFunctor (X : RingedSpace.{u}) (U : Opens X.carrier) :
    AbelianSheafCat X ⥤ AddCommGrpCat.{u} :=
  sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} ⋙
    (evaluation (Opens X.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op U)

/-- The derived sections functor `R\Gamma(U,-)` on derived abelian sheaves over the underlying
space of `X`. -/
abbrev abelianSectionsDerived (X : RingedSpace.{u}) (U : Opens X.carrier)
    [(abelianSectionsFunctor X U).Additive]
    [IsGrothendieckAbelian.{u} (AbelianSheafCat X)] :
    DerivedCategory (AbelianSheafCat X) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  CategoryTheory.additiveFunctorTotalRightDerived (abelianSectionsFunctor X U)

/-- The direct-image functor on abelian sheaves induced by a morphism of ringed spaces. -/
abbrev abelianPushforwardFunctor {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    AbelianSheafCat X ⥤ AbelianSheafCat Y :=
  TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.hom.base

/-- The derived direct-image functor on underlying abelian sheaves. -/
abbrev abelianPushforwardDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(abelianPushforwardFunctor f).Additive]
    [IsGrothendieckAbelian.{u} (AbelianSheafCat X)] :
    DerivedCategory (AbelianSheafCat X) ⥤ DerivedCategory (AbelianSheafCat Y) :=
  CategoryTheory.additiveFunctorTotalRightDerived (abelianPushforwardFunctor f)

section

variable (X : RingedSpace.{u}) (U : Opens X.carrier)
variable [IsGrothendieckAbelian.{u} (RingedSpace.Modules X)]
variable [IsGrothendieckAbelian.{u} (AbelianSheafCat X)]
variable [(moduleSectionsAsAbelianFunctor X U).Additive]
variable [(abelianSectionsFunctor X U).Additive]

-- Proof sketch: both underived section functors on `U` are evaluation of the same underlying
-- abelian presheaf, once starting from `\mathcal O_X`-modules and once starting from abelian
-- sheaves. Compare their total right derived functors to obtain the canonical map
-- `R\Gamma(U, K) \to R\Gamma(U, K_{ab})`; the textbook K-injective construction shows that this
-- comparison is an isomorphism.
/-- Lemma 20.32.7 (1): for an open subset `U ⊆ X` and an object `K` of `D(\mathcal O_X)`, the
canonical comparison map `R\Gamma(U, K) \to R\Gamma(U, K_{ab})` is an isomorphism in
`D(\operatorname{Ab})`. Here `K_{ab}` denotes the image of `K` in the derived category of
abelian sheaves on `X`. -/
lemma moduleSectionsAsAbelianDerived_underlyingAbelian_isomorphic
    (K : DerivedCategory (RingedSpace.Modules X)) :
    IsIsomorphic
      ((moduleSectionsAsAbelianDerived X U).obj K)
      ((abelianSectionsDerived X U).obj
        ((underlyingAbelianSheafDerived X).obj K)) := sorry

end

section

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)
variable [IsGrothendieckAbelian.{u} (RingedSpace.Modules X)]
variable [IsGrothendieckAbelian.{u} (RingedSpace.Modules Y)]
variable [IsGrothendieckAbelian.{u} (AbelianSheafCat X)]
variable [(abelianPushforwardFunctor f).Additive]

-- Proof sketch: underived pushforward of `\mathcal O_X`-modules followed by forgetting module
-- structure agrees with pushforward of the underlying abelian sheaf along the underlying
-- continuous map. Comparing the two total right derived functors yields the canonical morphism
-- `Rf_* K \to Rf_*(K_{ab})` in the derived category of abelian sheaves on `Y`, and the same
-- K-injective representative computes both sides.
/-- Lemma 20.32.7 (2): for a morphism of ringed spaces `f : X ⟶ Y` and an object `K` of
`D(\mathcal O_X)`, the canonical comparison map `Rf_* K \to Rf_*(K_{ab})`, viewed in the derived
category of abelian sheaves on `Y`, is an isomorphism. Here `K_{ab}` denotes the image of `K` in
the derived category of abelian sheaves on `X`. -/
lemma modulePushforwardDerived_underlyingAbelian_isomorphic
    (K : DerivedCategory (RingedSpace.Modules X)) :
    IsIsomorphic
      ((underlyingAbelianSheafDerived Y).obj ((moduleDerivedPushforward f).obj K))
      ((abelianPushforwardDerived f).obj
        ((underlyingAbelianSheafDerived X).obj K)) := sorry

end

end AlgebraicGeometry.RingedSpace
