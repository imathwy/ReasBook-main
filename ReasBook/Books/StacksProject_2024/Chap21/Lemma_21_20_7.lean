import Mathlib
import StacksProject_2024.Chap19.Lemma_19_13_6
import StacksProject_2024.Chap21.Lemma_21_20_5

open CategoryTheory
open Opposite

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

namespace RingedSite.Hom

/-- The abelian category of sheaves of abelian groups on the site underlying a ringed site. -/
abbrev AbelianSheafCat (X : RingedSite.{u, v}) :=
  Sheaf X.siteTopology AddCommGrpCat.{max u v}

/-- The forgetful functor from `\mathcal O_X`-modules to their underlying abelian sheaves. -/
abbrev underlyingAbelianSheafFunctor (X : RingedSite.{u, v}) :
    ModuleCat X ⥤ AbelianSheafCat X :=
  SheafOfModules.toSheaf X.structureSheaf

/-- The derived forgetful functor sending a complex of `\mathcal O_X`-modules to its underlying
complex of abelian sheaves. -/
abbrev underlyingAbelianSheafDerived (X : RingedSite.{u, v})
    [IsGrothendieckAbelian.{max u v} (ModuleCat X)] :
    ModuleDerived X ⥤ DerivedCategory (AbelianSheafCat X) :=
  CategoryTheory.additiveFunctorTotalRightDerived
    (underlyingAbelianSheafFunctor X)

/-- The global-sections functor on abelian sheaves over the site underlying `X`. -/
abbrev abelianGlobalSectionsFunctor (X : RingedSite.{u, v})
    [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{max u v}] :
    AbelianSheafCat X ⥤ AddCommGrpCat.{max u v} :=
  CategoryTheory.Sheaf.Γ X.siteTopology AddCommGrpCat.{max u v}

/-- The total right derived functor of global sections on abelian sheaves over the site underlying
`X`. -/
abbrev abelianGlobalSectionsDerived (X : RingedSite.{u, v})
    [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{max u v}]
    [(abelianGlobalSectionsFunctor X).Additive]
    [IsGrothendieckAbelian.{max u v} (AbelianSheafCat X)] :
    DerivedCategory (AbelianSheafCat X) ⥤ DerivedCategory AddCommGrpCat.{max u v} :=
  CategoryTheory.additiveFunctorTotalRightDerived
    (abelianGlobalSectionsFunctor X)

/-- The underived sections functor `\Gamma(U,-)` on `\mathcal O_X`-modules, viewed in abelian
groups. -/
abbrev moduleSectionsAsAbelianFunctor (X : RingedSite.{u, v}) (U : X)
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}] :
    ModuleCat X ⥤ AddCommGrpCat.{max u v} :=
  SheafOfModules.toSheaf X.structureSheaf ⋙
    sheafToPresheaf X.siteTopology AddCommGrpCat.{max u v} ⋙
      (evaluation X.carrierᵒᵖ AddCommGrpCat.{max u v}).obj (op U)

/-- The derived sections functor `R\Gamma(U,-)` on `D(\mathcal O_X)`, viewed in
`D(\operatorname{Ab})`. -/
abbrev moduleSectionsAsAbelianDerived (X : RingedSite.{u, v}) (U : X)
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    [(moduleSectionsAsAbelianFunctor X U).Additive]
    [IsGrothendieckAbelian.{max u v} (ModuleCat X)] :
    ModuleDerived X ⥤ DerivedCategory AddCommGrpCat.{max u v} :=
  CategoryTheory.additiveFunctorTotalRightDerived
    (moduleSectionsAsAbelianFunctor X U)

/-- The underived sections functor `\Gamma(U,-)` on abelian sheaves over the site underlying
`X`. -/
abbrev abelianSectionsFunctor (X : RingedSite.{u, v}) (U : X)
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}] :
    AbelianSheafCat X ⥤ AddCommGrpCat.{max u v} :=
  sheafToPresheaf X.siteTopology AddCommGrpCat.{max u v} ⋙
    (evaluation X.carrierᵒᵖ AddCommGrpCat.{max u v}).obj (op U)

/-- The total right derived functor of sections over `U` on abelian sheaves over the site
underlying `X`. -/
abbrev abelianSectionsDerived (X : RingedSite.{u, v}) (U : X)
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    [(abelianSectionsFunctor X U).Additive]
    [IsGrothendieckAbelian.{max u v} (AbelianSheafCat X)] :
    DerivedCategory (AbelianSheafCat X) ⥤ DerivedCategory AddCommGrpCat.{max u v} :=
  CategoryTheory.additiveFunctorTotalRightDerived
    (abelianSectionsFunctor X U)

/-- The direct-image functor on abelian sheaves induced by a morphism of ringed sites. -/
abbrev abelianPushforwardFunctor {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y) :
    AbelianSheafCat X ⥤ AbelianSheafCat Y :=
  f.base.sheafPushforwardContinuous AddCommGrpCat.{max u v}
    Y.siteTopology X.siteTopology

/-- The total right derived direct-image functor on underlying abelian sheaves. -/
abbrev abelianPushforwardDerived {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [(abelianPushforwardFunctor f).Additive]
    [IsGrothendieckAbelian.{max u v} (AbelianSheafCat X)] :
    DerivedCategory (AbelianSheafCat X) ⥤ DerivedCategory (AbelianSheafCat Y) :=
  CategoryTheory.additiveFunctorTotalRightDerived
    (abelianPushforwardFunctor f)

section

variable (X : RingedSite.{u, v})

variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{max u v}]
variable [(moduleGlobalSectionsFunctor X).Additive]
variable [Functor.HasRightDerivedFunctor (moduleGlobalSectionsToDerived X) (ModuleQis X)]
variable [(abelianGlobalSectionsFunctor X).Additive]
variable [IsGrothendieckAbelian.{max u v} (ModuleCat X)]
variable [IsGrothendieckAbelian.{max u v} (AbelianSheafCat X)]

-- Proof sketch: the underived global-sections functor on `\mathcal O_X`-modules is the composite
-- of the forgetful functor to abelian sheaves with global sections on abelian sheaves. Compare the
-- two total right derived functors of this composite; the induced canonical map is the one from
-- the statement, and it is an isomorphism because the same K-injective representative computes
-- both sides after forgetting module structure.
/-- Lemma 21.20.7 (1): for a ringed site `X` and `K : D(\mathcal O_X)`, the canonical comparison
map `R\Gamma(\mathcal C, K) \to R\Gamma(\mathcal C, K_{ab})` is an isomorphism in
`D(\operatorname{Ab})`. -/
theorem moduleGlobalSectionsDerived_underlyingAbelian_isomorphic
    (K : ModuleDerived X) :
    IsIsomorphic
      ((moduleGlobalSectionsDerived X).obj K)
      ((abelianGlobalSectionsDerived X).obj
        ((underlyingAbelianSheafDerived X).obj K)) := sorry

end

section

variable (X : RingedSite.{u, v})

variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [IsGrothendieckAbelian.{max u v} (ModuleCat X)]
variable [IsGrothendieckAbelian.{max u v} (AbelianSheafCat X)]

variable (U : X)
variable [(moduleSectionsAsAbelianFunctor X U).Additive]
variable [(abelianSectionsFunctor X U).Additive]

-- Proof sketch: both underived sections functors over `U` are computed by evaluation of the
-- underlying abelian presheaf at `U`; the left-hand functor first starts from module sheaves and
-- the right-hand functor first forgets to abelian sheaves. Compare their total right derived
-- functors to obtain the canonical map `R\Gamma(U, K) \to R\Gamma(U, K_{ab})`, and use the same
-- K-injective resolution argument as in the textbook to see that it is an isomorphism.
/-- Lemma 21.20.7 (2): for an object `U` of a ringed site `X` and `K : D(\mathcal O_X)`, the
canonical comparison map `R\Gamma(U, K) \to R\Gamma(U, K_{ab})` is an isomorphism in
`D(\operatorname{Ab})`. -/
theorem moduleSectionsAsAbelianDerived_underlyingAbelian_isomorphic
    (K : ModuleDerived X) :
    IsIsomorphic
      ((moduleSectionsAsAbelianDerived X U).obj K)
      ((abelianSectionsDerived X U).obj
        ((underlyingAbelianSheafDerived X).obj K)) := sorry

end

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)

variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [HasWeakSheafify Y.siteTopology AddCommGrpCat.{max u v}]
variable [f.modulePushforward.Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [(abelianPushforwardFunctor f).Additive]
variable [IsGrothendieckAbelian.{max u v} (ModuleCat X)]
variable [IsGrothendieckAbelian.{max u v} (ModuleCat Y)]
variable [IsGrothendieckAbelian.{max u v} (AbelianSheafCat X)]

-- Proof sketch: underived pushforward of `\mathcal O_X`-modules followed by forgetting module
-- structure agrees with pushforward of the underlying abelian sheaf along the underlying morphism
-- of sites. Comparing the two total right derived functors yields the canonical morphism
-- `Rf_* K \to Rf_*(K_{ab})` in the derived category of abelian sheaves on `Y`, and the textbook
-- K-injective construction shows that this morphism is an isomorphism.
/-- Lemma 21.20.7 (3): for a morphism of ringed sites `f : X ⟶ Y` and `K : D(\mathcal O_X)`, the
canonical comparison map `Rf_* K \to Rf_*(K_{ab})`, viewed in the derived category of abelian
sheaves on `Y`, is an isomorphism. -/
theorem modulePushforwardDerived_underlyingAbelian_isomorphic
    (K : ModuleDerived X) :
    IsIsomorphic
      ((underlyingAbelianSheafDerived Y).obj ((modulePushforwardDerived f).obj K))
      ((abelianPushforwardDerived f).obj
        ((underlyingAbelianSheafDerived X).obj K)) := sorry

end

end RingedSite.Hom
