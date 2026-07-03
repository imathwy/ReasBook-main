import Mathlib
import StacksProject_2024.Chap19.Lemma_19_13_6
import StacksProject_2024.Chap21.Lemma_21_20_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalClosed
open Opposite

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard
set_option checkBinderAnnotations false

namespace SheafOfModules.RingedSite

section

variable (X : RingedSite.{u, v})

/-- The abelian category `\mathrm{Mod}(\mathcal O_X)` of sheaves of modules on the ringed site
`X`. -/
private abbrev RingedSiteModuleCat (X : RingedSite.{u, v}) :=
  RingedSite.Hom.ModuleCat X

/-- The abelian category `\mathrm{Mod}(\mathcal O_U)` on the localized ringed site
`X.localization U`. -/
private abbrev LocalizedRingedSiteModuleCat (X : RingedSite.{u, v}) (U : X) :=
  SheafOfModules (X.structureSheaf.over U)

/-- The standard chosen derived category `D(\mathcal O_X)` attached to `X`. -/
private abbrev StandardRingedSiteDerivedCat (X : RingedSite.{u, v})
    [Abelian (RingedSiteModuleCat X)] :=
  @DerivedCategory (RingedSiteModuleCat X) _ _
    (HasDerivedCategory.standard (RingedSiteModuleCat X))

/-- The standard chosen localized derived category `D(\mathcal O_U)` attached to `X` and `U`. -/
private abbrev StandardLocalizedRingedSiteDerivedCat (X : RingedSite.{u, v}) (U : X)
    [Abelian (LocalizedRingedSiteModuleCat X U)] :=
  @DerivedCategory (LocalizedRingedSiteModuleCat X U) _ _
    (HasDerivedCategory.standard (LocalizedRingedSiteModuleCat X U))

/-- The underived sections functor `\Gamma(U,-)` on `\mathcal O_X`-modules over a fixed object
`U` of the ringed site `X`. -/
private abbrev ringedSiteSectionsOverObjectFunctor (U : X) :
    RingedSiteModuleCat X ⥤ AddCommGrpCat.{max u v} :=
  SheafOfModules.toSheaf X.structureSheaf ⋙
    sheafToPresheaf X.siteTopology AddCommGrpCat.{max u v} ⋙
      (CategoryTheory.evaluation X.carrierᵒᵖ AddCommGrpCat.{max u v}).obj (op U)

-- Proof sketch: `SheafOfModules.toSheaf`, `sheafToPresheaf`, and evaluation at `U` are additive,
-- so their composite sections functor is additive as well.
/-- The sections functor over a fixed object of a ringed site is additive. -/
private theorem ringedSiteSectionsOverObjectFunctor_isAdditive
    (U : X) [hAb : Abelian (RingedSiteModuleCat X)] :
    @Functor.Additive
      (RingedSiteModuleCat X) AddCommGrpCat.{max u v}
      _ _
      hAb.toPreadditive
      AddCommGrpCat.instAbelian.toPreadditive
      (ringedSiteSectionsOverObjectFunctor X U) := sorry

/-- The right derived sections functor `R\Gamma(U,-)` on `D(\mathcal O_X)`. -/
private abbrev ringedSiteDerivedSectionsOverObjectFunctor
    (U : X)
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)] :
    DerivedCategory (RingedSiteModuleCat X) ⥤
      DerivedCategory AddCommGrpCat.{max u v} :=
  @CategoryTheory.additiveFunctorTotalRightDerived
    (RingedSiteModuleCat X) AddCommGrpCat.{max u v}
    _ _ _ AddCommGrpCat.instAbelian
    (ringedSiteSectionsOverObjectFunctor X U)
    (ringedSiteSectionsOverObjectFunctor_isAdditive X U) inferInstance

/-- The degree-`m` objectwise cohomology group `H^m(U, K)` on the ringed site `X`. -/
private abbrev ringedSiteDerivedObjectwiseCohomology
    (U : X)
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)]
    (m : ℤ) (K : DerivedCategory (RingedSiteModuleCat X)) :
    AddCommGrpCat.{max u v} :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} m).obj
    ((ringedSiteDerivedSectionsOverObjectFunctor X U).obj K)

/-- The underived global-sections functor `\Gamma(\mathcal C, -)` on `\mathcal O_X`-modules. -/
private abbrev ringedSiteGlobalSectionsFunctor :
    RingedSiteModuleCat X ⥤ AddCommGrpCat.{max u v} :=
  SheafOfModules.toSheaf X.structureSheaf ⋙
    Sheaf.Γ X.siteTopology AddCommGrpCat.{max u v}

-- Proof sketch: the forgetful functor to abelian sheaves and the global-sections functor on
-- sheaves of abelian groups are additive, so their composite is additive.
/-- The global-sections functor on a ringed site is additive. -/
private theorem ringedSiteGlobalSectionsFunctor_isAdditive
    [hAb : Abelian (RingedSiteModuleCat X)] :
    @Functor.Additive
      (RingedSiteModuleCat X) AddCommGrpCat.{max u v}
      _ _
      hAb.toPreadditive
      AddCommGrpCat.instAbelian.toPreadditive
      (ringedSiteGlobalSectionsFunctor X) := sorry

/-- The right derived global-sections functor `R\Gamma(\mathcal C, -)` on `D(\mathcal O_X)`. -/
private abbrev ringedSiteDerivedGlobalSectionsFunctor
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)] :
    DerivedCategory (RingedSiteModuleCat X) ⥤
      DerivedCategory AddCommGrpCat.{max u v} :=
  @CategoryTheory.additiveFunctorTotalRightDerived
    (RingedSiteModuleCat X) AddCommGrpCat.{max u v}
    _ _ _ AddCommGrpCat.instAbelian
    (ringedSiteGlobalSectionsFunctor X)
    (ringedSiteGlobalSectionsFunctor_isAdditive X) inferInstance

/-- The degree-`m` global cohomology group `H^m(\mathcal C, K)` on the ringed site `X`. -/
private abbrev ringedSiteDerivedGlobalCohomology
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)]
    (m : ℤ) (K : DerivedCategory (RingedSiteModuleCat X)) :
    AddCommGrpCat.{max u v} :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} m).obj
    ((ringedSiteDerivedGlobalSectionsFunctor X).obj K)

-- Proof sketch: choose a K-flat complex representing `L` and a K-injective complex representing
-- `M`. Lemma `21.34.8` shows that the internal-Hom complex representing
-- `R\mathcal H\!\mathit{om}(L, M)` is again K-injective, so `H^0(U, -)` is computed by ordinary
-- sections of that complex. Lemma `21.34.6` then identifies the resulting degree-zero cohomology
-- with morphisms in the localized derived category `D(\mathcal O_U)`.
/-- Lemma 21.35.1 (1): for every object `U` of a ringed site `(\mathcal C, \mathcal O)`, the
degree-zero cohomology of the derived internal Hom over `U` is identified with the morphism group
in the localized derived category. Formalized here, after choosing a derived restriction functor
to the localized site, a chosen comparison map
`H^0(U, R\mathcal H\!\mathit{om}(L, M)) →
  \operatorname{Hom}_{D(\mathcal O_U)}(L|_U, M|_U)`
is bijective. -/
theorem derivedInternalHom_objectwiseH0_comparison_bijective
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)]
    [MonoidalCategory (DerivedCategory (RingedSiteModuleCat X))]
    [MonoidalClosed (DerivedCategory (RingedSiteModuleCat X))]
    (U : X)
    [Abelian (LocalizedRingedSiteModuleCat X U)]
    (restrictU :
      DerivedCategory (RingedSiteModuleCat X) ⥤
        DerivedCategory (LocalizedRingedSiteModuleCat X U))
    (L M : DerivedCategory (RingedSiteModuleCat X))
    (comparison :
      ringedSiteDerivedObjectwiseCohomology X U (0 : ℤ) ((ihom L).obj M) →
        ((restrictU.obj L) ⟶ (restrictU.obj M))) :
    Function.Bijective comparison := sorry

-- Proof sketch: choose a K-flat complex representing `L` and a K-injective complex representing
-- `M`. By Lemma `21.34.8`, their internal-Hom complex is K-injective and represents
-- `R\mathcal H\!\mathit{om}(L, M)`. Applying global sections and then Lemma `21.34.6` identifies
-- the degree-zero cohomology of that complex with the morphism group
-- `\operatorname{Hom}_{D(\mathcal O)}(L, M)`.
/-- Lemma 21.35.1 (2): the degree-zero global cohomology of the derived internal Hom on a ringed
site `(\mathcal C, \mathcal O)` is identified with the morphism group in `D(\mathcal O)`.
Formalized here, a chosen comparison map
`H^0(\mathcal C, R\mathcal H\!\mathit{om}(L, M)) →
  \operatorname{Hom}_{D(\mathcal O)}(L, M)`
is bijective. -/
theorem derivedInternalHom_globalH0_comparison_bijective
    [Abelian (RingedSiteModuleCat X)]
    [CategoryWithHomology (RingedSiteModuleCat X)]
    [IsGrothendieckAbelian (RingedSiteModuleCat X)]
    [MonoidalCategory (DerivedCategory (RingedSiteModuleCat X))]
    [MonoidalClosed (DerivedCategory (RingedSiteModuleCat X))]
    (L M : DerivedCategory (RingedSiteModuleCat X))
    (comparison :
      ringedSiteDerivedGlobalCohomology X (0 : ℤ) ((ihom L).obj M) →
        (L ⟶ M)) :
    Function.Bijective comparison := sorry

end

end SheafOfModules.RingedSite
