import Mathlib
import stacks_project.Chap20.«20_14_1_1»
import stacks_project.Chap20.«20_40_0_1»

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open ComplexShape

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}} {ι : Type u} [Finite ι]

/-- The underlying sheaf of abelian groups of an `\mathcal O_X`-module. -/
abbrev moduleUnderlyingAdditiveSheaf (X : RingedSpace.{u}) :
    (RingedSpace.Modules X) ⥤ TopCat.Sheaf AddCommGrpCat.{u} X.carrier :=
  SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)

/-- The forgetful functor from `\mathcal O_X`-modules to abelian sheaves preserves zero
morphisms. -/
instance moduleUnderlyingAdditiveSheaf_preservesZeroMorphisms (X : RingedSpace.{u}) :
    (moduleUnderlyingAdditiveSheaf X).PreservesZeroMorphisms :=
  show (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).PreservesZeroMorphisms from inferInstance

/-- The global-sections functor on `\mathcal O_X`-modules, after forgetting the
`\Gamma(X, \mathcal O_X)`-module structure down to abelian groups. -/
abbrev moduleGlobalSectionsAsAbelianFunctor (X : RingedSpace.{u}) :
    (RingedSpace.Modules X) ⥤ AddCommGrpCat.{u} :=
  moduleGlobalSectionsFunctor X ⋙
    forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}

/-- The global-sections functor on `\mathcal O_X`-modules is additive after forgetting the
module structure. -/
instance moduleGlobalSectionsAsAbelianFunctor_additive (X : RingedSpace.{u}) :
    (moduleGlobalSectionsAsAbelianFunctor X).Additive :=
  inferInstance

/-- Applying abelian global sections termwise to a complex of `\mathcal O_X`-modules, then
localizing to the derived category of abelian groups. -/
abbrev moduleGlobalSectionsAsAbelianToDerived (X : RingedSpace.{u}) :
    CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory AddCommGrpCat.{u} :=
  moduleGlobalSectionsToDerived X ⋙
    (forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapDerivedCategory

/-- The total alternating Čech complex of a complex of `\mathcal O_X`-modules, formed after
forgetting to abelian sheaves on the underlying space. -/
abbrev moduleAlternatingCechTotalComplexFunctor (X : RingedSpace.{u})
    (𝒰 : ι → Opens X.carrier) :
    CochainComplex (RingedSpace.Modules X) ℤ ⥤ CochainComplex AddCommGrpCat.{u} ℤ :=
  (moduleUnderlyingAdditiveSheaf X).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    TopCat.Sheaf.alternatingCechTotalComplexFunctor X.carrier 𝒰

/-- The total alternating Čech complex of a complex of `\mathcal O_X`-modules, viewed in
`D(\operatorname{Ab})`. -/
abbrev moduleAlternatingCechToDerivedFunctor (X : RingedSpace.{u})
    (𝒰 : ι → Opens X.carrier) :
    CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory AddCommGrpCat.{u} :=
  moduleAlternatingCechTotalComplexFunctor X 𝒰 ⋙ DerivedCategory.Q

/-- The abelian-valued derived global-sections functor `R\Gamma(X, -)` on `D(\mathcal O_X)`. -/
abbrev moduleDerivedGlobalSectionsToAbelian (X : RingedSpace.{u}) :
    DerivedCategory (RingedSpace.Modules X) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  moduleDerivedGlobalSections X ⋙
    (forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapDerivedCategory

/-- The canonical comparison from the underived abelian global-sections complex to
`R\Gamma(X, -)` in `D(\operatorname{Ab})`. -/
abbrev moduleGlobalSectionsAsAbelianDerivedUnit (X : RingedSpace.{u}) :
    moduleGlobalSectionsAsAbelianToDerived X ⟶
      (DerivedCategory.Q : CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory (RingedSpace.Modules X)) ⋙
        moduleDerivedGlobalSectionsToAbelian X :=
  Functor.whiskerRight
      ((moduleGlobalSectionsToDerived X).totalRightDerivedUnit
      (DerivedCategory.Q : CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory (RingedSpace.Modules X))
      (HomologicalComplex.quasiIso (RingedSpace.Modules X) (ComplexShape.up ℤ)))
      ((forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapDerivedCategory) ≫
    (Functor.associator
      (DerivedCategory.Q : CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory (RingedSpace.Modules X))
      (moduleDerivedGlobalSections X)
      ((forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapDerivedCategory)).hom

/-- The complex-level map of `20.40.0.1` for a complex of `\mathcal O_X`-modules, obtained after
forgetting to abelian sheaves on the underlying space. -/
abbrev moduleGlobalSectionsToAlternatingCechTotalMap (X : RingedSpace.{u})
    (𝒰 : ι → Opens X.carrier) (K : CochainComplex (RingedSpace.Modules X) ℤ) :
    ((moduleGlobalSectionsAsAbelianFunctor X).mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶
      (moduleAlternatingCechTotalComplexFunctor X 𝒰).obj K :=
  TopCat.Sheaf.globalSectionsToAlternatingCechTotalMap X.carrier 𝒰
    (((moduleUnderlyingAdditiveSheaf X).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)

/-- The canonical comparison from the localized underived abelian global-sections complex of `K`
to `R\Gamma(X, K)` in `D(\operatorname{Ab})`, rewritten so that its source is the localization of
the abelian global-sections complex itself. -/
abbrev moduleGlobalSectionsAsAbelianDerivedUnitApp (X : RingedSpace.{u})
    (K : CochainComplex (RingedSpace.Modules X) ℤ) :
    DerivedCategory.Q.obj (((moduleGlobalSectionsAsAbelianFunctor X).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) ⟶
      ((DerivedCategory.Q : CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory (RingedSpace.Modules X)) ⋙
        moduleDerivedGlobalSectionsToAbelian X).obj K :=
  ((forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapDerivedCategoryFactors.inv.app
      (((moduleGlobalSectionsFunctor X).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
    (moduleGlobalSectionsAsAbelianDerivedUnit X).app K

-- Proof sketch: choose a functorial K-injective resolution of complexes of `\mathcal O_X`-
-- modules. Apply `20.40.0.1` to the chosen K-injective resolution, use the finite-cover
-- acyclicity of injective terms to see that this Čech map computes derived global sections, and
-- descend the resulting comparison along the quasi-isomorphism from the original complex to its
-- resolution. Naturality comes from functoriality of the chosen resolution, and compatibility says
-- that precomposing with the localized map of `20.40.0.1` recovers the canonical derived-unit map
-- for abelian global sections.
/-- Lemma 20.40.1: for a finite open covering `𝒰 : X = \bigcup_{i \in I} U_i` of a ringed space
`(X,\mathcal O_X)`, there exists a functorial comparison from the total alternating Čech complex
of a complex of `\mathcal O_X`-modules to `R\Gamma(X,-)` in `D(\operatorname{Ab})`, and this
comparison is compatible with the canonical map of `20.40.0.1` from the underived global-sections
complex to the total alternating Čech complex. -/
theorem exists_moduleAlternatingCechToDerivedGlobalSections
    (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = ⊤) :
    ∃ τ :
      moduleAlternatingCechToDerivedFunctor X 𝒰 ⟶
        (DerivedCategory.Q : CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory (RingedSpace.Modules X)) ⋙
          moduleDerivedGlobalSectionsToAbelian X,
      ∀ K : CochainComplex (RingedSpace.Modules X) ℤ,
        DerivedCategory.Q.map (moduleGlobalSectionsToAlternatingCechTotalMap X 𝒰 K) ≫
            τ.app K =
          moduleGlobalSectionsAsAbelianDerivedUnitApp X K := sorry

end AlgebraicGeometry.RingedSpace
