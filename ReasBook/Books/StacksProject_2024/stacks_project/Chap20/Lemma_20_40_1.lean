import StacksProject_2024.Chap20.Global_sections_module_owners_core
import StacksProject_2024.Chap20.«20_40_0_1»
import StacksProject_2024.Chap20.OpensInstances

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open ComplexShape

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}} {ι : Type u} [Finite ι]

private instance moduleGlobalSectionsToDerived_hasRightDerivedFunctor (X : RingedSpace.{u}) :
    (((moduleGlobalSectionsFunctor X).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
      DerivedCategory.Q).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (RingedSpace.Modules X) (ComplexShape.up ℤ)) :=
  CategoryTheory.mapHomologicalComplexQ_hasRightDerivedFunctor (moduleGlobalSectionsFunctor X)

/-- The total alternating Čech complex of a complex of `𝒪_X`-modules, formed after
forgetting to abelian sheaves on the underlying space. -/
abbrev moduleAlternatingCechTotalComplexFunctor (X : RingedSpace.{u})
    (𝒰 : ι → Opens X.carrier) :
    CochainComplex (RingedSpace.Modules X) ℤ ⥤ CochainComplex AddCommGrpCat.{u} ℤ :=
  (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    TopCat.Sheaf.alternatingCechTotalComplexFunctor X.carrier 𝒰

/-- The total alternating Čech complex of a complex of `𝒪_X`-modules, viewed in
`D(AddCommGrpCat)`. -/
abbrev moduleAlternatingCechToDerivedFunctor (X : RingedSpace.{u})
    (𝒰 : ι → Opens X.carrier) :
    CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory AddCommGrpCat.{u} :=
  moduleAlternatingCechTotalComplexFunctor X 𝒰 ⋙ DerivedCategory.Q

/-- The abelian-valued derived global-sections functor `RΓ(X, -)` on `D(𝒪_X)`. -/
abbrev moduleDerivedGlobalSectionsToAbelian (X : RingedSpace.{u}) :
    DerivedCategory (RingedSpace.Modules X) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  moduleDerivedGlobalSections X ⋙
    (forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapDerivedCategory

private noncomputable abbrev moduleGlobalSectionsAdditiveIso (X : RingedSpace.{u}) :
    (moduleGlobalSectionsFunctor X ⋙
      forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}) ≅
      SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X) ⋙
        Sheaf.Γ (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} := by
  letI : ∀ U : Opens X.carrier, Nonempty (U ⟶ (⊤ : Opens X.carrier)) := fun U ↦
    ⟨homOfLE le_top⟩
  simpa [moduleGlobalSectionsFunctor, sheafSections] using
    Functor.isoWhiskerLeft (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X))
      ((Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology X.carrier)
        AddCommGrpCat.{u} (Preorder.isTerminalTop (Opens X.carrier))).symm)

private instance moduleUnderlyingSheafGamma_additive (X : RingedSpace.{u}) :
    (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X) ⋙
      Sheaf.Γ (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).Additive :=
  Functor.additive_of_iso (moduleGlobalSectionsAdditiveIso X)

private instance moduleUnderlyingSheafGamma_preservesZeroMorphisms (X : RingedSpace.{u}) :
    (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X) ⋙
      Sheaf.Γ (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _

private noncomputable abbrev moduleGlobalSectionsAdditiveComplexIso (X : RingedSpace.{u}) :
    ((moduleGlobalSectionsFunctor X ⋙
        forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapHomologicalComplex
      (ComplexShape.up ℤ)) ≅
      (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X) ⋙
        Sheaf.Γ (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).mapHomologicalComplex
          (ComplexShape.up ℤ) :=
  NatIso.mapHomologicalComplex (moduleGlobalSectionsAdditiveIso X) (ComplexShape.up ℤ)

/-- The module-level comparison of `20.40.0.1`, after forgetting to abelian sheaves, is the
transport of the sheaf-level comparison across the canonical global-sections identification. -/
def IsModuleGlobalSectionsToAlternatingCechTotalMap (X : RingedSpace.{u})
    (𝒰 : ι → Opens X.carrier) (K : CochainComplex (RingedSpace.Modules X) ℤ)
    (α :
      (((moduleGlobalSectionsFunctor X ⋙
          forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) ⟶
        (moduleAlternatingCechTotalComplexFunctor X 𝒰).obj K) : Prop :=
  let L :=
    ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K
  ∃ β : TopCat.Sheaf.globalSectionsComplex X.carrier L ⟶
      (TopCat.Sheaf.alternatingCechTotalComplexFunctor X.carrier 𝒰).obj L,
    TopCat.Sheaf.IsGlobalSectionsToAlternatingCechTotalMap X.carrier 𝒰 L β ∧
      α = (moduleGlobalSectionsAdditiveComplexIso X).hom.app K ≫ β

omit [Finite ι] in
/-- The comparison of `20.40.0.1` for complexes of `𝒪_X`-modules is unique after
transporting the sheaf-level comparison across the canonical source identification. -/
theorem existsUnique_moduleGlobalSectionsToAlternatingCechTotalMap
    (X : RingedSpace.{u}) (𝒰 : ι → Opens X.carrier)
    (K : CochainComplex (RingedSpace.Modules X) ℤ) :
    ∃! α :
      (((moduleGlobalSectionsFunctor X ⋙
          forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) ⟶
        (moduleAlternatingCechTotalComplexFunctor X 𝒰).obj K,
      IsModuleGlobalSectionsToAlternatingCechTotalMap X 𝒰 K α := by
  obtain ⟨β, hβ, hβuniq⟩ :=
    TopCat.Sheaf.existsUnique_globalSectionsToAlternatingCechTotalMap X.carrier 𝒰
      (((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K)
  refine ⟨(moduleGlobalSectionsAdditiveComplexIso X).hom.app K ≫ β, ?_, ?_⟩
  · exact ⟨β, hβ, rfl⟩
  · intro α hα
    rcases hα with ⟨β', hβ', rfl⟩
    simpa using congrArg
      (fun γ ↦ (moduleGlobalSectionsAdditiveComplexIso X).hom.app K ≫ γ)
      (hβuniq β' hβ')

private abbrev moduleGlobalSectionsAdditiveDerivedUnit (X : RingedSpace.{u}) :
    (((moduleGlobalSectionsFunctor X).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
      DerivedCategory.Q ⋙
        (forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapDerivedCategory) ⟶
      (DerivedCategory.Q : CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory (RingedSpace.Modules X)) ⋙
        moduleDerivedGlobalSectionsToAbelian X :=
  Functor.whiskerRight
      ((((moduleGlobalSectionsFunctor X).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
          DerivedCategory.Q).totalRightDerivedUnit
      (DerivedCategory.Q : CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory (RingedSpace.Modules X))
      (HomologicalComplex.quasiIso (RingedSpace.Modules X) (ComplexShape.up ℤ)))
      ((forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapDerivedCategory) ≫
    (Functor.associator
      (DerivedCategory.Q : CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory (RingedSpace.Modules X))
      (moduleDerivedGlobalSections X)
      ((forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapDerivedCategory)).hom

/-- The canonical comparison from the localized underived abelian global-sections complex of `K`
to `RΓ(X, K)` in `D(AddCommGrpCat)`, rewritten so that its source is the localization of
the abelian global-sections complex itself. -/
abbrev moduleGlobalSectionsAdditiveDerivedUnitApp (X : RingedSpace.{u})
    (K : CochainComplex (RingedSpace.Modules X) ℤ) :
    DerivedCategory.Q.obj ((((moduleGlobalSectionsFunctor X ⋙
          forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K)) ⟶
      ((DerivedCategory.Q : CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory (RingedSpace.Modules X)) ⋙
        moduleDerivedGlobalSectionsToAbelian X).obj K :=
  ((forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapDerivedCategoryFactors.inv.app
      (((moduleGlobalSectionsFunctor X).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
    (moduleGlobalSectionsAdditiveDerivedUnit X).app K

/-- A comparison from the total alternating Čech complex to abelian-valued derived global
sections has the expected source-facing compatibility if, for every complex `K`, it identifies
after precomposition with the canonical transported map from abelian global sections of `K`. -/
def IsModuleAlternatingCechToDerivedGlobalSectionsComparison (X : RingedSpace.{u})
    (𝒰 : ι → Opens X.carrier)
    (τ :
      moduleAlternatingCechToDerivedFunctor X 𝒰 ⟶
        (DerivedCategory.Q :
          CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory (RingedSpace.Modules X)) ⋙
          moduleDerivedGlobalSectionsToAbelian X) : Prop :=
  ∀ K : CochainComplex (RingedSpace.Modules X) ℤ,
    ∃ α :
      (((moduleGlobalSectionsFunctor X ⋙
          forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) ⟶
        (moduleAlternatingCechTotalComplexFunctor X 𝒰).obj K,
      IsModuleGlobalSectionsToAlternatingCechTotalMap X 𝒰 K α ∧
        DerivedCategory.Q.map α ≫ τ.app K =
          moduleGlobalSectionsAdditiveDerivedUnitApp X K

-- Proof sketch: choose a functorial K-injective resolution of complexes of `𝒪_X`-
-- modules. Apply `20.40.0.1` to the chosen K-injective resolution, use the finite-cover
-- acyclicity of injective terms to see that this Čech map computes derived global sections, and
-- descend the resulting comparison along the quasi-isomorphism from the original complex to its
-- resolution. Naturality comes from functoriality of the chosen resolution, and compatibility says
-- that precomposing with the localized map of `20.40.0.1` recovers the canonical derived-unit map
-- for abelian global sections.
/-- Lemma 20.40.1: for a finite open covering `𝒰` with `iSup 𝒰 = ⊤` of a ringed space
`(X, 𝒪_X)`, there exists a functorial comparison from the total alternating Čech complex
of a complex of `𝒪_X`-modules to `RΓ(X, -)` in `D(AddCommGrpCat)`, and this
comparison is compatible with the canonical map of `20.40.0.1` from the underived global-sections
complex to the total alternating Čech complex. -/
@[stacks 08C1]
theorem exists_moduleAlternatingCechToDerivedGlobalSections
    (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = ⊤) :
    ∃ τ :
      moduleAlternatingCechToDerivedFunctor X 𝒰 ⟶
        (DerivedCategory.Q : CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory (RingedSpace.Modules X)) ⋙
          moduleDerivedGlobalSectionsToAbelian X,
      IsModuleAlternatingCechToDerivedGlobalSectionsComparison X 𝒰 τ := sorry

end AlgebraicGeometry.RingedSpace
