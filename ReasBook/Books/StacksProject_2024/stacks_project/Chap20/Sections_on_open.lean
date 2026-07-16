import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import StacksProject_2024.stacks_project.Chap19.AdditiveFunctorTotalRightDerived
import StacksProject_2024.stacks_project.Chap12.Remark_12_29_2
import StacksProject_2024.stacks_project.Chap06.Definition_6_26_1
import StacksProject_2024.stacks_project.Chap06.Definition_6_25_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.mapHomologicalComplexQ_hasRightDerivedFunctor

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}

/- Domain-style sampling for open sections on a ringed space:
- primary domain: section rings on an open subset and restriction of scalars along
  `Γ(V, 𝒪_Y) → Γ(f⁻¹(V), 𝒪_X)`;
- sampled owner declarations:
  `RingedSpace.preimageOpen`,
  `SheafOfModules.evaluation`,
  `ModuleCat.restrictScalars`,
  `additiveFunctorTotalRightDerived`,
  `Functor.mapDerivedCategory`;
- best owner abstraction:
  `source-facing`: the section ring `Γ(U, 𝒪_X)` and the induced restriction-of-scalars functor on
    modules over section rings;
  `core/canonical`: evaluation of the structure sheaf, `ModuleCat.restrictScalars`, and the
    chapter owner `additiveFunctorTotalRightDerived`;
  `bridge/view`: the map on section rings induced by a morphism of ringed spaces and its exact
    derived restriction functor.
- primitive data: a ringed space `X`, an open subset `U ⊆ X`, and a morphism `f : X ⟶ Y`;
- derived API: additive and derived-category structure on the associated module categories, the
  resulting derived sections functors, and the source-facing open hypercohomology owner
  `moduleOpenHypercohomology`.
 -/

/-- The ring of sections `Γ(U, \mathcal O_X)` on an open subset `U ⊆ X`. -/
abbrev sectionsRingOnOpen (X : RingedSpace.{u}) (U : Opens X.carrier) : CommRingCat :=
  X.presheaf.obj (op U)

/-- Modules over `Γ(U, \mathcal O_X)` have their standard derived category. -/
instance sectionsRingOnOpen_hasDerivedCategory (X : RingedSpace.{u}) (U : Opens X.carrier) :
    HasDerivedCategory (ModuleCat (sectionsRingOnOpen X U)) :=
  HasDerivedCategory.standard (ModuleCat (sectionsRingOnOpen X U))

/-- The sections functor on an open subset is additive. -/
instance moduleSectionsEvaluation_additive (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (SheafOfModules.evaluation (RingedSpace.ringCatSheaf X) (op U)).Additive where
  map_add := by
    intro M N f g
    rfl

/-- The underived sections functor `\Gamma(U,-)` on `\mathcal O_X`-modules, viewed in abelian
groups. -/
abbrev moduleSectionsAsAbelianFunctor (X : RingedSpace.{u}) (U : Opens X.carrier) :
    X.Modules ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.evaluation X.ringCatSheaf (op U) ⋙
    forget₂ (ModuleCat (sectionsRingOnOpen X U)) AddCommGrpCat.{u}

/-- The underived abelian-valued sections functor on an open subset is additive. -/
instance moduleSectionsAsAbelianFunctor_additive (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (moduleSectionsAsAbelianFunctor X U).Additive where
  map_add := by
    intro M N f g
    rfl

/-- The sections functor on an open subset preserves zero morphisms. -/
instance moduleSectionsEvaluation_preservesZeroMorphisms
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (SheafOfModules.evaluation (RingedSpace.ringCatSheaf X) (op U)).PreservesZeroMorphisms := by
  let _ : (SheafOfModules.evaluation (RingedSpace.ringCatSheaf X) (op U)).Additive := by
    infer_instance
  infer_instance

/-- The map on section rings over `V` induced by a morphism of ringed spaces. -/
abbrev sectionsMapOnOpen (f : X ⟶ Y) (V : Opens Y.carrier) :
    sectionsRingOnOpen Y V ⟶ sectionsRingOnOpen X (preimageOpen f V) :=
  f.hom.c.app (op V)

/-- Restriction of scalars along `Γ(V, \mathcal O_Y) → Γ(f^{-1}(V), \mathcal O_X)`. -/
abbrev moduleSectionsRestrictionFunctor (f : X ⟶ Y) (V : Opens Y.carrier) :
    ModuleCat (sectionsRingOnOpen X (preimageOpen f V)) ⥤
      ModuleCat (sectionsRingOnOpen Y V) :=
  ModuleCat.restrictScalars (sectionsMapOnOpen f V).hom

/-- Restriction of scalars on section modules is additive. -/
instance moduleSectionsRestrictionFunctor_additive (f : X ⟶ Y) (V : Opens Y.carrier) :
    (moduleSectionsRestrictionFunctor f V).Additive := by
  infer_instance

private abbrev moduleSectionsEvaluationFunctor
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    RingedSpace.Modules X ⥤ ModuleCat (sectionsRingOnOpen X U) :=
  SheafOfModules.evaluation (RingedSpace.ringCatSheaf X) (op U)

private abbrev topOpenSubset (X : RingedSpace.{u}) : Opens X.carrier :=
  ⟨Set.univ, isOpen_univ⟩

/-- The total right derived functor `RΓ(U, -)` on `D(\mathcal O_X)`. -/
abbrev moduleDerivedSectionsAtOpen
    (X : RingedSpace.{u}) [IsGrothendieckAbelian X.Modules] (U : Opens X.carrier) :
    DerivedCategory (RingedSpace.Modules X) ⥤ DerivedCategory (ModuleCat (sectionsRingOnOpen X U)) :=
  let F : RingedSpace.Modules X ⥤ ModuleCat (sectionsRingOnOpen X U) :=
    moduleSectionsEvaluationFunctor X U
  letI : F.Additive := moduleSectionsEvaluation_additive X U
  letI :
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).HasRightDerivedFunctor
        (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ)) :=
    CategoryTheory.mapHomologicalComplexQ_hasRightDerivedFunctor F
  (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).totalRightDerived
    DerivedCategory.Q
    (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ))

/-- The derived sections functor `RΓ(U, -)` on `D(\mathcal O_X)`, viewed in
`D(\operatorname{Ab})` via the forgetful functor on `Γ(U, \mathcal O_X)`-modules. -/
abbrev moduleDerivedSectionsAtOpenToAb
    (X : RingedSpace.{u}) [IsGrothendieckAbelian X.Modules] (U : Opens X.carrier) :
    DerivedCategory (RingedSpace.Modules X) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  let F : ModuleCat (sectionsRingOnOpen X U) ⥤ AddCommGrpCat.{u} :=
    forget₂ (ModuleCat (sectionsRingOnOpen X U)) AddCommGrpCat.{u}
  let _ : PreservesFiniteLimits F := inferInstance
  let _ : PreservesFiniteColimits F := inferInstance
  moduleDerivedSectionsAtOpen X U ⋙ F.mapDerivedCategory

/-- The total right derived functor of ordinary abelian-valued sections on `U`. -/
abbrev moduleSectionsAsAbelianDerived
    (X : RingedSpace.{u}) [IsGrothendieckAbelian X.Modules] (U : Opens X.carrier) :
    DerivedCategory (RingedSpace.Modules X) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  let F := moduleSectionsAsAbelianFunctor X U
  letI :
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).HasRightDerivedFunctor
        (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ)) :=
    CategoryTheory.mapHomologicalComplexQ_hasRightDerivedFunctor F
  (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).totalRightDerived
    DerivedCategory.Q
    (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ))

section

variable {X : RingedSpace.{u}} [IsGrothendieckAbelian X.Modules]

local notation "DModX" => DerivedCategory X.Modules
local notation "QModX" => (DerivedCategory.Q : CochainComplex X.Modules ℤ ⥤ DModX)
local notation "QisModX" => HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ)

private abbrev moduleSectionsAsAbelianToDerived
    (U : Opens X.carrier) :
    CochainComplex X.Modules ℤ ⥤ DerivedCategory AddCommGrpCat.{u} :=
  (moduleSectionsAsAbelianFunctor X U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q

private theorem moduleSectionsAsAbelianToDerived_hasRightDerivedFunctor
    (U : Opens X.carrier) :
    (moduleSectionsAsAbelianToDerived U).HasRightDerivedFunctor QisModX := by
  simpa [moduleSectionsAsAbelianToDerived] using
    (CategoryTheory.mapHomologicalComplexQ_hasRightDerivedFunctor
      (moduleSectionsAsAbelianFunctor X U))

attribute [local instance] moduleSectionsAsAbelianToDerived_hasRightDerivedFunctor

private instance moduleSectionsAsAbelianDerived_isRightDerivedFunctor
    (U : Opens X.carrier) :
    (moduleSectionsAsAbelianDerived X U).IsRightDerivedFunctor
      ((moduleSectionsAsAbelianToDerived U).totalRightDerivedUnit QModX QisModX)
      QisModX := by
  simpa [moduleSectionsAsAbelianDerived, moduleSectionsAsAbelianToDerived] using
    (inferInstance :
      ((moduleSectionsAsAbelianToDerived U).totalRightDerived QModX QisModX).IsRightDerivedFunctor
        ((moduleSectionsAsAbelianToDerived U).totalRightDerivedUnit QModX QisModX)
        QisModX)

private theorem moduleSectionsEvaluationToDerived_hasRightDerivedFunctor
    (U : Opens X.carrier) :
    (((SheafOfModules.evaluation X.ringCatSheaf (op U)).mapHomologicalComplex
          (ComplexShape.up ℤ)) ⋙
        DerivedCategory.Q).HasRightDerivedFunctor QisModX := by
  simpa using
    (CategoryTheory.mapHomologicalComplexQ_hasRightDerivedFunctor
      (SheafOfModules.evaluation X.ringCatSheaf (op U)))

attribute [local instance] moduleSectionsEvaluationToDerived_hasRightDerivedFunctor

private noncomputable def moduleSectionsAsAbelianToDerived_forgetCompIso
    (U : Opens X.carrier) :
    moduleSectionsAsAbelianToDerived U ≅
      (((SheafOfModules.evaluation X.ringCatSheaf (op U)).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q) ⋙
        (forget₂ (ModuleCat (sectionsRingOnOpen X U)) AddCommGrpCat.{u}).mapDerivedCategory) := by
  let evalH := (SheafOfModules.evaluation X.ringCatSheaf (op U)).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let forgetSec := forget₂ (ModuleCat (sectionsRingOnOpen X U)) AddCommGrpCat.{u}
  simpa [moduleSectionsAsAbelianToDerived, moduleSectionsAsAbelianFunctor, evalH, forgetSec] using
    Functor.isoWhiskerLeft evalH forgetSec.mapDerivedCategoryFactors.symm ≪≫
      (Functor.associator evalH DerivedCategory.Q forgetSec.mapDerivedCategory).symm

private noncomputable def moduleSectionsAsAbelianDerivedSourceComparisonNat
    (U : Opens X.carrier) :
    moduleSectionsAsAbelianToDerived U ⟶
      QModX ⋙ moduleDerivedSectionsAtOpenToAb X U :=
  (moduleSectionsAsAbelianToDerived_forgetCompIso U).hom ≫
    Functor.whiskerRight
      (Functor.totalRightDerivedUnit
        (((SheafOfModules.evaluation X.ringCatSheaf (op U)).mapHomologicalComplex
            (ComplexShape.up ℤ)) ⋙
          DerivedCategory.Q)
        QModX
        QisModX)
      ((forget₂ (ModuleCat (sectionsRingOnOpen X U)) AddCommGrpCat.{u}).mapDerivedCategory) ≫
    (Functor.associator
      QModX
      (moduleDerivedSectionsAtOpen X U)
      (forget₂ (ModuleCat (sectionsRingOnOpen X U)) AddCommGrpCat.{u}).mapDerivedCategory).hom

private noncomputable def moduleSectionsAsAbelianDerivedComparison
    (U : Opens X.carrier) :
    moduleSectionsAsAbelianDerived X U ⟶ moduleDerivedSectionsAtOpenToAb X U := by
  exact
    (moduleSectionsAsAbelianDerived X U).rightDerivedDesc
      ((moduleSectionsAsAbelianToDerived U).totalRightDerivedUnit QModX QisModX)
      QisModX
      (moduleDerivedSectionsAtOpenToAb X U)
      (moduleSectionsAsAbelianDerivedSourceComparisonNat U)

private theorem moduleSectionsAsAbelianDerivedComparison_isIso
    (U : Opens X.carrier) :
    IsIso (moduleSectionsAsAbelianDerivedComparison (X := X) U) := by
  sorry

/-- The abelian-valued open derived sections functor `RΓ[U]` is canonically isomorphic to the
total right derived functor of ordinary abelian-valued sections on `U`. -/
theorem moduleDerivedSectionsAtOpenToAb_isomorphic_moduleSectionsAsAbelianDerived
    (X : RingedSpace.{u}) [IsGrothendieckAbelian X.Modules] (U : Opens X.carrier) :
    IsIsomorphic
      (moduleDerivedSectionsAtOpenToAb X U)
      (moduleSectionsAsAbelianDerived X U) := by
  let _ := moduleSectionsAsAbelianDerivedComparison_isIso (X := X) U
  exact ⟨(asIso (moduleSectionsAsAbelianDerivedComparison (X := X) U)).symm⟩

end

/- Textbook surface notation for the abelian-valued derived sections functor `RΓ(U,-)` on a
ringed space. The ambient ringed space is recovered from the open subset `U`. -/
@[inherit_doc AlgebraicGeometry.RingedSpace.moduleDerivedSectionsAtOpenToAb]
scoped[RingedSpaceDerivedSectionsAtOpenToAb] notation3:max "RΓ[" U "]" =>
  AlgebraicGeometry.RingedSpace.moduleDerivedSectionsAtOpenToAb _ U

/-- The open hypercohomology group `H^p(U, K)` of a derived `\mathcal O_X`-module, viewed in
`AddCommGrpCat`. -/
abbrev moduleOpenHypercohomology
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    [IsGrothendieckAbelian X.Modules]
    (K : DerivedCategory (RingedSpace.Modules X)) (p : ℤ) : AddCommGrpCat.{u} :=
  (forget₂ (ModuleCat (sectionsRingOnOpen X U)) AddCommGrpCat.{u}).obj
    ((DerivedCategory.homologyFunctor (ModuleCat (sectionsRingOnOpen X U)) p).obj
      ((moduleDerivedSectionsAtOpen X U).obj K))

/-- The degree-`p` cohomology of an `\mathcal O_X`-module on the open subset `U`, viewed as a
`Γ(U, \mathcal O_X)`-module. -/
abbrev moduleCohomologyAtOpen
    [IsGrothendieckAbelian X.Modules]
    (U : Opens X.carrier) (ℱ : RingedSpace.Modules X) (p : ℕ) :
    ModuleCat (sectionsRingOnOpen X U) :=
  let F : RingedSpace.Modules X ⥤ ModuleCat (sectionsRingOnOpen X U) :=
    SheafOfModules.evaluation (RingedSpace.ringCatSheaf X) (op U)
  letI : IsGrothendieckAbelian (RingedSpace.Modules X) := inferInstance
  letI : F.Additive := moduleSectionsEvaluation_additive X U
  (F.rightDerived p).obj ℱ

namespace RingedSpaceOpenHypercohomology

/- Textbook surface notation for open hypercohomology `H^p(U, K)`. -/
scoped notation:max "H^" p:max "(" U ", " K ")" =>
  AlgebraicGeometry.RingedSpace.moduleOpenHypercohomology _ U K p

end RingedSpaceOpenHypercohomology

/-- The derived restriction-of-scalars functor on section modules induced by a morphism of ringed
spaces. -/
abbrev moduleSectionsRestrictionDerived (f : X ⟶ Y) (V : Opens Y.carrier) :
    DerivedCategory (ModuleCat (sectionsRingOnOpen X (preimageOpen f V))) ⥤
      DerivedCategory (ModuleCat (sectionsRingOnOpen Y V)) :=
  let _ : PreservesFiniteLimits (moduleSectionsRestrictionFunctor f V) :=
    ((exactFunctor_iff (moduleSectionsRestrictionFunctor f V)).mp
      (restrictScalars_exact (sectionsMapOnOpen f V).hom)).1
  let _ : PreservesFiniteColimits (moduleSectionsRestrictionFunctor f V) :=
    ((exactFunctor_iff (moduleSectionsRestrictionFunctor f V)).mp
      (restrictScalars_exact (sectionsMapOnOpen f V).hom)).2
  let F := ExactFunctor.of (moduleSectionsRestrictionFunctor f V)
  let _ : F.obj.Additive := moduleSectionsRestrictionFunctor_additive f V
  F.obj.mapDerivedCategory

end AlgebraicGeometry.RingedSpace
