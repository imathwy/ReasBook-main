import Mathlib
import StacksProject_2024.stacks_project.Chap20.Global_sections_module_owners_core
import StacksProject_2024.stacks_project.Chap20.OpensInstances

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/-- The ring of sections `Γ(U, \mathcal O_X)` on an open subset `U ⊆ X`. -/
private abbrev sectionsRingOnOpen (X : RingedSpace.{u}) (U : Opens X.carrier) : CommRingCat :=
  X.presheaf.obj (op U)

/-- The sections functor on an open subset is additive. -/
private instance moduleSectionsEvaluation_additive
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (SheafOfModules.evaluation X.ringCatSheaf (op U)).Additive where
  map_add := by
    intro M N f g
    rfl

/-- The sections functor on an open subset preserves zero morphisms. -/
private instance moduleSectionsEvaluation_preservesZeroMorphisms
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (SheafOfModules.evaluation X.ringCatSheaf (op U)).PreservesZeroMorphisms := by
  let _ : (SheafOfModules.evaluation X.ringCatSheaf (op U)).Additive :=
    moduleSectionsEvaluation_additive X U
  infer_instance

/-- The total right derived functor `RΓ(U,-)` on `D(\mathcal O_X)`. -/
private abbrev moduleDerivedSectionsAtOpen
    (X : RingedSpace.{u}) [IsGrothendieckAbelian X.Modules] (U : Opens X.carrier) :
    DerivedCategory (RingedSpace.Modules X) ⥤ DerivedCategory (ModuleCat (sectionsRingOnOpen X U)) :=
  let F : RingedSpace.Modules X ⥤ ModuleCat (sectionsRingOnOpen X U) :=
    SheafOfModules.evaluation X.ringCatSheaf (op U)
  letI : F.Additive := moduleSectionsEvaluation_additive X U
  letI :
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).HasRightDerivedFunctor
        (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ)) :=
    CategoryTheory.mapHomologicalComplexQ_hasRightDerivedFunctor F
  (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).totalRightDerived
    DerivedCategory.Q
    (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ))

/-- Restriction of scalars along the canonical map `Γ(X, \mathcal O_X) → Γ(U, \mathcal O_X)`. -/
abbrev moduleSectionsRestrictionToGlobalFunctor
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    ModuleCat (sectionsRingOnOpen X U) ⥤ ModuleCat (sectionsRingOnOpen X ⊤) :=
  ModuleCat.restrictScalars
    ((X.presheaf.map (homOfLE (show U ≤ (⊤ : Opens X.carrier) from le_top)).op).hom)

/-- Restriction of scalars from `Γ(U, \mathcal O_X)`-modules to `Γ(X, \mathcal O_X)`-modules is
additive. -/
instance moduleSectionsRestrictionToGlobalFunctor_additive
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (moduleSectionsRestrictionToGlobalFunctor X U).Additive := by
  infer_instance

/-- The underived sections functor `Γ(U,-)` viewed as taking values in
`Γ(X,\mathcal O_X)`-modules by restriction of scalars. -/
abbrev moduleSectionsOverGlobalFunctor
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    RingedSpace.Modules X ⥤ ModuleCat (sectionsRingOnOpen X ⊤) :=
  SheafOfModules.evaluation X.ringCatSheaf (op U) ⋙
    moduleSectionsRestrictionToGlobalFunctor X U

/-- The underived sections functor `Γ(U,-)` viewed over `Γ(X,\mathcal O_X)` is additive. -/
private instance moduleSectionsOverGlobalFunctorComp_additive
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (SheafOfModules.evaluation X.ringCatSheaf (op U) ⋙
        moduleSectionsRestrictionToGlobalFunctor X U).Additive where
  map_add := by
    intro ℱ 𝒢 φ ψ
    rfl

instance moduleSectionsOverGlobalFunctor_additive
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (moduleSectionsOverGlobalFunctor X U).Additive := by
  simpa [moduleSectionsOverGlobalFunctor] using
    (inferInstance :
      (SheafOfModules.evaluation X.ringCatSheaf (op U) ⋙
          moduleSectionsRestrictionToGlobalFunctor X U).Additive)

/-- The underived sections functor `Γ(U,-)` viewed over `Γ(X,\mathcal O_X)` preserves zero
morphisms. -/
private instance moduleSectionsOverGlobalFunctorComp_preservesZeroMorphisms
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (SheafOfModules.evaluation X.ringCatSheaf (op U) ⋙
        moduleSectionsRestrictionToGlobalFunctor X U).PreservesZeroMorphisms where
  map_zero := by
    intro ℱ 𝒢
    rfl

instance moduleSectionsOverGlobalFunctor_preservesZeroMorphisms
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (moduleSectionsOverGlobalFunctor X U).PreservesZeroMorphisms := by
  simpa [moduleSectionsOverGlobalFunctor] using
    (inferInstance :
      (SheafOfModules.evaluation X.ringCatSheaf (op U) ⋙
          moduleSectionsRestrictionToGlobalFunctor X U).PreservesZeroMorphisms)

/-- The total right derived functor `RΓ(U,-)` valued in `D(Γ(X,\mathcal O_X))`. -/
abbrev moduleDerivedSectionsOverGlobal
    (X : RingedSpace.{u}) [IsGrothendieckAbelian X.Modules] (U : Opens X.carrier) :
    DerivedCategory (RingedSpace.Modules X) ⥤
      DerivedCategory (ModuleCat (sectionsRingOnOpen X ⊤)) :=
  let _ : (moduleSectionsOverGlobalFunctor X U).Additive :=
    moduleSectionsOverGlobalFunctor_additive X U
  let F : RingedSpace.Modules X ⥤ ModuleCat (sectionsRingOnOpen X ⊤) :=
    moduleSectionsOverGlobalFunctor X U
  letI :
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).HasRightDerivedFunctor
        (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ)) :=
    CategoryTheory.mapHomologicalComplexQ_hasRightDerivedFunctor F
  (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).totalRightDerived
    DerivedCategory.Q
    (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ))

section DerivedSectionsOverGlobalRestriction

variable (X : RingedSpace.{u}) [IsGrothendieckAbelian X.Modules]

local notation "ModX" => RingedSpace.Modules X
local notation "QModX" => (DerivedCategory.Q : CochainComplex ModX ℤ ⥤ DerivedCategory ModX)
local notation "QisModX" => HomologicalComplex.quasiIso ModX (ComplexShape.up ℤ)

private abbrev moduleGlobalSectionsToDerived :
    CochainComplex ModX ℤ ⥤ DerivedCategory (ModuleCat (sectionsRingOnOpen X ⊤)) :=
  (SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : Opens X.carrier))).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q

private abbrev moduleSectionsOverGlobalToDerived (U : Opens X.carrier) :
    CochainComplex ModX ℤ ⥤ DerivedCategory (ModuleCat (sectionsRingOnOpen X ⊤)) :=
  (moduleSectionsOverGlobalFunctor X U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q

private instance moduleGlobalSectionsToDerived_hasRightDerivedFunctor :
    (moduleGlobalSectionsToDerived X).HasRightDerivedFunctor QisModX := by
  simpa [moduleGlobalSectionsToDerived] using
    (CategoryTheory.mapHomologicalComplexQ_hasRightDerivedFunctor.{u, u + 1, u + 1, u, u}
      (SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : Opens X.carrier))))

private instance moduleSectionsOverGlobalToDerived_hasRightDerivedFunctor (U : Opens X.carrier) :
    (moduleSectionsOverGlobalToDerived X U).HasRightDerivedFunctor QisModX := by
  let _ : (moduleSectionsOverGlobalFunctor X U).Additive :=
    moduleSectionsOverGlobalFunctor_additive X U
  simpa [moduleSectionsOverGlobalToDerived] using
    (CategoryTheory.mapHomologicalComplexQ_hasRightDerivedFunctor.{u, u + 1, u + 1, u, u}
      (moduleSectionsOverGlobalFunctor X U))

private noncomputable abbrev moduleDerivedSectionsAtOpenUnit :
    (moduleGlobalSectionsToDerived X) ⟶ QModX ⋙ moduleDerivedSectionsAtOpen X ⊤ :=
  let F : ModX ⥤ ModuleCat (sectionsRingOnOpen X ⊤) :=
    SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : Opens X.carrier))
  let _ : F.Additive := moduleSectionsEvaluation_additive X ⊤
  let _ :
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).HasRightDerivedFunctor
        QisModX :=
    CategoryTheory.mapHomologicalComplexQ_hasRightDerivedFunctor F
  show (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⟶
      QModX ⋙ moduleDerivedSectionsAtOpen X ⊤ from
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).totalRightDerivedUnit
      QModX
      QisModX

private noncomputable abbrev moduleDerivedSectionsOverGlobalUnit (U : Opens X.carrier) :
    (moduleSectionsOverGlobalToDerived X U) ⟶
      QModX ⋙ moduleDerivedSectionsOverGlobal X U :=
  let F : ModX ⥤ ModuleCat (sectionsRingOnOpen X ⊤) :=
    moduleSectionsOverGlobalFunctor X U
  let _ : F.Additive := moduleSectionsOverGlobalFunctor_additive X U
  let _ :
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).HasRightDerivedFunctor
        QisModX :=
    CategoryTheory.mapHomologicalComplexQ_hasRightDerivedFunctor F
  show (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⟶
      QModX ⋙ moduleDerivedSectionsOverGlobal X U from
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).totalRightDerivedUnit
      QModX
      QisModX

private instance moduleDerivedSectionsAtOpen_isRightDerivedFunctor :
    (moduleDerivedSectionsAtOpen X ⊤).IsRightDerivedFunctor
      (moduleDerivedSectionsAtOpenUnit X) QisModX := by
  sorry

private instance moduleDerivedSectionsOverGlobal_isRightDerivedFunctor (U : Opens X.carrier) :
    (moduleDerivedSectionsOverGlobal X U).IsRightDerivedFunctor
      (moduleDerivedSectionsOverGlobalUnit X U) QisModX := by
  sorry

/-- The canonical restriction natural transformation on underived section functors
`Γ(X,-) → Γ(U,-)` after viewing the target as `Γ(X,\mathcal O_X)`-modules. -/
private abbrev moduleSectionsOverGlobalRestrictionNatTrans
    (U : Opens X.carrier) :
    SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : Opens X.carrier)) ⟶
      (SheafOfModules.evaluation X.ringCatSheaf (op U) ⋙
        moduleSectionsRestrictionToGlobalFunctor X U) where
  app ℱ :=
    ℱ.val.map (homOfLE (show U ≤ (⊤ : Opens X.carrier) from le_top)).op
  naturality {ℱ 𝒢} φ := by
    simpa [moduleSectionsOverGlobalFunctor, moduleSectionsRestrictionToGlobalFunctor] using
      (φ.val.naturality (homOfLE (show U ≤ (⊤ : Opens X.carrier) from le_top)).op).symm

/-- The canonical derived restriction natural transformation
`RΓ(X,-) → RΓ(U,-)` valued in `D(Γ(X,\mathcal O_X))`. -/
private abbrev moduleSectionsOverGlobalRestrictionNatTransOnComplexes
    (U : Opens X.carrier) :
    (SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : Opens X.carrier))).mapHomologicalComplex
        (ComplexShape.up ℤ) ⟶
      (moduleSectionsOverGlobalFunctor X U).mapHomologicalComplex (ComplexShape.up ℤ) where
  app K :=
    { f := fun i ↦ (moduleSectionsOverGlobalRestrictionNatTrans X U).app (K.X i)
      comm' := by
        intro i j hij
        cases hij
        simpa using
          ((moduleSectionsOverGlobalRestrictionNatTrans X U).naturality (K.d i (i + 1))).symm }
  naturality {K L} φ := by
    ext i x
    simpa using
      congrArg (fun f ↦ (ModuleCat.Hom.hom f) x)
        ((moduleSectionsOverGlobalRestrictionNatTrans X U).naturality (φ.f i))

/-- The canonical derived restriction natural transformation
`RΓ(X,-) → RΓ(U,-)` valued in `D(Γ(X,\mathcal O_X))`. -/
noncomputable def moduleDerivedSectionsOverGlobalRestrictionNatTrans
    (U : Opens X.carrier) :
    moduleDerivedGlobalSections X ⟶ moduleDerivedSectionsOverGlobal X U := by
  letI := moduleSectionsEvaluation_preservesZeroMorphisms X ⊤
  letI := moduleSectionsOverGlobalFunctorComp_preservesZeroMorphisms X U
  simpa [moduleDerivedGlobalSections] using
    (Functor.rightDerivedNatTrans
      (moduleDerivedSectionsAtOpen X ⊤)
      (moduleDerivedSectionsOverGlobal X U)
      (moduleDerivedSectionsAtOpenUnit X)
      (moduleDerivedSectionsOverGlobalUnit X U)
      QisModX
      (Functor.whiskerRight
        (moduleSectionsOverGlobalRestrictionNatTransOnComplexes X U)
        DerivedCategory.Q))

/-- The canonical restriction natural transformation on underived sections over global scalars for
nested opens `U ≤ V`. -/
private abbrev moduleSectionsOverGlobalRestrictionNatTransOfLE
    {U V : Opens X.carrier} (hUV : U ≤ V) :
    moduleSectionsOverGlobalFunctor X V ⟶ moduleSectionsOverGlobalFunctor X U where
  app ℱ :=
    let α : sectionsRingOnOpen X ⊤ ⟶ sectionsRingOnOpen X V :=
      X.presheaf.map (homOfLE (show V ≤ (⊤ : Opens X.carrier) from le_top)).op
    let β : sectionsRingOnOpen X V ⟶ sectionsRingOnOpen X U :=
      X.presheaf.map (homOfLE hUV).op
    let γ : sectionsRingOnOpen X ⊤ ⟶ sectionsRingOnOpen X U :=
      X.presheaf.map (homOfLE (show U ≤ (⊤ : Opens X.carrier) from le_top)).op
    let hcomp : β.hom.comp α.hom = γ.hom := by
      have hcompOp :
          (homOfLE (show V ≤ (⊤ : Opens X.carrier) from le_top)).op ≫ (homOfLE hUV).op =
            (homOfLE (show U ≤ (⊤ : Opens X.carrier) from le_top)).op := by
        apply Subsingleton.elim
      have hmap :
          X.presheaf.map
              ((homOfLE (show V ≤ (⊤ : Opens X.carrier) from le_top)).op ≫
                (homOfLE hUV).op) =
            X.presheaf.map (homOfLE (show U ≤ (⊤ : Opens X.carrier) from le_top)).op := by
        simpa using congrArg (fun f ↦ X.presheaf.map f) hcompOp
      simpa [α, β, γ] using congrArg CommRingCat.Hom.hom hmap
    show (moduleSectionsOverGlobalFunctor X V).obj ℱ ⟶ (moduleSectionsOverGlobalFunctor X U).obj ℱ from
      (moduleSectionsRestrictionToGlobalFunctor X V).map (ℱ.val.map (homOfLE hUV).op) ≫
        (ModuleCat.restrictScalarsComp' α.hom β.hom γ.hom hcomp.symm).inv.app
          (ℱ.val.obj (op U))
  naturality {ℱ 𝒢} φ := by
    ext x
    simp [moduleSectionsOverGlobalFunctor, moduleSectionsRestrictionToGlobalFunctor]
    simpa using
      DFunLike.congr_fun
        (congrArg ModuleCat.Hom.hom ((φ.val.naturality (homOfLE hUV).op).symm))
        x

/-- The canonical derived restriction natural transformation on sections over global scalars for
nested opens `U ≤ V`. -/
noncomputable def moduleDerivedSectionsOverGlobalRestrictionNatTransOfLE
    {U V : Opens X.carrier} (hUV : U ≤ V) :
    moduleDerivedSectionsOverGlobal X V ⟶ moduleDerivedSectionsOverGlobal X U :=
  letI := moduleSectionsOverGlobalFunctor_preservesZeroMorphisms X V
  letI := moduleSectionsOverGlobalFunctor_preservesZeroMorphisms X U
  Functor.rightDerivedNatTrans
    (moduleDerivedSectionsOverGlobal X V)
    (moduleDerivedSectionsOverGlobal X U)
    (moduleDerivedSectionsOverGlobalUnit X V)
    (moduleDerivedSectionsOverGlobalUnit X U)
    QisModX
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex
        (moduleSectionsOverGlobalRestrictionNatTransOfLE X hUV)
        (ComplexShape.up ℤ))
      DerivedCategory.Q)

/-- The canonical morphism from derived sections over `V` to derived sections over `U`, both
viewed in `D(Γ(X,\mathcal O_X))`, for nested opens `U ≤ V`. -/
abbrev moduleDerivedSectionsOverGlobalRestrictionOfLE
    {U V : Opens X.carrier} (hUV : U ≤ V) (K : DerivedCategory X.Modules) :
    (moduleDerivedSectionsOverGlobal X V).obj K ⟶
      (moduleDerivedSectionsOverGlobal X U).obj K :=
  (moduleDerivedSectionsOverGlobalRestrictionNatTransOfLE X hUV).app K

/-- The canonical morphism from global derived sections to derived sections on `U`, both viewed in
`D(Γ(X,\mathcal O_X))`. -/
abbrev moduleDerivedSectionsOverGlobalRestriction
    (U : Opens X.carrier) (K : DerivedCategory X.Modules) :
    (moduleDerivedGlobalSections X).obj K ⟶
      (moduleDerivedSectionsOverGlobal X U).obj K :=
  (moduleDerivedSectionsOverGlobalRestrictionNatTrans X U).app K

/-- The canonical Mayer-Vietoris restriction natural transformation on derived sections over
global scalars. -/
abbrev moduleDerivedSectionsOverGlobalMayerVietorisToBiprod
    (U V : Opens X.carrier) :
    moduleDerivedGlobalSections X ⟶
      moduleDerivedSectionsOverGlobal X U ⊞ moduleDerivedSectionsOverGlobal X V :=
  biprod.lift
    (moduleDerivedSectionsOverGlobalRestrictionNatTrans X U)
    (moduleDerivedSectionsOverGlobalRestrictionNatTrans X V)

/-- The canonical Mayer-Vietoris overlap-difference natural transformation on derived sections
over global scalars. -/
abbrev moduleDerivedSectionsOverGlobalMayerVietorisDifference
    (U V : Opens X.carrier) :
    moduleDerivedSectionsOverGlobal X U ⊞ moduleDerivedSectionsOverGlobal X V ⟶
      moduleDerivedSectionsOverGlobal X (U ⊓ V) :=
  biprod.desc
    (moduleDerivedSectionsOverGlobalRestrictionNatTransOfLE X
      (show U ⊓ V ≤ U from inf_le_left))
    (-(moduleDerivedSectionsOverGlobalRestrictionNatTransOfLE X
      (show U ⊓ V ≤ V from inf_le_right)))

end DerivedSectionsOverGlobalRestriction

end AlgebraicGeometry.RingedSpace
