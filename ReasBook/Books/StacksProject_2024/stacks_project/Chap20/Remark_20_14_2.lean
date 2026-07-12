import StacksProject_2024.Chap13.Definition_13_18_1
import StacksProject_2024.Chap20.«20_14_1_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory AlgebraicGeometry
open scoped RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling:
- primary domain: the chosen-resolution comparison square from Remark 20.14.2;
- sampled owner declarations:
  `CochainComplex.InjectiveResolution` from Chapter 13,
  `moduleDerivedGlobalSectionsMap` from `20_14_1_1`,
  `CategoryTheory.CommSq`;
- best owner abstraction:
  `core/canonical`: `moduleDerivedGlobalSectionsMap`,
  `source-facing`: the explicit top edge in the chosen-resolution square,
  `bridge/view`: `comparisonTop`, the canonical project name for that top horizontal morphism.
- primitive data here: `φ` and the chosen injective resolution `I`;
- derived API here: only the cochain-level map that forms the top edge of the comparison square.

This file is therefore a thin `bridge/view`: it exports the explicit top horizontal map needed by
the downstream `CommSq` recall, without adding a second public chosen-resolution owner around the
already owned canonical derived comparison morphism.
-/

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y) (𝒢 : RingedSpace.Modules Y) (ℱ : RingedSpace.Modules X)

/- The top horizontal map in the chosen-resolution comparison square from Remark 20.14.2. -/
abbrev comparisonTop
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) (𝒢 : RingedSpace.Modules Y) (ℱ : RingedSpace.Modules X)
    (φ : 𝒢 ⟶ (f _*).obj ℱ)
    (I : CochainComplex.InjectiveResolution
      ((CochainComplex.singleFunctor (RingedSpace.Modules X) 0).obj ℱ)) :
    ((CochainComplex.singleFunctor (RingedSpace.Modules Y) 0).obj 𝒢) ⟶
      (((f _*).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (I : CochainComplex (RingedSpace.Modules X) ℤ)) :=
    ((CochainComplex.singleFunctor (RingedSpace.Modules Y) 0).map φ) ≫
    (((f _*).mapCochainComplexSingleFunctor 0).inv.app ℱ) ≫
    (((f _*).mapHomologicalComplex (ComplexShape.up ℤ)).map I.ι)

/-- `comparisonTop f 𝒢 ℱ φ I` is the explicit cochain-level comparison map induced by `φ`
and the augmentation `I.ι`. -/
theorem comparisonTop_eq
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) (𝒢 : RingedSpace.Modules Y) (ℱ : RingedSpace.Modules X)
    (φ : 𝒢 ⟶ (f _*).obj ℱ)
    (I : CochainComplex.InjectiveResolution
      ((CochainComplex.singleFunctor (RingedSpace.Modules X) 0).obj ℱ)) :
    comparisonTop f 𝒢 ℱ φ I =
      ((CochainComplex.singleFunctor (RingedSpace.Modules Y) 0).map φ) ≫
        (((f _*).mapCochainComplexSingleFunctor 0).inv.app ℱ) ≫
        (((f _*).mapHomologicalComplex (ComplexShape.up ℤ)).map I.ι) :=
  rfl

end AlgebraicGeometry.RingedSpace
