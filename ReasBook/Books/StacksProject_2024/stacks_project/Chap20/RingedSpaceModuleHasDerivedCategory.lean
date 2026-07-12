import Mathlib.Algebra.Homology.DerivedCategory.Basic
import StacksProject_2024.Chap06.RingedSpaceModuleCore

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The canonical Chapter 20 homology structure on `RingedSpace.Modules X`, obtained from the
abelian structure on sheaves of modules. -/
instance ringedSpaceModules_categoryWithHomology
    (X : RingedSpace.{u}) :
    CategoryWithHomology (RingedSpace.Modules X) :=
  CategoryTheory.categoryWithHomology_of_abelian

/-- The standard derived-category structure on `RingedSpace.Modules X`. This is the canonical
Chapter 20 instance for passing from complexes of `𝒪_X`-modules to
`DerivedCategory (RingedSpace.Modules X)`. -/
instance ringedSpaceModules_hasDerivedCategory
    (X : RingedSpace.{u}) [CategoryWithHomology (RingedSpace.Modules X)] :
    HasDerivedCategory (RingedSpace.Modules X) :=
  HasDerivedCategory.standard (RingedSpace.Modules X)

/-- The same canonical derived-category structure, written using the dot notation `X.Modules`. -/
instance ringedSpace_instHasDerivedCategoryModules
    (X : RingedSpace.{u}) [CategoryWithHomology X.Modules] :
    HasDerivedCategory X.Modules :=
  ringedSpaceModules_hasDerivedCategory X

end AlgebraicGeometry.RingedSpace
