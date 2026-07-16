import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import StacksProject_2024.stacks_project.Chap06.Definition_6_26_1

open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}} (U : Opens X.carrier)

instance pullbackRingSheafModules_abelian :
    Abelian
      (SheafOfModules
        ((TopCat.Sheaf.pullback RingCat U.inclusion').obj (RingedSpace.ringCatSheaf X))) := by
  let O : TopCat.Sheaf RingCat (TopCat.of U) :=
    (TopCat.Sheaf.pullback RingCat U.inclusion').obj (RingedSpace.ringCatSheaf X)
  change Abelian (SheafOfModules O)
  infer_instance

end

end AlgebraicGeometry.RingedSpace
