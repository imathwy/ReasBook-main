import Mathlib
import StacksProject_2024.stacks_project.Chap06.Definition_6_26_1

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}
variable [MonoidalCategory (SheafOfModules (RingedSpace.ringCatSheaf X))]

/- Shared Chapter 17 owner for the tensor powers `\mathrm{T}^n(\mathcal F)` of a sheaf of
modules on a ringed space. -/

/-- The `n`th tensor power `\mathrm{T}^n(\mathcal F)` of a sheaf of `\mathcal O_X`-modules,
defined recursively from the tensor product. -/
noncomputable def tensorPowerSheaf
    (ℱ : SheafOfModules ((RingedSpace.ringCatSheaf X))) :
    ℕ → SheafOfModules ((RingedSpace.ringCatSheaf X))
  | 0 => SheafOfModules.unit ((RingedSpace.ringCatSheaf X))
  | n + 1 => tensorObj ℱ (tensorPowerSheaf ℱ n)

scoped[AlgebraicGeometry] notation3:max "T^[" n "] " ℱ =>
  AlgebraicGeometry.RingedSpace.tensorPowerSheaf ℱ n

/-- The successor step in the recursive definition of the tensor-power sheaf. -/
theorem tensorPowerSheaf_succ
    (ℱ : SheafOfModules ((RingedSpace.ringCatSheaf X))) (n : ℕ) :
    (T^[n + 1] ℱ) = tensorObj ℱ (T^[n] ℱ) :=
  rfl

end AlgebraicGeometry.RingedSpace
