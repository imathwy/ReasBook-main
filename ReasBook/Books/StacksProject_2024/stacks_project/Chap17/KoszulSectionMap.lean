import Mathlib
import StacksProject_2024.stacks_project.Chap06.Definition_6_26_1

noncomputable section

universe u

open AlgebraicGeometry
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}} {n : ℕ}

/-- The canonical morphism from the free rank-`n` module sheaf to `\mathcal O_X` determined by a
finite family of global sections of the structure sheaf. -/
abbrev koszulSectionMap
    (f : Fin n →
      (SheafOfModules.unit X.ringCatSheaf : SheafOfModules X.ringCatSheaf).sections) :=
  (SheafOfModules.unit X.ringCatSheaf : SheafOfModules X.ringCatSheaf).freeHomEquiv.symm
    (fun i : ULift.{u} (Fin n) ↦ f i.down)

end AlgebraicGeometry.RingedSpace
