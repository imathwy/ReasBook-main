import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap17.Definition_17_13_1_Owner

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The ideal sheaf of a scheme morphism, viewed canonically as a subobject of the ambient
structure sheaf. -/
noncomputable def closedImmersionIdealSubobject {X Z : Scheme.{u}} (i : Z ⟶ X) :
    Subobject
      (SheafOfModules.unit (RingedSpace.ringCatSheaf X.toRingedSpace) :
        RingedSpace.Modules X.toRingedSpace) :=
  Subobject.mk
    (kernel.ι
      (SheafOfModules.unitToPushforwardObjUnit
        (RingedSpace.Hom.toRingCatSheafHom i.toShHom)))

end AlgebraicGeometry
