import StacksProject_2024.stacks_project.Chap20.IdealSheafStalkIdeal
import StacksProject_2024.stacks_project.Chap31.ClosedImmersionIdealSubobject

open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

section StalkIdeal

variable {X : Scheme.{u}}

/-- The stalk ideal `\mathcal I_x \subset \mathcal O_{X, x}` cut out by the ideal sheaf data
`D`. -/
abbrev stalkIdeal (D : X.IdealSheafData) (x : X) : Ideal (X.presheaf.stalk x) :=
  RingedSpace.idealSheafStalkIdeal (closedImmersionIdealSubobject D.subschemeι) x

/-- Identify `stalkIdeal` with the canonical Chapter 20 stalk-ideal owner for the closed
immersion ideal sheaf of `D`. -/
@[simp] theorem stalkIdeal_def (D : X.IdealSheafData) (x : X) :
    D.stalkIdeal x =
      RingedSpace.idealSheafStalkIdeal (closedImmersionIdealSubobject D.subschemeι) x :=
  rfl

end StalkIdeal

end AlgebraicGeometry.Scheme.IdealSheafData
