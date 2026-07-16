import Mathlib
import StacksProject_2024.stacks_project.Chap17.ModuleRestrictionAndStalks

open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "ModX" => RingedSpace.Modules X
local notation "𝒪X" =>
  (SheafOfModules.unit (AlgebraicGeometry.RingedSpace.ringCatSheaf X) : ModX)

/-- The stalk map of the ideal inclusion, viewed in the stalk ring through the canonical
identification of the unit-module stalk with `\mathcal O_{X, x}`. -/
noncomputable abbrev idealSheafStalkToRing
    (I : Subobject 𝒪X) (x : X) :
    RingedSpace.stalkModuleCat (I : ModX) x ⟶
      ModuleCat.of (X.presheaf.stalk x) ↑(X.presheaf.stalk x) :=
  RingedSpace.moduleStalkHom x I.arrow ≫ RingedSpace.unitStalkLinearMap x

/-- The stalk ideal `\mathcal I_x \subset \mathcal O_{X, x}`, owned as the image ideal of the
stalk map induced by `ι`. -/
noncomputable def idealSheafStalkIdeal
    (I : Subobject 𝒪X) (x : X) :
    Ideal (X.presheaf.stalk x) :=
  LinearMap.range (idealSheafStalkToRing I x).hom

end AlgebraicGeometry.RingedSpace
