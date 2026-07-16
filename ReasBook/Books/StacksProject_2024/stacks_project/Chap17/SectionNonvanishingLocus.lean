import Mathlib
import StacksProject_2024.stacks_project.Chap06.Definition_6_26_1
import StacksProject_2024.stacks_project.Chap17.ModuleRestrictionAndStalks

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable (X : RingedSpace.{u})

local notation "ModX" => RingedSpace.Modules X

section Nonvanishing

variable [∀ x : X, IsLocalRing (X.presheaf.stalk x)]

/-- The source-defined nonvanishing locus of a section of an `\mathcal O_X`-module. -/
def sectionNonvanishingLocus (ℒ : ModX) (s : ℒ.sections) : Set X :=
  {x | (TopCat.Presheaf.Γgerm ℒ.val.presheaf x (s.1 (Opposite.op ⊤))) ∉
    ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
      (⊤ : Submodule (X.presheaf.stalk x) (↑(RingedSpace.stalkModuleCat ℒ x))))}

end Nonvanishing

end AlgebraicGeometry.RingedSpace
