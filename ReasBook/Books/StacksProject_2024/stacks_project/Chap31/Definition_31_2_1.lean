import Mathlib
import StacksProject_2024.stacks_project.Chap06.RingedSpaceModuleCore
import StacksProject_2024.stacks_project.Chap06.Definition_6_26_1
import StacksProject_2024.stacks_project.Chap10.Definition_10_63_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry.RingedSpace

variable {X : Scheme.{u}}
local notation "ModX" => RingedSpace.Modules X.toRingedSpace

-- Semantic recall: `lean_leansearch` surfaced `associatedPrimesOfModule` / `IsAssociatedToModule`,
-- and the
-- project owner `RingedSpace.stalkModuleCat` supplies the stalk module over `\mathcal O_{X,x}`.

/-- Definition 31.2.1 (1): the associated points `Ass(ℱ)` of a quasi-coherent `\mathcal O_X`-module
`ℱ` are the points `x : X` such that the maximal ideal `\mathfrak m_x` of the local ring
`\mathcal O_{X, x}` is an associated prime of the stalk module `ℱ_x`. -/
def associatedPoints (ℱ : ModX) : Set X :=
  {x : X | IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∈
    associatedPrimesOfModule (X.presheaf.stalk x)
      (RingedSpace.stalkModuleCat ℱ (x : X.toRingedSpace))}

/-- Membership in `associatedPoints ℱ` is the stalkwise associated-prime condition from
Definition `31.2.1 (1)`. -/
theorem mem_associatedPoints_iff (ℱ : ModX) (x : X) :
    x ∈ associatedPoints ℱ ↔
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∈
        associatedPrimesOfModule (X.presheaf.stalk x)
          (RingedSpace.stalkModuleCat ℱ (x : X.toRingedSpace)) :=
  Iff.rfl

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

open AlgebraicGeometry.RingedSpace

variable (X : Scheme.{u})

local notation "ModX" => RingedSpace.Modules X.toRingedSpace
local notation "𝒪X" => (SheafOfModules.unit X.ringCatSheaf : ModX)

/-- Definition 31.2.1 (2): the associated points of a scheme `X` are the associated points of its
structure sheaf `\mathcal O_X`. -/
abbrev associatedPoints : Set X :=
  Scheme.Modules.associatedPoints 𝒪X

/-- Membership in `X.associatedPoints` is the associated-prime condition for the stalk of the
structure sheaf. -/
theorem mem_associatedPoints_iff (x : X) :
    x ∈ X.associatedPoints ↔
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∈
        associatedPrimesOfModule (X.presheaf.stalk x)
          (RingedSpace.stalkModuleCat 𝒪X (x : X.toRingedSpace)) :=
  Scheme.Modules.mem_associatedPoints_iff 𝒪X x

end AlgebraicGeometry.Scheme
