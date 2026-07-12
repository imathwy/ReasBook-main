import StacksProject_2024.Chap06.Definition_6_26_1
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

/- 
Domain-style sampling for coherence of `\mathcal O_X`-modules on a ringed space:
- inspected owner declarations:
  `RingedSpace.Modules`,
  `SheafOfModules.IsFiniteType`,
  `SheafOfModules.IsFinitePresentation`,
  `CategoryTheory.ObjectProperty.FullSubcategory`
- best owner abstraction:
  the ambient owner is `(RingedSpace.Modules X)`
- primitive data:
  a module sheaf `ℱ : (RingedSpace.Modules X)`, finite type on `X`, and
  finite-type kernels for maps from finite free modules on restrictions `ℱ.over U`
- derived API:
  the object property `SheafOfModules.isCoherent X`, the finite-presentation consequence, and the
  full subcategory `RingedSpace.Coh X`

Layer triage:
- `source-facing`: the textbook coherence condition on `\mathcal O_X`-modules
- `core/canonical`: the owner category `(RingedSpace.Modules X)`
- `bridge/view`: the object property and the coherent full subcategory
-/ 

namespace SheafOfModules

variable {X : RingedSpace.{u}}
local notation "ModX" => X.Modules

/-- Definition 17.12.1: a sheaf of `\mathcal O_X`-modules on a ringed space is coherent if it is
of finite type and for every open `U ⊆ X` and every morphism from a finite free
`\mathcal O_U`-module to `ℱ |_U`, the kernel is of finite type. -/
@[stacks 01BV]
class IsCoherent (ℱ : ModX) : Prop where
  /-- A coherent `\mathcal O_X`-module is of finite type. -/
  toIsFiniteType : ℱ.IsFiniteType
  /-- Kernels of morphisms from finite free modules into restrictions of a coherent sheaf are of
  finite type. -/
  isFiniteType_kernel (U : TopologicalSpace.Opens X) (r : ℕ)
      (φ :
        (SheafOfModules.free.{u} (ULift.{u} (Fin r)) :
          SheafOfModules (X.ringCatSheaf.over U)) ⟶
          ℱ.over U) :
      (kernel φ).IsFiniteType

/-- A coherent `\mathcal O_X`-module is of finite type. -/
instance isFiniteType_of_isCoherent (ℱ : ModX) [h : ℱ.IsCoherent] :
    ℱ.IsFiniteType :=
  h.toIsFiniteType

variable (X)

/-- The object property of coherent `\mathcal O_X`-modules. -/
abbrev isCoherent : ObjectProperty X.Modules :=
  SheafOfModules.IsCoherent

variable {X}

end SheafOfModules

namespace AlgebraicGeometry.RingedSpace

/-- The category `Coh(\mathcal O_X)` of coherent `\mathcal O_X`-modules on a ringed space `X`. -/
abbrev Coh (X : RingedSpace.{u}) :=
  (SheafOfModules.isCoherent X).FullSubcategory

end AlgebraicGeometry.RingedSpace
