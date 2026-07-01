import Mathlib
import stacks_project.Chap06.Definition_6_26_1
import stacks_project.Chap17.Definition_17_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

/- 
Domain-style sampling for coherence of `\mathcal O_X`-modules on a ringed space:
- inspected owner declarations:
  `(RingedSpace.Modules AlgebraicGeometry.RingedSpace)`,
  `SheafOfModules.IsFiniteType`,
  `SheafOfModules.IsFinitePresentation`,
  `SheafOfModules.RingedSite.IsCoherent`
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

-- Lean miselaborates the direct owner reference `SheafOfModules.IsFiniteType ℱ` in a class field
-- over `RingedSpace.Modules X`; keep a private alias so the public owner remains canonical.
private abbrev FiniteTypeProp (ℱ : RingedSpace.Modules X) : Prop :=
  SheafOfModules.IsFiniteType ℱ

/-- Definition 17.12.1: a sheaf of `\mathcal O_X`-modules on a ringed space is coherent if it is
of finite type and for every open `U ⊆ X` and every morphism from a finite free
`\mathcal O_U`-module to `ℱ |_U`, the kernel is of finite type. -/
class IsCoherent (ℱ : RingedSpace.Modules X) : Prop where
  /-- A coherent sheaf of modules is of finite type. -/
  toIsFiniteType : FiniteTypeProp ℱ
  /-- Kernels of morphisms from finite free modules into restrictions of a coherent sheaf are of
  finite type. -/
  isFiniteType_kernel (U : Opens X) (r : ℕ)
      (φ :
        (SheafOfModules.free.{u} (ULift.{u} (Fin r)) :
          SheafOfModules (X.ringCatSheaf.over U)) ⟶
          ℱ.over U) :
      (kernel φ).IsFiniteType

variable (X)

/-- The object property of coherent `\mathcal O_X`-modules. -/
abbrev isCoherent : ObjectProperty (RingedSpace.Modules X) :=
  SheafOfModules.IsCoherent

variable {X}

instance (ℱ : RingedSpace.Modules X) [h : ℱ.IsCoherent] :
    ℱ.IsFiniteType :=
  h.toIsFiniteType

-- Proof sketch: choose on a neighbourhood `U` a finite generating family of `ℱ|_U`; the induced
-- epimorphism from a finite free `\mathcal O_U`-module onto `ℱ|_U` has finite type kernel by
-- coherence, yielding a local finite presentation.
/-- A coherent `\mathcal O_X`-module is finitely presented. -/
instance (ℱ : RingedSpace.Modules X) [ℱ.IsCoherent] :
    ℱ.IsFinitePresentation := sorry

end SheafOfModules

namespace AlgebraicGeometry.RingedSpace

/-- The category `Coh(\mathcal O_X)` of coherent `\mathcal O_X`-modules on a ringed space `X`. -/
abbrev Coh (X : RingedSpace.{u}) :=
  (SheafOfModules.isCoherent X).FullSubcategory

end AlgebraicGeometry.RingedSpace
