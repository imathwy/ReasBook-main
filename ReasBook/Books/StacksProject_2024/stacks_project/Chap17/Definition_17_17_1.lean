import Mathlib
import StacksProject_2024.stacks_project.Chap17.Definition_17_17_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace

noncomputable section

universe u

namespace SheafOfModules

variable {X : RingedSpace.{u}}

/- Domain-style sampling for Definition 17.17.1:
- primary domain: flat sheaves of modules on a ringed space, defined by exactness of tensoring on
  the right;
- inspected owner declarations:
  `RingedSpace.Modules`,
  `SheafOfModules.IsFlat`,
  `SheafOfModules.flat_at`,
  `Module.Flat`;
- best owner abstraction: within the current chapter, the canonical owner is the ringed-space
  class `SheafOfModules.IsFlat`, whose primitive data is stalkwise flatness and whose intended
  source meaning is the exactness definition of flatness;
- primitive data: a sheaf `ℱ : RingedSpace.Modules X`;
- derived API: the ringed-space specialization `SheafOfModules.IsFlat` and the stalkwise bridge
  theorems `isFlat_stalk` and `isFlat_of_stalkwise`.

Source/core/bridge triage:
- `source-facing`: global flatness of an `\mathcal O_X`-module sheaf, defined by exactness of
  tensoring with it;
- `core/canonical`: `SheafOfModules.IsFlat`;
- `bridge/view`: the stalkwise characterization via `flat_at`.

This file should therefore expose the high-reuse ringed-space specialization
`SheafOfModules.IsFlat` and treat the pointwise predicate `flat_at` as the public bridge API. -/

/-- Definition 17.17.1: an `\mathcal O_X`-module on a ringed space is flat. In Chapter 17 we use
the ringed-space owner whose primitive interface is stalkwise flatness. -/
@[mk_iff]
class IsFlat (ℱ : RingedSpace.Modules X) : Prop where
  /-- Every stalk `\mathcal F_x` is flat over `\mathcal O_{X, x}`. -/
  flatAt (x : X) : ℱ.flat_at x

/-- Companion bridge: a flat sheaf of modules has flat stalks. -/
theorem isFlat_stalk {ℱ : RingedSpace.Modules X}
    (hℱ : ℱ.IsFlat) (x : X) :
    Module.Flat (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x) := by
  simpa [flat_at] using hℱ.flatAt x

/-- Companion bridge: stalkwise flatness implies flatness of the sheaf. -/
theorem isFlat_of_stalkwise (ℱ : RingedSpace.Modules X)
    (hℱ : ∀ x : X, Module.Flat (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x)) :
    ℱ.IsFlat := by
  exact ⟨fun x ↦ by simpa [flat_at] using hℱ x⟩

end SheafOfModules
