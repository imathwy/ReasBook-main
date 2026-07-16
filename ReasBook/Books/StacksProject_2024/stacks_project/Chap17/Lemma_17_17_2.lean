import Mathlib
import StacksProject_2024.stacks_project.Chap17.Definition_17_17_3
import StacksProject_2024.stacks_project.Chap17.Definition_17_17_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace

universe u

namespace SheafOfModules

variable {X : RingedSpace.{u}}

/- Domain-style sampling for Lemma 17.17.2:
- primary domain: flat sheaves of modules on a ringed space, expressed through stalkwise
  flatness;
- sampled owner declarations:
  `RingedSpace.Modules`,
  `SheafOfModules.IsFlat`,
  `AlgebraicGeometry.RingedSpace.stalkModuleCat`,
  `SheafOfModules.flat_at`,
  `SheafOfModules.RingedSite.IsFlat`;
- best owner abstraction: for this chapter's ringed-space statements the owner is the established
  specialization `SheafOfModules.IsFlat`, while `SheafOfModules.RingedSite.IsFlat` remains the
  underlying site-level core and `flat_at` is the source-facing pointwise view on stalk modules;
- primitive data: a module sheaf `ℱ : RingedSpace.Modules X`;
- derived API: the stalkwise characterization theorem below.

Source/core/bridge triage:
- `source-facing`: the stalkwise reformulation of flatness;
- `core/canonical`: `RingedSpace.Modules`, `RingedSpace.stalkModuleCat`,
  `SheafOfModules.IsFlat`, with definitional core `SheafOfModules.RingedSite.IsFlat`;
- `bridge/view`: `flat_at`.

This file should therefore state the source-facing bridge between the canonical exactness owner
and the stalkwise predicate, using the chapter-local ringed-space owner rather than spelling the
underlying site-level predicate on the public surface.
-/

/-- Lemma 17.17.2: an `\mathcal O_X`-module `ℱ` on a ringed space is flat if and only if, for
every point `x : X`, the stalk `ℱ_x` is a flat module over the local ring `\mathcal O_{X, x}`. -/
theorem isFlat_iff_stalkwise (ℱ : X.Modules) :
    ℱ.IsFlat ↔ ∀ x : X, ℱ.flat_at x :=
  by
    constructor
    · intro hℱ x
      simpa [flat_at] using isFlat_stalk hℱ x
    · intro hℱ
      exact isFlat_of_stalkwise ℱ (fun x ↦ by simpa [flat_at] using hℱ x)

end SheafOfModules
