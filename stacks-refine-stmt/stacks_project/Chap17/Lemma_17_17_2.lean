import Mathlib
import stacks_project.Chap17.Definition_17_17_3

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
  `AlgebraicGeometry.RingedSpace.stalkModuleCat`,
  `SheafOfModules.RingedSite.IsFlat`,
  `SheafOfModules.flat_at`;
- best owner abstraction: `SheafOfModules.RingedSite.IsFlat X.sheaf` is the canonical owner on
  the opens-site of `X`, while `flat_at` is the source-facing pointwise view;
- primitive data: a module sheaf `ℱ : X.Modules`, with flatness owned globally by exactness of
  tensoring on the right;
- derived API: the stalkwise characterization theorem below.

Source/core/bridge triage:
- `source-facing`: the stalkwise reformulation of flatness;
- `core/canonical`: `X.Modules`, `RingedSpace.stalkModuleCat`, and
  `SheafOfModules.RingedSite.IsFlat X.sheaf`;
- `bridge/view`: `flat_at`.

This file should therefore state only the source-facing equivalence and reuse the canonical owner
from `Definition_17_17_1`, rather than redeclaring a parallel `IsFlat` API.
-/

-- Proof sketch: one direction is exactly the stalk projection theorem for the canonical owner.
-- Conversely, the stalkwise hypotheses are precisely the data required to build the owner class.
/-- Lemma 17.17.2: an `\mathcal O_X`-module `ℱ` on a ringed space is flat if and only if, for
every point `x : X`, the stalk `ℱ_x` is a flat module over the local ring `\mathcal O_{X, x}`. -/
theorem isFlat_iff_stalkwise (ℱ : X.Modules) :
    SheafOfModules.RingedSite.IsFlat X.sheaf ℱ ↔ ∀ x : X, ℱ.flat_at x :=
  ⟨fun _ x ↦ isFlat_stalk x, isFlat_of_stalkwise ℱ⟩

end SheafOfModules
