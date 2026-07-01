import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.CategoryTheory.Sites.Sheafification
import stacks_project.Chap06.Definition_6_26_1
import stacks_project.Chap17.Definition_17_17_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace

noncomputable section

universe u

namespace SheafOfModules

variable {X : RingedSpace.{u}}

/- Domain-style sampling for Definition 17.17.3:
- primary domain: stalkwise flatness of sheaves of modules on a ringed space;
- sampled owner declarations:
  `AlgebraicGeometry.RingedSpace.stalkModuleCat`,
  `SheafOfModules.RingedSite.IsFlat`,
  `SheafOfModules.isFlat_stalk`,
  `Module.Flat`;
- owner abstractions:
  the canonical stalk owner is `AlgebraicGeometry.RingedSpace.stalkModuleCat`, and the chapter-level
  flatness owner is `SheafOfModules.RingedSite.IsFlat X.sheaf`;
- primitive data: a sheaf `ℱ : X.Modules` and a point `x : X`;
- derived API: the source-facing pointwise predicate `flat_at` and its specialization
  `unit_flat_at`.

Source/core/bridge triage:
- `source-facing`: flatness of an `\mathcal O_X`-module at a single point;
- `core/canonical`: `RingedSpace.stalkModuleCat`,
  `SheafOfModules.RingedSite.IsFlat X.sheaf`, and `Module.Flat`;
- `bridge/view`: the pointwise predicate `flat_at`, obtained by evaluating the canonical stalk
  flatness owner at one point.

This file should therefore keep only the source-facing pointwise view and reuse the existing
canonical stalk and flatness owners, rather than redeclaring a parallel public stalk-module
bridge. -/

/-- Definition 17.17.3: an `\mathcal O_X`-module `ℱ` is flat at `x` if its stalk `ℱ_x` is a flat
module over the local ring `\mathcal O_{X, x}`. -/
abbrev flat_at (ℱ : X.Modules) (x : X) : Prop :=
  Module.Flat (X.presheaf.stalk x) ↑(stalkModuleCat ℱ x)

/-- The structure sheaf is flat at every point. -/
theorem unit_flat_at (x : X) :
    flat_at (SheafOfModules.unit (ringCatSheaf X)) x :=
  isFlat_stalk x

end SheafOfModules
