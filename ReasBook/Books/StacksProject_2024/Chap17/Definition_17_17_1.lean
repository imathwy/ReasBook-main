import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap17.Lemma_17_16_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry.RingedSpace

noncomputable section

universe u

namespace SheafOfModules

variable {X : RingedSpace.{u}}

/- Domain-style sampling for Definition 17.17.1:
- primary domain: flat sheaves of modules on a ringed space, defined by exactness of tensoring on
  the right;
- inspected owner declarations:
  `X.Modules`,
  `SheafOfModules.RingedSite.IsFlat`,
  `SheafOfModules.RingedSite.unit_isFlat`,
  `Module.Flat`;
- best owner abstraction: the canonical owner is the site-level predicate
  `SheafOfModules.RingedSite.IsFlat`, specialized to the opens-site of `X` and hence to the
  ambient category `X.Modules`;
- primitive data: a sheaf `ℱ : X.Modules`;
- derived API: the stalkwise bridge theorems `isFlat_stalk` and `isFlat_of_stalkwise`, together
  with the unit instance.

Source/core/bridge triage:
- `source-facing`: global flatness of an `\mathcal O_X`-module sheaf, defined by exactness of
  tensoring with it;
- `core/canonical`: `SheafOfModules.RingedSite.IsFlat`;
- `bridge/view`: the later stalkwise characterization, exposed here only through companion bridge
  theorems rather than as primitive public data.

This file should therefore recall the site-level owner specialized to `X` and treat stalkwise
flatness as derived bridge API. -/

/- Definition 17.17.1: for a ringed space `(X, \mathcal O_X)`, flatness of an
`\mathcal O_X`-module is exactly the opens-site specialization of the canonical site-level owner
`SheafOfModules.RingedSite.IsFlat`. -/
recall SheafOfModules.RingedSite.IsFlat

/-- Companion bridge: a flat sheaf of modules has flat stalks. -/
theorem isFlat_stalk {ℱ : X.Modules}
    [SheafOfModules.RingedSite.IsFlat X.sheaf ℱ] (x : X) :
    Module.Flat (X.presheaf.stalk x) ↑(stalkModuleCat ℱ x) := sorry

/-- Companion bridge: stalkwise flatness implies flatness of the sheaf. -/
theorem isFlat_of_stalkwise (ℱ : X.Modules)
    (hℱ : ∀ x : X, Module.Flat (X.presheaf.stalk x) ↑(stalkModuleCat ℱ x)) :
    SheafOfModules.RingedSite.IsFlat X.sheaf ℱ := sorry

/-- The structure sheaf, viewed as a module over itself, is flat. -/
theorem unit_isFlat :
    SheafOfModules.RingedSite.IsFlat X.sheaf
      (SheafOfModules.unit (ringCatSheaf X)) := by
  simpa using SheafOfModules.RingedSite.unit_isFlat X.sheaf

/-- The structure sheaf carries its canonical flatness instance. -/
instance :
    SheafOfModules.RingedSite.IsFlat X.sheaf
      (SheafOfModules.unit (ringCatSheaf X)) :=
  unit_isFlat

end SheafOfModules
