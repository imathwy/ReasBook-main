import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap17.Definition_17_25_1
import StacksProject_2024.Chap18.Lemma_18_32_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}

/- Domain-style sampling for Lemma 17.25.3:
- primary domain: invertible `\mathcal O_X`-modules under pullback along a morphism of ringed
  spaces;
- inspected owner declarations:
  `SheafOfModules.RingedSite.IsInvertible`,
  `SheafOfModules.RingedSite.pullback_isInvertible`,
  `AlgebraicGeometry.RingedSpace.Hom.pullback`,
  `SheafOfModules.RingedSite.isInvertible_iff_exists_tensor_inverse`;
- best owner abstraction: the canonical owner is `SheafOfModules.RingedSite.IsInvertible`,
  specialized to `RingedSpace.Modules`; the source-facing pullback statement is therefore a
  ringed-space specialization of the Chapter 18 ringed-site theorem, not a separate local owner;
- primitive data: a morphism of ringed spaces `f : X ⟶ Y` and a module `ℒ : Y.Modules`;
- derived API: the canonical pullback owner `(f^*)` and the inherited invertibility theorem from
  `SheafOfModules.RingedSite.pullback_isInvertible`.

Source/core/bridge triage:
- `source-facing`: invertibility of the pulled-back module on a ringed space;
- `core/canonical`: `SheafOfModules.RingedSite.IsInvertible` and the pullback owner
  `RingedSpace.Hom.pullback`;
- `bridge/view`: the specialization of
  `SheafOfModules.RingedSite.pullback_isInvertible` from ringed sites to ringed spaces.
-/

variable [MonoidalCategory X.Modules] [MonoidalCategory Y.Modules]

/- Lemma 17.25.3: for a morphism of ringed spaces `f : (X, \mathcal O_X) → (Y, \mathcal O_Y)`,
the pullback of an invertible `\mathcal O_Y`-module is invertible. This is the exact opens-site
specialization of the Chapter 18 owner theorem. -/
recall SheafOfModules.RingedSite.pullback_isInvertible

end AlgebraicGeometry.RingedSpace
