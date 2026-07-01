import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open Limits

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable (F : Cᵒᵖ ⥤ Type w)

/- Domain-style sampling for 21.2.0.2:
- primary domain: set-valued presheaves and their global sections;
- sampled owner API:
  `Functor.sections`,
  `Functor.sectionsEquivHom`,
  `Functor.isTerminalConst`,
  `Types.isTerminalPUnit`;
- best owner abstraction: the core owner is `Functor.sections`, and the source-facing
  `Γ(\mathcal C, F) ≃ \operatorname{Hom}(*, F)` formula is its canonical bridge
  `Functor.sectionsEquivHom`;
- primitive data: only the presheaf `F : Cᵒᵖ ⥤ Type w`;
- derived API: the realization of a terminal presheaf as a constant singleton-valued presheaf and
  the induced equivalence from global sections to morphisms out of that terminal object.

Source/core/bridge triage:
- `source-facing`: the identification of global sections with morphisms from the terminal
  presheaf;
- `core/canonical`: `Functor.sections`;
- `bridge/view`: `Functor.sectionsEquivHom`, together with `Functor.isTerminalConst` for the
  singleton-valued constant presheaf.

This item is therefore a bridge/view recall, not a new owner declaration. -/
/- 21.2.0.2: for a set-valued presheaf `F : Cᵒᵖ ⥤ Type w`, the identification
`Γ(\mathcal C, F) ≃ \operatorname{Hom}(*, F)` is the canonical bridge
`Functor.sectionsEquivHom`, with the terminal presheaf realized by the constant presheaf on a
singleton type. -/
recall Functor.sectionsEquivHom

example : IsTerminal ((Functor.const Cᵒᵖ).obj (PUnit : Type w)) :=
  Functor.isTerminalConst Cᵒᵖ Types.isTerminalPUnit

example : F.sections ≃ ((Functor.const Cᵒᵖ).obj (PUnit : Type w) ⟶ F) :=
  F.sectionsEquivHom PUnit

end CategoryTheory
