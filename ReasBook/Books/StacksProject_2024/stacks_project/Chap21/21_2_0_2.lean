import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap07.Example_7_10_2

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u

namespace CategoryTheory

open Limits
open scoped TerminalPresheaf

variable {C : Type u} [Category.{v} C]
variable (ℱ : Presheaf C)

/- Domain-style sampling for 21.2.0.2:
- primary domain: set-valued presheaves and their global sections;
- sampled owner API:
  `Presheaf`,
  `Functor.sections`,
  `Functor.sectionsEquivHom`,
  `Functor.isTerminalConst`,
  `Types.isTerminalPUnit`;
- best owner abstraction: the core owner is `Functor.sections`, and the source-facing
  `ℱ.sections ≃ (*ₚ[C] ⟶ ℱ)` formula is its canonical bridge
  `Functor.sectionsEquivHom`;
- primitive data: only the presheaf `ℱ : Presheaf C`;
- derived API: the chapter's source-facing terminal-presheaf notation `*ₚ[C]` and the induced
  equivalence from global sections to morphisms out of that terminal object.

Source/core/bridge triage:
- `source-facing`: the identification of global sections with morphisms from the terminal
  presheaf;
- `core/canonical`: `Functor.sections`;
- `bridge/view`: `Functor.sectionsEquivHom`, together with `Functor.isTerminalConst` for the
  terminal presheaf `*ₚ[C]`.

This item is therefore a bridge/view recall, not a new owner declaration. -/
/- 21.2.0.2: for a set-valued presheaf `ℱ : Presheaf C`, the identification
`ℱ.sections ≃ (*ₚ[C] ⟶ ℱ)` is the canonical bridge
`Functor.sectionsEquivHom`, written in the project's established source-facing notation for the
terminal presheaf. -/
recall Functor.sectionsEquivHom

/- Companion check: the terminal presheaf `*ₚ[C]` is the singleton-valued constant presheaf and
is terminal in `Cᵒᵖ ⥤ Type w`. -/
#check
  (Functor.isTerminalConst Cᵒᵖ Types.isTerminalPUnit : IsTerminal *ₚ[C])

/- Source-facing specialization: global sections of `ℱ` identify with morphisms from the terminal
presheaf `*ₚ[C]` to `ℱ`. -/
#check
  (ℱ.sectionsEquivHom PUnit : ℱ.sections ≃ (*ₚ[C] ⟶ ℱ))

end CategoryTheory
