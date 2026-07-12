import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

variable {I : Type u} [Category.{v} I]

/- Definition 4.19.1: the canonical mathlib notion of a filtered index category is
`CategoryTheory.IsFiltered I`. -/
recall IsFiltered

/-
Domain-style sampling for Definition 4.19.1:
- primary domain: filtered index categories in category theory;
- relevant owner declarations inspected:
  - `CategoryTheory.IsFiltered`,
  - `CategoryTheory.IsFilteredOrEmpty`,
  - `CategoryTheory.IsFiltered.max`,
  - `CategoryTheory.IsFiltered.coeq_condition`;
- best owner abstraction:
  - `source-facing`: the textbook nonemptiness, common-successor, and postcomposition-equalizer
    conditions;
  - `core/canonical`: `IsFiltered`, with primitive owner data in `IsFilteredOrEmpty`;
  - `bridge/view`: direct downstream existential uses of `IsFilteredOrEmpty.cocone_objs` and
    local equalizer constructions when only the source-facing witnesses are needed;
- primitive data: `IsFiltered.nonempty`, `IsFilteredOrEmpty.cocone_objs`, and
  `IsFilteredOrEmpty.cocone_maps`.

Source/core/bridge triage for Definition 4.19.1:
- `source-facing`: the nonemptiness, common-successor, and postcomposition-equalizer conditions.
- `core/canonical`: `IsFiltered` and `IsFilteredOrEmpty`.
- `bridge/view`: downstream existential uses of `IsFilteredOrEmpty.cocone_objs` together with
  direct equalizer witnesses on opposite categories.
-/

end CategoryTheory
