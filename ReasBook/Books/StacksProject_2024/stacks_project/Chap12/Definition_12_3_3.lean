import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory.Limits

/-
Domain-style sampling for Definition 12.3.3:
- primary domain: zero, initial, and terminal objects in a category;
- inspected canonical declarations:
  `IsZero`,
  `IsZero.isInitial`,
  `IsZero.isTerminal`,
  `IsInitial.isZero`;
- owner abstraction: `IsZero X`;
- primitive data: the canonical initial and terminal structures on `X`;
- derived API: `IsZero.isInitial` and `IsZero.isTerminal` already live on the owner. The
  zero-morphism layer adds one-sided reverse constructors such as `IsInitial.isZero`, so this file
  only needs the source-facing bridge from both structures to `IsZero X` without extra ambient
  hypotheses.

Source/core/bridge triage:
- `source-facing`: the source characterization that a zero object is both initial and terminal;
- `core/canonical`: the owner predicate `IsZero X`;
- `bridge/view`: the reverse constructor from `IsInitial X` and `IsTerminal X` to `IsZero X`. -/

/- Definition 12.3.3: the notion of zero object is the canonical predicate `IsZero`. -/
recall IsZero
recall IsZero.isInitial
recall IsZero.isTerminal

section

variable {C : Type u} [Category.{v} C]
variable {X : C}

namespace IsInitial

/-- Definition 12.3.3, source-facing bridge: if an initial object is also terminal, then it is a
zero object. Unlike the zero-morphism-based theorem `IsInitial.isZero`, this bridge does not
assume ambient zero morphisms. -/
theorem isZero_of_isTerminal (hI : IsInitial X) (hT : IsTerminal X) : IsZero X :=
  { unique_to := fun Y ↦ ⟨{ default := hI.to Y, uniq := fun f ↦ hI.hom_ext f _ }⟩
    unique_from := fun Y ↦ ⟨{ default := hT.from Y, uniq := fun f ↦ hT.hom_ext f _ }⟩ }

end IsInitial

end

end CategoryTheory.Limits
