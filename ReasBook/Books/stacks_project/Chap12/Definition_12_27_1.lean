import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory

universe v u

/- Domain-style sampling for Definition 12.27.1:
- primary domain: injective objects in a category, expressed through extension across
  monomorphisms;
- sampled core/canonical declarations:
  `Injective`,
  `Injective.factors`,
  `Injective.factorThru`;
- best owner abstraction: `Injective J`;
- primitive data: only the object `J : C`;
- derived API: the extension existence clause `Injective.factors` and the chosen extension
  `Injective.factorThru`;
- source/core/bridge triage:
  `source-facing`: the textbook predicate that an object is injective;
  `core/canonical`: `Injective`;
  `bridge/view`: the explicit extension property `Injective.factors`.

No local wrapper is needed: the source notion is already owned canonically by `Injective`. -/

variable {C : Type u} [Category.{v} C]

/- Definition 12.27.1: an object `J` is injective if every morphism `A ⟶ J` extends across every
monomorphism `A ⟶ B`; this is the canonical notion `Injective J`. -/
recall Injective

/- Companion recall: `Injective.factors` is the extension property for injective objects,
producing for `g : A ⟶ J` and a monomorphism `f : A ⟶ B` a morphism `B ⟶ J` with `f ≫ h = g`. -/
recall Injective.factors

end CategoryTheory
