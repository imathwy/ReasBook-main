import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory

universe v u

/- Domain-style sampling for Definition 12.28.1:
- primary domain: projective objects in a category, expressed through lifting across epimorphisms;
- sampled core/canonical declarations:
  `Projective`,
  `Projective.factors`,
  `Projective.factorThru`,
  `EnoughProjectives`;
- best owner abstraction: `Projective P`;
- primitive data: only the object `P : C`;
- derived API: the lifting existence clause `Projective.factors`, the chosen lift
  `Projective.factorThru`, and later chapter packaging such as `EnoughProjectives`;
- source/core/bridge triage:
  `source-facing`: the textbook predicate that an object is projective;
  `core/canonical`: `Projective`;
  `bridge/view`: the explicit lifting property `Projective.factors`.

No local wrapper is needed: the source notion is already owned canonically by `Projective`. -/

variable {C : Type u} [Category.{v} C]

/- Definition 12.28.1: in the chapter's abelian-category setting, an object `P` is projective if
every morphism `P ⟶ B` lifts across every epimorphism `A ⟶ B`; this is the canonical notion
`Projective P`. -/
recall Projective

/- Companion recall: `Projective.factors` is the lifting property for projective objects,
producing for `f : P ⟶ B` and an epimorphism `e : A ⟶ B` a morphism `P ⟶ A` with `f' ≫ e = f`. -/
recall Projective.factors

end CategoryTheory
