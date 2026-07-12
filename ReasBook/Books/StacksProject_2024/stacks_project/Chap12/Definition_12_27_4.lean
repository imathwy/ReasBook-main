import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory

universe v u

/- Domain-style sampling for Definition 12.27.4:
- primary domain: injective presentations and the category-level predicate of having enough
  injectives;
- sampled core/canonical declarations:
  `InjectivePresentation`,
  `EnoughInjectives`,
  `EnoughInjectives.presentation`;
- best owner abstraction: `EnoughInjectives C`;
- primitive data: for each object `X : C`, the existence datum
  `Nonempty (InjectivePresentation X)`;
- derived API: the owner field `EnoughInjectives.presentation X`.

This item is `core/canonical`: the source notion is already owned by mathlib's
`EnoughInjectives`, so the file should remain a direct recall rather than introducing a local
wrapper or alias. -/

section

variable {C : Type u} [Category.{v} C]

/- Definition 12.27.4: the owner abstraction for "having enough injectives" is
`EnoughInjectives C`, meaning every object of `C` admits an injective presentation. -/
recall EnoughInjectives

/- Companion recall: the primitive data of `EnoughInjectives C` is
`EnoughInjectives.presentation`, witnessing `Nonempty (InjectivePresentation X)` for each
`X : C`. -/
recall EnoughInjectives.presentation

end

end CategoryTheory
