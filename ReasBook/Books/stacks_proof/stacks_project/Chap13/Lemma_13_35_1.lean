import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.ObjectProperty

namespace CategoryTheory.ObjectProperty.ExtensionProductNotation

/- Source-facing notation for the extension product of object properties in Section `13.35`:
`A ⋆ B` is owned canonically by `CategoryTheory.ObjectProperty.extensionProduct A B`. -/
scoped notation:70 A:70 " ⋆ " B:71 =>
  extensionProduct A B

end CategoryTheory.ObjectProperty.ExtensionProductNotation

open scoped CategoryTheory.ObjectProperty.ExtensionProductNotation

/- Domain-style sampling for Lemma 13.35.1:
- primary domain: object properties/full subcategories in a triangulated category, with the
  extension product operation;
- sampled core/canonical declarations:
  `CategoryTheory.ObjectProperty.extensionProduct`,
  `CategoryTheory.ObjectProperty.extensionProduct_iff`,
  `CategoryTheory.ObjectProperty.extensionProduct_assoc`,
  `CategoryTheory.ObjectProperty.extensionProductIter`;
- best owner abstraction: `CategoryTheory.ObjectProperty.extensionProduct` is already the canonical
  owner for the extension product of full subcategories, so the source lemma should remain a pure
  recall of its upstream associativity theorem rather than introduce a parallel local statement;
- primitive-vs-derived split:
  primitive data are object properties `P`, `Q`, and `R`;
  derived API is the canonical associativity equality for their extension products.

Source/core/bridge triage:
- `source-facing`: associativity of the extension product `\mathcal A \star \mathcal B` of full
  subcategories;
- `core/canonical`: `CategoryTheory.ObjectProperty.extensionProduct` and
  `CategoryTheory.ObjectProperty.extensionProduct_assoc`;
- `bridge/view`: the later chapter notation `A ⋆ B` is only surface syntax for the same owner.
-/

/- Lemma 13.35.1: in a triangulated category, the extension product of full subcategories is
associative. This is already the canonical mathlib theorem
`CategoryTheory.ObjectProperty.extensionProduct_assoc`. -/
recall extensionProduct_assoc
