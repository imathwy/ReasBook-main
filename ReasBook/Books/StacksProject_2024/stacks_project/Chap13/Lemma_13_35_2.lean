import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.ObjectProperty

/- Domain-style sampling for Lemma 13.35.2:
- primary domain: object properties/full subcategories in a triangulated category, specifically
  the interaction of `extensionProduct` with retract/direct-summand closure;
- inspected owner declarations:
  `CategoryTheory.ObjectProperty.extensionProduct`,
  `CategoryTheory.ObjectProperty.retractClosure`,
  `CategoryTheory.ObjectProperty.extensionProduct_retractClosure_retractClosure_le`,
  `CategoryTheory.ObjectProperty.retractClosure_extensionProduct_retractClosure_retractClosure`;
- best owner abstraction: the ambient `CategoryTheory.ObjectProperty` operations
  `extensionProduct` and `retractClosure`, together with their canonical comparison theorems;
- layer: `core/canonical`; this numbered lemma is already an owner-level mathlib theorem, so the
  refined file should stay a direct recall rather than introduce a parallel wrapper;
- primitive data: the operations `P ↦ P.retractClosure` and `(P, Q) ↦ extensionProduct P Q`;
- derived API: the containment theorem
  `extensionProduct_retractClosure_retractClosure_le` and the induced equality after outer retract
  closure, `retractClosure_extensionProduct_retractClosure_retractClosure`.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma about saturation/direct-summand closure and the extension
  product of full subcategories;
- `core/canonical`: the owner operations `extensionProduct`, `retractClosure`, and their canonical
  mathlib theorems named below;
- `bridge/view`: none is needed here, because the numbered item already coincides exactly with the
  canonical owner-level statements.
-/

/- Lemma 13.35.2 (1): for full subcategories `\mathcal A` and `\mathcal B` of a triangulated
category, the extension product of their saturation/direct-summand closures is contained in the
saturation of their extension product. In mathlib this is the canonical theorem
`CategoryTheory.ObjectProperty.extensionProduct_retractClosure_retractClosure_le`. -/
recall extensionProduct_retractClosure_retractClosure_le

/- Lemma 13.35.2 (2): the saturation/direct-summand closure of the extension product of the
saturations of `\mathcal A` and `\mathcal B` coincides with the saturation of
`\mathcal A \star \mathcal B`. In mathlib this is the canonical theorem
`CategoryTheory.ObjectProperty.retractClosure_extensionProduct_retractClosure_retractClosure`. -/
recall retractClosure_extensionProduct_retractClosure_retractClosure
