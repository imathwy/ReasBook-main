import Mathlib.CategoryTheory.Noetherian
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/- Domain-style sampling for Definition 12.9.3:
- primary domain: Noetherian objects and the resulting objectwise notion of a Noetherian category;
- sampled owner-level declarations:
  `isNoetherianObject`,
  `IsNoetherianObject`,
  `isNoetherianObject_iff_monotone_chain_condition`,
  `Noetherian`;
- best owner abstraction: the canonical object property
  `isNoetherianObject : ObjectProperty C`;
- primitive data: the owner object property `isNoetherianObject`;
- derived API: the pointwise predicate `IsNoetherianObject X`, the monotone-chain
  characterization `isNoetherianObject_iff_monotone_chain_condition`, and the stronger bundled
  class `Noetherian`.

Source/core/bridge triage:
- `source-facing`: the textbook clause that an object `X` is Noetherian, and the textbook
  condition that a category is Noetherian iff `∀ X : C, IsNoetherianObject X`;
- `core/canonical`: `isNoetherianObject`, `IsNoetherianObject`;
- `bridge/view`: the characterization theorem
  `isNoetherianObject_iff_monotone_chain_condition`, and the stronger bundled class
  `Noetherian` whose field `Noetherian.isNoetherianObject` implies the source-facing category
  condition.
-/

/- Definition 12.9.3: the owner abstraction for Noetherian objects is the canonical object
property `CategoryTheory.isNoetherianObject`, whose values are the Noetherian objects of `C`. -/
recall CategoryTheory.isNoetherianObject : ObjectProperty C

/- Companion recall: for a specific object `X`, the textbook predicate that `X` is Noetherian is
the canonical proposition `CategoryTheory.IsNoetherianObject X`. -/
recall IsNoetherianObject

/- Companion recall: the ascending-chain formulation of a Noetherian object is the canonical theorem
`CategoryTheory.isNoetherianObject_iff_monotone_chain_condition`. -/
recall isNoetherianObject_iff_monotone_chain_condition

/- Definition 12.9.3: a category is Noetherian in the textbook sense exactly when every object
is Noetherian, i.e. when the proposition `∀ X : C, IsNoetherianObject X` holds. Unlike the
stronger bundled owner class `Noetherian`, this source-facing condition does not also package
essential smallness. -/
#check ∀ X : C, IsNoetherianObject X

/-
Companion recall: mathlib's canonical class `CategoryTheory.Noetherian` packages the stronger
notion that `C` is essentially small and every object of `C` is Noetherian.
-/
recall Noetherian

/- Bridge recall: the field `Noetherian.isNoetherianObject` recovers the source-facing objectwise
Noetherian condition from the stronger bundled class `Noetherian`. -/
#check Noetherian.isNoetherianObject

end CategoryTheory
