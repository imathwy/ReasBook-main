import Mathlib.CategoryTheory.Noetherian
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/- Domain-style sampling for Definition 12.9.2:
- primary domain: Artinian objects and the resulting objectwise notion of an Artinian category;
- sampled owner-level declarations:
  `isArtinianObject`,
  `IsArtinianObject`,
  `isArtinianObject_iff_antitone_chain_condition`,
  `Artinian`;
- best owner abstraction: the canonical object property `isArtinianObject : ObjectProperty C`;
- primitive data: the owner object property `isArtinianObject`;
- derived API: the pointwise predicate `IsArtinianObject X`, the antitone-chain characterization
  `isArtinianObject_iff_antitone_chain_condition`, and the stronger bundled class `Artinian`.

Source/core/bridge triage:
- `source-facing`: the textbook clause that an object `X` is Artinian, and the textbook condition
  that a category is Artinian iff `∀ X : C, IsArtinianObject X`;
- `core/canonical`: `isArtinianObject`, `IsArtinianObject`;
- `bridge/view`: the characterization theorem
  `isArtinianObject_iff_antitone_chain_condition`, and the stronger bundled class `Artinian`
  whose field `Artinian.isArtinianObject` implies the source-facing category condition.
-/

/- Definition 12.9.2 (1): the owner abstraction for Artinian objects is the canonical object
property `isArtinianObject`, whose values are the Artinian objects of `C`. -/
recall isArtinianObject : ObjectProperty C

/- Companion recall: for a specific object `X`, the textbook predicate that `X` is Artinian is the
canonical proposition `IsArtinianObject X`. -/
recall IsArtinianObject

/- Companion recall: the descending-chain formulation of an Artinian object is the canonical theorem
`isArtinianObject_iff_antitone_chain_condition`. -/
recall isArtinianObject_iff_antitone_chain_condition

/- Definition 12.9.2 (2): a category is Artinian in the textbook sense exactly when every object
is Artinian, i.e. when the proposition `∀ X : C, IsArtinianObject X` holds. Unlike the stronger
bundled owner class `Artinian`, this source-facing condition does not also package essential
smallness. -/
#check ∀ X : C, IsArtinianObject X

/- Companion recall: mathlib's canonical class `Artinian` packages the stronger
notion that `C` is essentially small and every object of `C` is Artinian. -/
recall Artinian

/- Bridge recall: the field `Artinian.isArtinianObject` recovers the source-facing objectwise
Artinian condition from the stronger bundled class `Artinian`. -/
recall Artinian.isArtinianObject

end CategoryTheory
