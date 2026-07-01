import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling:
* primary domain: injectivity of ring homomorphisms out of fields and, more generally, simple
  rings;
* sampled owner declarations:
  `DivisionRing.isSimpleRing`,
  `RingHom.injective`,
  `IsSimpleRing.iff_injective_ringHom`,
  `FaithfulSMul.algebraMap_injective`;
* best owner abstraction: `RingHom.injective`;
* primitive data: a ring homomorphism `φ : F →+* R` with field source and nontrivial target;
* derived API: `Function.Injective φ`.

Layer triage:
* `source-facing`: the textbook field-specialized injectivity statement;
* `core/canonical`: `RingHom.injective`, using the owner fact that a field is a simple ring;
* `bridge/view`: `FaithfulSMul.algebraMap_injective` for the special case of algebra maps.

This item should therefore remain a direct recall of the canonical owner theorem, not a local
field-specific wrapper.
-/

/- Lemma 9.6.1: if `F` is a field and `R` is a nonzero ring, then any ring homomorphism
`φ : F →+* R` is injective. This is the field-specialized textbook reading of the canonical
mathlib theorem `RingHom.injective`, whose native owner signature is stated for homomorphisms out
of simple rings into nontrivial semirings. -/
recall RingHom.injective
