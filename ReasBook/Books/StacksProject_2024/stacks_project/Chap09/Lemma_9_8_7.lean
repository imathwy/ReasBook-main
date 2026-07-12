import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {k : Type u} {E : Type v} [Field k] [Field E] [Algebra k E]

/- Domain-style sampling for Lemma 9.8.7:
- primary domain: algebraic field extensions and the intermediate field cut out by algebraic
  elements;
- sampled owner declarations:
  `algebraicClosure`,
  `mem_algebraicClosure_iff`,
  `le_algebraicClosure`,
  `le_algebraicClosure_iff`;
- best owner abstraction: the canonical intermediate field `algebraicClosure k E`;
- primitive data: none locally, since the source statement is already owned by mathlib's
  `algebraicClosure`;
- derived API: the membership/specification theorem `mem_algebraicClosure_iff` and the order
  characterization `le_algebraicClosure_iff`.

Source/core/bridge triage:
- `source-facing`: the set of elements of `E` algebraic over `k` forms a subextension of `E / k`;
- `core/canonical`: `algebraicClosure k E : IntermediateField k E`;
- `bridge/view`: `mem_algebraicClosure_iff`, which identifies membership in the owner with the
  textbook pointwise algebraicity predicate.

This file should therefore remain a pure recall surface: the source statement is already the
canonical owner declaration, so any local `def` or wrapper theorem would only duplicate upstream
API. -/

/- Lemma 9.8.7 (Tag 09GI): for a field extension `E / k`, the elements of `E` algebraic over `k`
form a subextension of `E / k`; in mathlib this subextension is the canonical intermediate field
`algebraicClosure k E`, i.e. the relative algebraic closure of `k` in `E`. -/
recall algebraicClosure

/- Companion recall: membership in `algebraicClosure k E` is exactly algebraicity over `k`. -/
recall mem_algebraicClosure_iff
