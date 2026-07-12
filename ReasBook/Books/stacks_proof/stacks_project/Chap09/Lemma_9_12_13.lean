import Mathlib.FieldTheory.SeparableClosure
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Lemma 9.12.13:
- primary domain: separable elements, separable extensions, and the canonical intermediate field
  they define inside a field extension;
- sampled owner declarations:
  * `separableClosure`
  * `mem_separableClosure_iff`
  * `le_separableClosure_iff`
  * `eq_separableClosure_iff`
- best owner abstraction: the mathlib owner `separableClosure k E : IntermediateField k E`;
- primitive data: only the ambient field extension `E / k`;
- derived API: the pointwise membership criterion `mem_separableClosure_iff` and the maximality and
  uniqueness characterizations `le_separableClosure_iff` and `eq_separableClosure_iff`.

Source/core/bridge triage:
- `source-facing`: the textbook subfield of elements of `E` that are separable over `k`;
- `core/canonical`: `separableClosure k E`;
- `bridge/view`: `mem_separableClosure_iff`, which identifies the source description with the
  canonical owner predicate.

This item should therefore remain a pure recall surface. Any local definition of the set or
intermediate field of separable elements would only duplicate the upstream owner without adding
mathematics.
-/

/- Lemma 9.12.13: the elements of a field extension `E / k` that are separable over `k` form the
canonical intermediate field `separableClosure k E`, i.e. the maximal separable subextension of
`E / k`. -/
recall separableClosure

/- Companion recall: an element of `E` lies in `separableClosure k E` exactly when it is separable
over `k`; this is the canonical theorem `mem_separableClosure_iff`. -/
recall mem_separableClosure_iff
