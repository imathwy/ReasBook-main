import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable (k : Type u) (E : Type v) [Field k] [Field E] [Algebra k E]

/- Domain-style sampling:
* primary domain: relative perfect closures and purely inseparable intermediate subextensions;
* sampled owner declarations:
  `perfectClosure`,
  `le_perfectClosure_iff`,
  `IntermediateField.isPurelyInseparable_adjoin_simple_iff_natSepDegree_eq_one`;
* best owner abstraction: the canonical intermediate field `perfectClosure k E`, already tagged in
  mathlib with Stacks `09HH`;
* primitive data: none locally, since the owner object and its canonical characterizations already
  exist upstream;
* derived API: the elementwise simple-extension criterion is recovered from the owner theorem
  `le_perfectClosure_iff` together with the standard simple-extension bridge, so it should not be
  the main public entry here.

Layer triage:
* `source-facing`: Lemma 9.14.4 identifies the subextension of `E / k` consisting of the elements
  purely inseparable over `k`;
* `core/canonical`: `perfectClosure k E`;
* `bridge/view`: membership and simple-extension characterizations of `perfectClosure`.

This file should therefore be a recall surface for the canonical owner `perfectClosure`, not a
local theorem whose statement hides that owner behind an elementwise reformulation.
-/

/- Lemma 9.14.4: the subextension of `E / k` consisting of the elements of `E` that are purely
inseparable over `k` is the canonical intermediate field `perfectClosure k E`. -/
#check perfectClosure k E

end

/- Companion recall: `perfectClosure k E` is the owner-level relative perfect closure, and the
source elementwise criterion is a derived bridge rather than the main declaration of this item. -/
recall perfectClosure
