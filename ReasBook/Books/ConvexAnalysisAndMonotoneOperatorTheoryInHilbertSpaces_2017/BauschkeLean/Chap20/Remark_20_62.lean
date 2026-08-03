import Mathlib.Tactic.Recall
import BauschkeLean.Chap20.Proposition_20_58
import BauschkeLean.Chap20.Proposition_20_61

-- Declarations for this item will be appended below by the statement pipeline.

namespace SetValuedOperator

/- Source/core/bridge triage:
- `source-facing`: Remark 20.62 records the converse Fitzpatrick contact-set descriptions of a
  maximally monotone operator.
- `core/canonical`: the owner declarations are
  `Maximal.eq_pairingEqualityOperator_fitzpatrickFunction` and
  `Maximal.eq_pairingEqualityOperator_conjugateTranspose_fitzpatrickFunction` and
  are built from
  `Maximal IsMonotone A`, the Fitzpatrick owner `F[A]`, and the pairing-contact owner
  `pairingEqualityOperator`.
- `bridge/view`: the graph/contact-set recalls are companion descriptions of the same recovered
  operator, not new owners.

Primitive data: maximal monotonicity `Maximal IsMonotone A` together with the canonical Fitzpatrick
owner `F[A]`.
Derived API: the recovered pairing-equality operators and their graph/contact-set descriptions. -/

-- Semantic recall note: `lean_leansearch` did not return a relevant mathlib owner for these
-- Fitzpatrick contact-set converses, so this item stays as a local Chapter 20 recall block over
-- Proposition 20.58 and Proposition 20.61.

/- Remark 20.62: Proposition 20.58 and Proposition 20.61 recover a maximally monotone operator
from the Fitzpatrick contact-set descriptions, giving converses to the canonical
pairing-equality-operator construction of Theorem 20.46. -/
recall Maximal.eq_pairingEqualityOperator_fitzpatrickFunction

/- Companion recall: Proposition 20.61 identifies the recovered operator itself with the
transpose-conjugate pairing-contact owner. -/
recall Maximal.eq_pairingEqualityOperator_conjugateTranspose_fitzpatrickFunction

/- Companion recall: Proposition 20.58 identifies the graph with the Fitzpatrick contact set. -/
recall Maximal.graph_eq_setOf_fitzpatrickFunction_eq_inner

/- Companion recall: Proposition 20.61 identifies the graph with the transpose-conjugate
Fitzpatrick contact set. -/
recall Maximal.graph_eq_setOf_conjugateTranspose_fitzpatrickFunction_eq_inner

end SetValuedOperator
