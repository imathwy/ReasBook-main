import Mathlib.Tactic.Recall
import LinearRepresentations_Serre_1977.Chap03.Corollary_3_3_1_2

-- Declarations for this item will be appended below by the statement pipeline.

/- Source/core/bridge triage:
* source-facing: this remark only records the complex case of the chapter's index bound for an
  irreducible finite-dimensional representation.
* core/canonical: the owner is
  `Representation.finrank_le_index_of_commutative_subgroup` from Corollary `3-3.1-2`.
* bridge/view: no new declaration is needed here, because the remark is exactly the chapter-8
  reading of that upstream owner theorem at `k = ℂ`.

Remark 8-8.1-4: without assuming that `A` is normal, the divisibility statement from Corollary
`8-8.1-3` may fail, but Corollary `3-3.1-2` still gives the index bound for irreducible
finite-dimensional complex representations. -/
recall Representation.finrank_le_index_of_commutative_subgroup
