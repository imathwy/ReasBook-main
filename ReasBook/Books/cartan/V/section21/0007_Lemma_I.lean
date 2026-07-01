import Mathlib

-- Domain sampling: this item lies in the sequential compactness / compactness domain for metric
-- spaces. The relevant owner declarations inspected before refinement were `IsSeqCompact`,
-- `SeqCompactSpace`, `IsSeqCompact.isCompact`, and `compactSpace_iff_seqCompactSpace`. The main
-- owner abstraction is `IsSeqCompact`, with `SeqCompactSpace` as the univ specialization. Primitive
-- data: `IsSeqCompact (univ : Set X)` (equivalently `[SeqCompactSpace X]`). Derived API:
-- `IsCompact (univ : Set X)` and hence compactness of the ambient space. Since Lemma I is the
-- source-facing implication direction rather than the full equivalence, the main entry should use
-- `IsSeqCompact.isCompact` directly.

variable {X : Type*} [MetricSpace X]

/- Lemma I. In a metric space, if every sequence has a convergent subsequence whose limit lies in
the space, then the space is compact. This is the `univ` specialization of mathlib's canonical
implication `IsSeqCompact.isCompact`. -/
#check (IsSeqCompact.isCompact : IsSeqCompact (Set.univ : Set X) → IsCompact (Set.univ : Set X))
