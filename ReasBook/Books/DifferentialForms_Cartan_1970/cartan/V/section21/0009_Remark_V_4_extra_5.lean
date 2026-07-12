import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain sampling: this file lives in general topology/compactness. The upstream owner layer is
-- mathlib's Tychonoff API in `Topology/Compactness/Compact`, whose primitive theorem-level owners
-- are `isCompact_pi_infinite` and `isCompact_univ_pi`, with `Pi.compactSpace` as the derived
-- typeclass-level packaging.

/- Remark V.4-extra-5: the source note is a direct canonical recall of Tychonoff compactness for
products. The special-case compactness argument just established is subsumed by the canonical
mathlib Tychonoff owners `isCompact_pi_infinite` and `isCompact_univ_pi`; when each factor is
itself a compact space, the corresponding product compactness is packaged by the instance
`Pi.compactSpace`. -/
recall isCompact_pi_infinite
recall isCompact_univ_pi
recall Pi.compactSpace
