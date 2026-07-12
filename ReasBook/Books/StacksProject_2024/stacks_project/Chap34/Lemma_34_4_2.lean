import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

/- Semantic recall:
`lean_leansearch` located the canonical scheme-site owners
`AlgebraicGeometry.Scheme.zariskiTopology`,
`AlgebraicGeometry.Scheme.etaleTopology`, and the exact bridge theorem
`AlgebraicGeometry.Scheme.zariskiTopology_le_etaleTopology`.
This matches the source lemma directly: every Zariski covering sieve is an étale covering sieve. -/

/- Lemma 34.4.2: any Zariski covering is an étale covering. This is a pure canonical recall:
mathlib already provides the inclusion `Scheme.zariskiTopology ≤ Scheme.etaleTopology`. -/
recall AlgebraicGeometry.Scheme.zariskiTopology_le_etaleTopology

#check Scheme.zariskiTopology_le_etaleTopology
