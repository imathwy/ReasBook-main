import Mathlib.Tactic.Recall
import LinearRepresentations_Serre_1977.Serre.Chap02.Proposition_2_2_2_1

/- Source/core/bridge triage:
- `source-facing`: Proposition 4-21 records Schur's lemma in the chapter's compact continuous
  complex setting.
- `core/canonical`: the repository already owns the source-facing Schur-lemma consequences in
  `Representation.intertwiningMap_eq_zero_of_not_isomorphic` and
  `Representation.intertwiningMap_eq_smul_id`.
- `bridge/view`: none; the Chapter 4 continuity and compactness hypotheses do not change these
  statements.

This item is therefore recall-only: reintroducing Chapter 4-local theorem names would duplicate
the earlier canonical owner surface without adding mathematical content or improving reuse.
-/

/- Proposition 4-21 (1): if two irreducible complex representations are not isomorphic, then every
intertwining map between them is zero. In Chapter 4 this is applied to continuous finite-dimensional
representations of compact groups, but the statement itself is already the canonical theorem
`Representation.intertwiningMap_eq_zero_of_not_isomorphic`. -/
recall Representation.intertwiningMap_eq_zero_of_not_isomorphic

/- Proposition 4-21 (2): every intertwining endomorphism of an irreducible finite-dimensional
complex representation is a scalar multiple of the identity. In Chapter 4 this is applied to
continuous representations of compact groups, but the statement itself is already the canonical
theorem `Representation.intertwiningMap_eq_smul_id`. -/
recall Representation.intertwiningMap_eq_smul_id
