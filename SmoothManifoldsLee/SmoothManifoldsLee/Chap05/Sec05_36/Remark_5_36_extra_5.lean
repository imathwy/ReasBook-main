import Mathlib.Tactic.Recall
import SmoothManifoldsLee.Chap05.Sec05_36.Theorem_5_53

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: `lean_leansearch` was unavailable in this environment; this remark is
-- matched against the owner theorem already used in the Theorem 5.29 codomain-restriction
-- formalization and recalled again in `Theorem_5_53.lean`.

/-
Remark 5.36-extra-5: as in Theorem 5.29, the boundaryless ambient-manifold hypothesis is not
mathematically needed for part (b), the codomain-restriction statement. In the local
formalization, that observation is represented by the canonical owner theorem already recalled in
Theorem 5.53 (2).
-/
recall Manifold.IsSmoothEmbedding.contMDiff_toSubtype
