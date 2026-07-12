import Mathlib.Tactic.Recall
import SmoothManifolds_Lee_2012.Chap02.Sec02_11.Definition_2_11_extra_2

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: `lean_leansearch` points to manifold-extension APIs in core mathlib, and
-- local repo search confirms that Problem 5-18 uses
-- `Function.isSmoothOn_iff_exists_local_extension` as the project owner for Lee's extension
-- lemma for functions on submanifolds.

/- Problem 5-17: this problem asks for a proof of Lemma 5.34, the extension lemma for functions on
submanifolds, so the canonical recall surface is the existing theorem
`Function.isSmoothOn_iff_exists_local_extension`. Applied to the submanifold subtype `S`, it says
that an intrinsically smooth function is exactly one that admits a smooth ambient local extension
near each point. -/
recall Function.isSmoothOn_iff_exists_local_extension
