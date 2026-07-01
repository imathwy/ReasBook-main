import Mathlib.Tactic.Recall
import SmoothManifoldsLee.Chap02.Sec02_09.Proposition_2_15

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: no `lean_leansearch` tool was available in this environment, so this
-- exercise is matched directly against the locally formalized preceding proposition.

/- Exercise 2.16: this exercise asks for proofs of the clauses of Proposition 2.15. In this
formalization, the preceding proposition is expressed through the canonical `Diffeomorph`
constructors `Diffeomorph.trans`, `Diffeomorph.pi`, and `Diffeomorph.restrictOpen`, together with
the open-map and diffeomorphic-relation statements below. -/
recall Diffeomorph.trans
recall Diffeomorph.pi
recall Diffeomorph.restrictOpen
recall diffeomorph_isOpenMap
recall diffeomorphic_refl
recall diffeomorphic_symm
recall diffeomorphic_trans
