import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory

-- Semantic recall: `lean_leansearch` identified `AlgebraicGeometry.Scheme.etalePretopology` as
-- the canonical owner for etale coverings of schemes. Its pretopology instances are exactly the
-- three clauses in the source lemma: singleton isomorphism covers, stability under composition,
-- and stability under base change.

/- Lemma 34.4.3: this is a pure canonical recall. In mathlib, etale coverings of schemes are
packaged by `AlgebraicGeometry.Scheme.etalePretopology`, and the source lemma's three assertions
are the standard pretopology axioms on that owner. -/
recall AlgebraicGeometry.Scheme.etalePretopology
