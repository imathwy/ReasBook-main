import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory

-- Semantic recall: `Scheme.zariskiPretopology` is the canonical owner for Zariski coverings of
-- schemes. Its pretopology structure packages exactly the three source clauses: singleton
-- isomorphism covers, stability under refinement, and stability under pullback.

/- Lemma 34.3.2: this is a pure canonical recall. In mathlib, Zariski coverings of schemes are
packaged by `AlgebraicGeometry.Scheme.zariskiPretopology`, and the source lemma's three
assertions are the standard pretopology axioms on that owner. -/
recall AlgebraicGeometry.Scheme.zariskiPretopology
