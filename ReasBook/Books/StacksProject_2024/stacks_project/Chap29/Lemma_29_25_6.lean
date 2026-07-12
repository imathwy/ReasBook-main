import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall: `lean_leansearch` returned the exact scheme-level owner
-- `AlgebraicGeometry.Flat.comp`, matching the source statement that compositions of flat
-- morphisms of schemes are flat. The local Chapter 29 files already use `AlgebraicGeometry.Flat`
-- as the canonical owner for flatness of scheme morphisms, so this item is recorded as a direct
-- recall instead of a duplicate wrapper theorem.

/- Lemma 29.25.6: the composition of flat morphisms is flat. -/
recall AlgebraicGeometry.Flat.comp
