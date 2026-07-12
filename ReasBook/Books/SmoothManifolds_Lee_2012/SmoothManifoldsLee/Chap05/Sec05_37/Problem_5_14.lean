import Mathlib.Tactic.Recall
import SmoothManifolds_Lee_2012.Chap05.Sec05_33.Theorem_5_32

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: `lean_leansearch` returned only general diffeomorphism lemmas, while
-- local verification against `Theorem_5_32.lean` showed that this problem asks directly for that
-- theorem's proof, so the faithful statement-stage surface is a canonical recall.
/-
Problem 5-14: this problem asks for the proof of Theorem 5.32, namely the uniqueness of the
smooth structure on an immersed submanifold once the topology on the underlying space is fixed.
The canonical item-per-file surface is therefore the preceding theorem's statement itself.
-/
recall existsUnique_diffeomorph_refl_of_isImmersedSubmanifold
