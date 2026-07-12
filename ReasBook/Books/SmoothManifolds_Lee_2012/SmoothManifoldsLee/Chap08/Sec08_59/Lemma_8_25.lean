import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Tactic.Recall

open scoped ContDiff Manifold

-- Semantic recall note: `lean_leansearch` was unavailable in this environment, so this item was
-- matched directly against mathlib's `ContDiff.mlieBracket_vectorField` theorem.

/- Lemma 8.25. The Lie bracket of any pair of smooth vector fields is a smooth vector field.
In mathlib this is the canonical theorem `ContDiff.mlieBracket_vectorField`; its formal statement
includes the ambient completeness hypothesis on the model space that the manifold Lie-bracket API
uses downstream in this chapter. -/
recall ContDiff.mlieBracket_vectorField
