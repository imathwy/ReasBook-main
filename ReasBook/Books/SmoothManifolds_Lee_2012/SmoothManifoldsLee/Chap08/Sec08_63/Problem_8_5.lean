import Mathlib.Tactic.Recall
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap08.Sec08_55.Proposition_8_11

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

-- Semantic recall note: `lean_leansearch` surfaced mathlib's local-frame owner `IsLocalFrameOn`,
-- and the repository owner file `Sec08_55/Proposition_8_11.lean` confirms that Proposition 8.11
-- is formalized here by three separate extension theorems. This item therefore recalls those exact
-- theorem owners instead of the ambient predicate.

/- Problem 8-5 (1): Proposition 8.11 first asserts local completion of a linearly independent
smooth `k`-tuple on an open set to a smooth local frame near a chosen point. -/
recall exists_localFrame_completion_at_of_linearlyIndependentOn

/- Problem 8-5 (2): Proposition 8.11 next asserts extension of linearly independent tangent
vectors at one point to a smooth local frame on a neighborhood. -/
recall exists_localFrame_extending_tangentVectors

/- Problem 8-5 (3): Proposition 8.11 finally asserts extension of a linearly independent smooth
frame given along a closed subset to a smooth local frame on an open neighborhood. -/
recall exists_localFrame_extension_of_closed
