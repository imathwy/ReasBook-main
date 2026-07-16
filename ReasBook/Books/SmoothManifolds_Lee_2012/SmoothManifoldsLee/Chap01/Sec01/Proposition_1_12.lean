import Mathlib.Tactic.Recall
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap01.Sec01.Definition_1_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Proposition 1.12 (Manifolds Are Locally Compact): the canonical owner for this statement is
`TopologicalManifold.locallyCompactSpace_of_topologicalManifold`. -/
recall TopologicalManifold.locallyCompactSpace_of_topologicalManifold
  (n : ℕ) (M : Type u) [TopologicalSpace M] [TopologicalManifold n M] :
    LocallyCompactSpace M
