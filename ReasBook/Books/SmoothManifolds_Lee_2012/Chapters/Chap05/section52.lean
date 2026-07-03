import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_5_52 (from Chap05/Sec05_36) -/
-- Semantic recall note: `lean_leansearch` was unavailable in this environment, so the exercise
-- is matched directly against the local formalization of the preceding theorem.

/- Exercise 5.52: prove the preceding theorem. In this formalization, the forward existence result
is isolated as a companion theorem, and the exercise's main content is the canonical preceding
theorem itself. -/

/- Forward direction: a local slice condition with boundary yields the induced
manifold-with-boundary structure and smooth-embedding conclusion. -/
recall satisfiesLocalSliceConditionWithBoundary_has_manifold_with_boundary_structure

/- Main statement: the preceding theorem is exactly the local-slice criterion for embedded
submanifolds with boundary. -/
recall local_slice_criterion_for_embedded_submanifold_with_boundary
