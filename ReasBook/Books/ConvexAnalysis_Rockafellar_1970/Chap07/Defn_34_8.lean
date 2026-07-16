import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_5

/- Definition 34.8 is recall-only in the project API: the textbook simplicity condition for a
concave-convex saddle-function is already owned by `IsSimple` in `Defn_34_5`, now stated on the
intrinsic affine ambient layer needed by `ri[𝕜](·)` and `intrinsicClosure`, with companion
unpacking theorem `isSimple_iff` and the two canonical object-prefix projection lemmas for the
slice-domain clauses. -/
recall SaddleFunction.IsSimple
recall SaddleFunction.isSimple_iff
recall SaddleFunction.IsSimple.right_slice_dom_subset
recall SaddleFunction.IsSimple.left_slice_dom_subset
