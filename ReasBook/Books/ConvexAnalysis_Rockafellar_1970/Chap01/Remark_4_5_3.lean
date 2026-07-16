import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2

-- Declarations for this item will be appended below by the statement pipeline.

section

/- 
Source/core/bridge triage:
- `source-facing`: Remark 4.5.3 says the norm on `ℝⁿ` is convex, with the one-dimensional case
  giving convexity of `abs`.
- `core/canonical`: the intrinsic owner theorem is mathlib's `convexOn_univ_norm` on an arbitrary
  real normed space.
- `bridge/view`: first pass to the chapter owner theorem for `‖·‖` through
  `Function.isConvex_coe_of_convexOn_univ`, then specialize to dimension one and rewrite
  `‖x‖ = |x|` using `Real.norm_eq_abs`.
- Primitive data vs derived API: the primitive object is the canonical norm function `‖·‖`; the
  one-dimensional `abs` statement is a downstream bridge specialization.
- Domain-style sampling used here: `convexOn_univ_norm`, `ConvexOn.convex_epigraph`,
  `Function.IsConvex`, `Function.isConvex_coe_of_convexOn_univ`, `Function.isConvex_norm`,
  and `Real.norm_eq_abs`.
- Layer target: `core/canonical` for the owner theorem `Function.isConvex_norm`; the
  one-dimensional bridge is intentionally downstream.
-/

/- Remark 4.5.3: the intrinsic owner fact is the canonical theorem `convexOn_univ_norm`; the
textbook `ℝⁿ` statement is an exact specialization, so the main entry remains a direct recall
rather than a parallel local wrapper theorem. -/
recall convexOn_univ_norm

section

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

-- Proof sketch: pass from `convexOn_univ_norm` to the chapter owner predicate
-- `Function.IsConvex` through the canonical coercion bridge.
/-- Remark 4.5.3 on the chapter owner surface: the norm is globally convex as a
`WithTopBot ℝ`-valued function on any real normed space. -/
theorem Function.isConvex_norm :
    ((norm : E → ℝ).toWithTopBot).IsConvex ℝ := by
  exact Function.isConvex_coe_of_convexOn_univ convexOn_univ_norm

end

end
