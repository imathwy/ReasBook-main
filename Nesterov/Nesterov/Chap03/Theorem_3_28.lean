import Mathlib.Tactic.Recall
import Nesterov.Chap03.Theorem_3_1_23

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 3.28 lies in the chapter's convex composite minimization / first-order optimality
domain.

Sampled owner-style declarations:
- `ConvexOn.isMinOn_iff_variational_inequality_of_hasGradientAt` in `Chap02/Theorem_2_29`
- `ConvexOn.isMinOn_add_iff_neg_hasGradient_mem_constrainedSubdifferential`
  in `Chap03/Theorem_3_1_23`
- `ConvexOn.isMinOn_add_iff_variational_inequality_of_hasGradientAt`
  in `Chap03/Theorem_3_1_23`
- `isMinOn_add_convex_iff_forall_inner_gradient_add_ge` in `Chap03/Theorem_3_1_23`

Best owner abstraction:
- `ConvexOn.isMinOn_add_iff_neg_hasGradient_mem_constrainedSubdifferential`, the primitive
  gradient-witness owner theorem for convex composite minimization on a real inner-product space,
  phrased through the chapter's constrained-subdifferential owner.

Primitive data:
- `ConvexOn ℝ Q f`
- `ConvexOn ℝ Q Ψ`
- `xStar ∈ Q`
- `HasGradientAt f g xStar`

Derived API:
- the raw variational-inequality bridge
  `ConvexOn.isMinOn_add_iff_variational_inequality_of_hasGradientAt`
- the source-facing gradient specialization
  `isMinOn_add_convex_iff_forall_inner_gradient_add_ge`

Source/core/bridge triage:
- source-facing: Theorem 3.28's variational inequality for minimizing `x ↦ f x + Ψ x` on `Q`
- core/canonical: `ConvexOn.isMinOn_add_iff_neg_hasGradient_mem_constrainedSubdifferential`
- bridge/view: `ConvexOn.isMinOn_add_iff_variational_inequality_of_hasGradientAt` and
  `isMinOn_add_convex_iff_forall_inner_gradient_add_ge`

This file is recall-only. The earlier duplicate local theorem has already been removed, and the
upstream owner file now carries the right abstraction layer: general real inner-product spaces, no
redundant `Convex ℝ Q` binder, and only pointwise differentiability at `xStar` for the
gradient-based view. Accordingly, Theorem 3.28 recalls that source-facing corollary directly
rather than rebuilding a parallel local bridge. -/

recall isMinOn_add_convex_iff_forall_inner_gradient_add_ge
