import Mathlib.Tactic.Recall
import LecturesConvexOptimization_Nesterov_2018.Chap03.Theorem_3_1_1_4

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 3.5 is a source-facing recall in the chapter's closed-convex-function domain.

Primary domain:
- closed convex `WithTop ℝ`-valued functions and their real sublevel sets.

Sampled owner-style declarations:
- `ClosedConvexOn`
- `ClosedConvexFunction`
- `ClosedConvexFunction.isClosed_convex_sublevelSet`

Best owner abstraction:
- `ClosedConvexFunction`

Primitive data:
- the effective-domain closed-convex owner hypothesis `ClosedConvexFunction f`

Derived API:
- `ClosedConvexFunction.isClosed_convex_sublevelSet`

Source/core/bridge triage:
- source-facing: Theorem 3.5, the sublevel-set consequence of closed convexity
- core/canonical: `ClosedConvexFunction`
- bridge/view: `ClosedConvexOn` and the constrained-epigraph API behind it

This file therefore reuses the canonical owner theorem directly, without introducing a second
sublevel-set wrapper or theorem-shaped alias. -/

recall ClosedConvexFunction.isClosed_convex_sublevelSet
