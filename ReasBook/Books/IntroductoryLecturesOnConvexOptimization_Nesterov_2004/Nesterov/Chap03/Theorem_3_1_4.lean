import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Nesterov.Chap03.Theorem_3_1_1_4

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 3.1.4 is a source-facing recall in the chapter's closed-convex-function domain.

Primary domain:
- closed convex `WithTop ℝ`-valued functions and their real sublevel sets.

Sampled owner-style declarations:
- `ClosedConvexFunction`
- `ClosedConvexFunction.isClosed_convex_sublevelSet`

Source/core/bridge triage:
- source-facing: the sublevel-set consequence recorded as Theorem 3.1.4
- core/canonical: `ClosedConvexFunction`
- bridge/view: the epigraph-based owner API behind `ClosedConvexFunction`

Primitive data:
- the owner hypothesis `ClosedConvexFunction f`

Derived API:
- the recalled owner theorem `ClosedConvexFunction.isClosed_convex_sublevelSet`

This file therefore reuses the canonical owner theorem directly, without rebuilding the broader
five-result package that previously overreached the source theorem. -/

recall ClosedConvexFunction.isClosed_convex_sublevelSet
