import Mathlib.Tactic.Recall
import LecturesConvexOptimization_Nesterov_2018.Chap03.Lemma_3_6

-- Declarations for this item will be appended below by the statement pipeline.

/- Corollary 3.1.8 is a recall-only item in the chapter's extended-valued
constrained-subdifferential domain.

Primary domain:
- convexity and lower-semicontinuity consequences of nonempty constrained subdifferentials for
  `WithTop ℝ`-valued functions on Euclidean space.

Sampled owner-style declarations:
- `withTopRealPart`
- `constrainedSubdifferential`
- `convexOn_of_constrainedSubdifferential_nonempty`
- `lowerSemicontinuousOn_of_constrainedSubdifferential_nonempty`

Best owner abstraction:
- the owner theorem pair
  `convexOn_of_constrainedSubdifferential_nonempty` and
  `lowerSemicontinuousOn_of_constrainedSubdifferential_nonempty`,
  built from the chapter owner objects `withTopRealPart` and
  `constrainedSubdifferential`

Primitive data:
- a convex feasible set `Q`
- a `WithTop ℝ`-valued objective `f`
- pointwise nonemptiness of `constrainedSubdifferential Q f x` on `Q`

Derived API:
- convexity of `withTopRealPart f` on `Q`
- lower semicontinuity of `withTopRealPart f` on `Q`

Source/core/bridge triage:
- source-facing: the textbook corollary collecting the convexity and lower-semicontinuity
  consequences
- core/canonical: `withTopRealPart` and `constrainedSubdifferential`
- bridge/view: none; both consequences already exist upstream with the exact public interfaces
  needed here

The previous file-level conjunction theorem was a redundant wrapper around those two owner
consequences, and it had no downstream users. This file therefore keeps only direct recalls of the
upstream owner theorems instead of a parallel local packaging layer. -/

recall convexOn_of_constrainedSubdifferential_nonempty

recall lowerSemicontinuousOn_of_constrainedSubdifferential_nonempty
