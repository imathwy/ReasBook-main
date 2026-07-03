import Mathlib.Tactic.Recall
import Nesterov.Chap03.Lemma_3_3

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 3.1.2.1 lies in the chapter's support-function domain.

Primary domain:
- support functions of subsets of a real inner-product space and their behavior under convex hulls
  of two-set unions.

Sampled owner-style declarations:
- `supportFunction` from `Definition_3_9`
- `supportFunction_apply`
- `supportFunction_convexHull_union_eq_max` from `Lemma_3_3`
- the duplicate local theorem shell in `Lemma_3_1_3`

Best owner abstraction:
- the exact upstream theorem `supportFunction_convexHull_union_eq_max` from `Lemma_3_3`, stated at
  the same ambient owner level as `supportFunction`

Primitive data:
- two sets `Q₁ Q₂ : Set E`
- a direction `x : E`

Derived API:
- the support function of `convexHull ℝ (Q₁ ∪ Q₂)`
- its identification with the pointwise maximum of the two support functions

Source/core/bridge triage:
- source-facing: this two-set convex-hull support-function identity
- core/canonical: the exact upstream theorem `supportFunction_convexHull_union_eq_max`
- bridge/view: none needed; the target interface already exists upstream

This file previously repeated the exact upstream theorem already present in `Lemma_3_3` and again
in `Lemma_3_1_3`. Since the project already has the precise owner interface, this numbered item is
now a direct recall rather than a third parallel theorem shell. The textbook `ℝⁿ` statement is a
specialization of that generalized owner theorem.
-/

recall supportFunction_convexHull_union_eq_max
