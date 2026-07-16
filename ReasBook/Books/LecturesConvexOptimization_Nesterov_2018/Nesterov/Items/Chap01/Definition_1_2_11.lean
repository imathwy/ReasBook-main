import Mathlib.Tactic.Recall
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap01.Definition_1_2_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {Query : Type u} {Answer : Type v}

/- Definition 1.2.11 is a source-facing recall item in the Chapter 1 analytical-complexity
domain.

Layer targeted by this refinement:
* source-facing recall of the existing Chapter 1 owner
  `GeneralIterativeScheme.IsAnalyticalComplexity`

Primary domain:
* analytical complexity of information-set-based black-box iterative schemes

Relevant owner-style declarations sampled before refining:
* `IsLeast` in mathlib, the core/canonical least-natural-number owner underlying this notion;
* `GeneralIterativeScheme.HaltsAt` in `Algorithm_1_2_10.lean`, the chapter halting predicate;
* `GeneralIterativeScheme.IsAnalyticalComplexity` in `Chap01/Definition_1_2_11.lean`, the
  existing chapter owner of the source-facing notion;
* `GeneralIterativeScheme.isAnalyticalComplexity_iff` in `Chap01/Definition_1_2_11.lean`, the
  chapter bridge to the textbook “halts at `N` and not earlier” phrasing.

Source/core/bridge triage:
* source-facing: `scheme.IsAnalyticalComplexity N`;
* core/canonical: `IsLeast {k : ℕ | scheme.HaltsAt k} N`;
* bridge/view: `scheme.isAnalyticalComplexity_iff`.

Owner abstraction:
* `GeneralIterativeScheme.IsAnalyticalComplexity`

Primitive data:
* the iterative scheme `scheme`
* its derived halting predicate `scheme.HaltsAt`

Derived API:
* the least-halting-index formulation via `IsLeast`
* the textbook bridge theorem `scheme.isAnalyticalComplexity_iff`

This item intentionally introduces no parallel public predicate on an arbitrary
`haltsAt : ℕ → Prop`; the canonical chapter owner is already the analytical-complexity
predicate attached to a `GeneralIterativeScheme`. -/

namespace GeneralIterativeScheme

/- Definition 1.2.11: the analytical complexity predicate is the chapter owner
`scheme.IsAnalyticalComplexity N`. -/
recall GeneralIterativeScheme.IsAnalyticalComplexity
    (scheme : GeneralIterativeScheme Query Answer) (N : ℕ) : Prop

/- Unfolding analytical complexity gives the textbook criterion that the scheme halts at `N` and
does not halt earlier. -/
recall GeneralIterativeScheme.isAnalyticalComplexity_iff
    {N : ℕ} (scheme : GeneralIterativeScheme Query Answer) :
    scheme.IsAnalyticalComplexity N ↔
      scheme.HaltsAt N ∧ ∀ m < N, ¬ scheme.HaltsAt m

end GeneralIterativeScheme
