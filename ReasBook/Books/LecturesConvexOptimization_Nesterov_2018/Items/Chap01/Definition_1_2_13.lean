import Mathlib.Tactic.Recall
import LecturesConvexOptimization_Nesterov_2018.Chap01.Definition_1_2_13

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

variable {Problem : Type u} {Query : Type v} {Answer : Type w}

/- Definition 1.2.13 lies in the black-box optimization / local-oracle domain.

Layer targeted by this refinement:
* source-facing split recall of the two assumptions in the local black box concept

Primary domain:
* information available to black-box methods and locality of optimization oracles

Relevant owner-style declarations sampled before drafting:
* `Set (Query × Answer)`, the canonical owner for the accumulated oracle-sample information
  available to a method;
* `OptimizationOracle.IsLocal` from `Definition_1_2_13.lean`, the canonical locality predicate for
  class-level oracles `Problem → Query → Answer`;
* `GeneralIterativeScheme.query`, `GeneralIterativeScheme.shouldStop`, and
  `GeneralIterativeScheme.output` in `Algorithm_1_2_10.lean`, which consume only the
  informational state built from oracle samples.

Source/core/bridge triage:
* source-facing: the local black box concept as two assumptions, one about accessible
  information and one about locality of the oracle;
* core/canonical: the informational state `Set (Query × Answer)` and the predicate
  `OptimizationOracle.IsLocal oracle sameDataNear`;
* bridge/view: algorithmic uses of the informational state in later iterative-method files.

This item is therefore formalized as two atomic recall-style clauses rather than as a new wrapper
structure. -/

/- Definition 1.2.13 (1): under the local black box concept, the method has access only to the
oracle information contained in the observed query-answer pairs, whose canonical owner is the
informational state `Set (Query × Answer)`. -/
#check (Set (Query × Answer))

/- Definition 1.2.13 (2): the oracle is local if changing the problem data sufficiently far from
the query point does not change the oracle answer there, provided the modified problem remains in
the same class; this is exactly `OptimizationOracle.IsLocal oracle sameDataNear`. -/
recall OptimizationOracle.IsLocal
    (oracle : Problem → Query → Answer)
    (sameDataNear : Problem → Problem → Query → Prop) : Prop
