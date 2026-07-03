import LecturesConvexOptimization_Nesterov_2018.Chap01.Definition_1_2_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

variable {Problem : Type u} {Query : Type v} {Answer : Type w}

/- Definition 1.2.8 is a source-facing recall item in the Chapter 1 black-box optimization-oracle
domain.

Domain-style sampling:
* `#check (Query → Answer)` in `Definition_1_2_2.lean`, the fixed-problem oracle owner;
* `BlackBoxOptimizationProblemClass.oracle` in `Definition_1_2_4.lean`, the chapter owner field
  using the class-level oracle shape;
* `OptimizationOracle.IsLocal` in `Definition_1_2_13.lean`, the downstream locality predicate on
  class-level oracles.

Source/core/bridge triage:
* source-facing: the textbook class-level oracle notion;
* core/canonical: the chapter owner expression `Problem → Query → Answer`;
* bridge/view: fixed-problem evaluation `oracle problem : Query → Answer`.

Primitive data:
* `Problem`
* `Query`
* `Answer`

Derived API:
* fixed-problem evaluations `oracle problem : Query → Answer`
* downstream locality predicates such as `OptimizationOracle.IsLocal`

The canonical owner already lives upstream in `LecturesConvexOptimization_Nesterov_2018.Chap01.Definition_1_2_8`, so this item
keeps only the direct recall surface and does not restate a parallel local owner API. -/

/- Definition 1.2.8: an optimization oracle for problem instances in `Problem` and query points in
`Query` is just a curried answer rule `Problem → Query → Answer`. -/
#check (Problem → Query → Answer)
