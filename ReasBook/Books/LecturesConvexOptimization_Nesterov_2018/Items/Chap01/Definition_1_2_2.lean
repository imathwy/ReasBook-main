import LecturesConvexOptimization_Nesterov_2018.Chap01.Definition_1_2_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {Query : Type u} {Answer : Type v}

/- Definition 1.2.2 is a source-facing recall item in the Chapter 1 black-box optimization
domain.

Domain-style sampling:
* `GeneralIterativeScheme.oracle` in `Algorithm_1_2_10.lean`, which stores a fixed-problem oracle
  directly as `Query → Answer`;
* `BlackBoxOptimizationProblemClass.oracle` in `Definition_1_2_4.lean`, which upgrades the same
  owner shape to `Problem → Query → Answer`;
* `OptimizationOracle.IsLocal` in `Definition_1_2_13.lean`, the locality predicate on that
  class-level oracle owner.

Owner abstraction:
* the function type `Query → Answer`

Primitive data:
* the query type `Query`
* the answer type `Answer`

Derived API:
* the class-level oracle shape `Problem → Query → Answer`
* locality predicates and transcript-driven algorithms built from oracle evaluation

The owner already lives in `LecturesConvexOptimization_Nesterov_2018.Chap01.Definition_1_2_2`, so this item stays a direct
recall-only use of that canonical expression and introduces no parallel wrapper. -/

/- Definition 1.2.2: an oracle for a fixed optimization problem is the answer rule sending each
query point `x` to the returned oracle value `𝒪(x)`, so the canonical Chapter 1 owner is the
function type `Query → Answer`. -/
#check (Query → Answer)
