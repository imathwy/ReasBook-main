import Mathlib.Tactic.Recall
import Nesterov.Chap01.Definition_1_2_12

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {Query : Type u} {Answer : Type v}

/- Definition 1.2.12 is a source-facing recall item in the Chapter 1 arithmetic-complexity
domain.

Layer targeted by this refinement:
* source-facing recall of the existing Chapter 1 arithmetic-work owner API on
  `GeneralIterativeScheme`

Primary domain:
* arithmetic complexity of information-set-based black-box iterative schemes

Relevant owner-style declarations sampled before refining:
* `GeneralIterativeScheme.IsAnalyticalComplexity` in `Definition_1_2_11.lean`, the least-halting
  owner used by the arithmetic-complexity definition;
* `GeneralIterativeScheme.iterationArithmeticWork` in `Chap01/Definition_1_2_12.lean`, the
  chapter owner for one-step arithmetic work;
* `GeneralIterativeScheme.totalArithmeticWork` in `Chap01/Definition_1_2_12.lean`, the canonical
  accumulated-work owner built from `Finset.sum`;
* `GeneralIterativeScheme.IsArithmeticalComplexity` in `Chap01/Definition_1_2_12.lean`, the
  source-facing arithmetic-complexity predicate already attached to the iterative-scheme owner.

Source/core/bridge triage:
* source-facing: `scheme.IsArithmeticalComplexity oracleWork methodWork M`;
* core/canonical: the chapter owner arithmetic-work API on `GeneralIterativeScheme`;
* bridge/view: `scheme.isArithmeticalComplexity_iff` and
  `scheme.isArithmeticalComplexity_iff_haltsAt`.

Owner abstraction:
* `GeneralIterativeScheme` together with its chapter-owned arithmetic-work API

Primitive data:
* the iterative scheme `scheme`
* the oracle-work profile `oracleWork : Query → Answer → ℕ`
* the method-work profile `methodWork : Set (Query × Answer) → ℕ`

Derived API:
* `scheme.iterationArithmeticWork oracleWork methodWork`
* `scheme.totalArithmeticWork oracleWork methodWork`
* `scheme.IsArithmeticalComplexity oracleWork methodWork`
* the owner-side bridge theorems unpacking the analytical-complexity and least-halting
  formulations

This item therefore reuses the chapter owner directly instead of keeping parallel local
definitions. -/

namespace GeneralIterativeScheme

/- The arithmetic work of iteration `k` is the chapter owner
`scheme.iterationArithmeticWork oracleWork methodWork k`. -/
recall GeneralIterativeScheme.iterationArithmeticWork
    (scheme : GeneralIterativeScheme Query Answer)
    (oracleWork : Query → Answer → ℕ)
    (methodWork : Set (Query × Answer) → ℕ)
    (k : ℕ) : ℕ

/- The total arithmetic work up to iteration `N` is the chapter owner
`scheme.totalArithmeticWork oracleWork methodWork N`. -/
recall GeneralIterativeScheme.totalArithmeticWork
    (scheme : GeneralIterativeScheme Query Answer)
    (oracleWork : Query → Answer → ℕ)
    (methodWork : Set (Query × Answer) → ℕ)
    (N : ℕ) : ℕ

/- Definition 1.2.12: the arithmetic-complexity predicate is the chapter owner
`scheme.IsArithmeticalComplexity oracleWork methodWork M`. -/
recall GeneralIterativeScheme.IsArithmeticalComplexity
    (scheme : GeneralIterativeScheme Query Answer)
    (oracleWork : Query → Answer → ℕ)
    (methodWork : Set (Query × Answer) → ℕ)
    (M : ℕ) : Prop

/- Unfolding arithmetic complexity through the analytical-complexity owner gives the chapter
bridge `scheme.isArithmeticalComplexity_iff`. -/
recall GeneralIterativeScheme.isArithmeticalComplexity_iff
    (scheme : GeneralIterativeScheme Query Answer)
    {oracleWork : Query → Answer → ℕ}
    {methodWork : Set (Query × Answer) → ℕ}
    {M : ℕ} :
    scheme.IsArithmeticalComplexity oracleWork methodWork M ↔
      ∃ N : ℕ,
        scheme.IsAnalyticalComplexity N ∧
          M = scheme.totalArithmeticWork oracleWork methodWork N

/- Unfolding further to the least halting iteration gives the textbook bridge
`scheme.isArithmeticalComplexity_iff_haltsAt`. -/
recall GeneralIterativeScheme.isArithmeticalComplexity_iff_haltsAt
    (scheme : GeneralIterativeScheme Query Answer)
    {oracleWork : Query → Answer → ℕ}
    {methodWork : Set (Query × Answer) → ℕ}
    {M : ℕ} :
    scheme.IsArithmeticalComplexity oracleWork methodWork M ↔
      ∃ N : ℕ,
        scheme.HaltsAt N ∧
          (∀ m < N, ¬ scheme.HaltsAt m) ∧
          M = scheme.totalArithmeticWork oracleWork methodWork N

end GeneralIterativeScheme
