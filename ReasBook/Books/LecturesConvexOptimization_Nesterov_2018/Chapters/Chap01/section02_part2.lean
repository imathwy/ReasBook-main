import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_1_2_12 (from Chap01) -/
universe u v

variable {Query : Type u} {Answer : Type v}

/- Primary domain: arithmetic complexity of information-set-based black-box iterative schemes.

Relevant owner-style declarations sampled before refining:
* `GeneralIterativeScheme` and `GeneralIterativeScheme.HaltsAt` in
  `Algorithm_1_2_10.lean`, which supply the source-facing informational-state dynamics and halting
  predicate;
* `GeneralIterativeScheme.IsAnalyticalComplexity` in `Definition_1_2_11.lean`, the source-facing
  analytical-complexity predicate;
* `GeneralIterativeScheme.isAnalyticalComplexity_iff` in `Definition_1_2_11.lean`, the chapter
  bridge to the textbook “halts first at `N`” phrasing;
* `IsLeast` in mathlib `Order.Bounds.Defs`, the canonical least-element predicate used internally
  by `IsAnalyticalComplexity`.

Owner abstraction:
the pair consisting of the informational-state owner object `GeneralIterativeScheme` and the
source-facing analytical-complexity witness `scheme.IsAnalyticalComplexity N`.

Primitive data:
the scheme together with the per-call oracle work `oracleWork` and informational-state update work
`methodWork`.

Derived API:
the per-iteration and cumulative arithmetic work, and the source-facing predicate saying that
`M` is the total arithmetic work at the least halting iteration. -/

namespace GeneralIterativeScheme

variable (scheme : GeneralIterativeScheme Query Answer)
variable (oracleWork : Query → Answer → ℕ)
variable (methodWork : Set (Query × Answer) → ℕ)

/-- The arithmetic work of iteration `k` is the sum of the oracle work performed at the current
query point and the method work needed to choose the next point from the updated informational
set. -/
def iterationArithmeticWork (k : ℕ) : ℕ :=
  oracleWork (scheme.currentPoint k) (scheme.currentAnswer k) + methodWork (scheme (k + 1))

/-- The total arithmetic work up to iteration `N` is the sum of the oracle and method work over
the first `N` iterations. -/
def totalArithmeticWork (N : ℕ) : ℕ :=
  (Finset.range N).sum (scheme.iterationArithmeticWork oracleWork methodWork)

/- Definition 1.2.12 is the derived complexity predicate on the owner object
`GeneralIterativeScheme`, built from the analytical-complexity witness
`scheme.IsAnalyticalComplexity N` and the accumulated arithmetic work up to that iteration. -/

/-- Definition 1.2.12: A natural number `M` is the arithmetical complexity of a method when `M`
is the total number of arithmetic operations, counting both oracle work and method work, required
to reach the analytical complexity threshold for the chosen stopping criterion. -/
def IsArithmeticalComplexity (M : ℕ) : Prop :=
  ∃ N : ℕ,
    scheme.IsAnalyticalComplexity N ∧
      M = scheme.totalArithmeticWork oracleWork methodWork N

variable {scheme} {oracleWork} {methodWork}

/-- Arithmetical complexity is exactly total arithmetic work evaluated at an analytical-complexity
index. -/
@[simp]
theorem isArithmeticalComplexity_iff {M : ℕ} :
    scheme.IsArithmeticalComplexity oracleWork methodWork M ↔
      ∃ N : ℕ,
        scheme.IsAnalyticalComplexity N ∧
          M = scheme.totalArithmeticWork oracleWork methodWork N :=
  Iff.rfl

/-- Arithmetical complexity is the total accumulated oracle and method work at the least halting
iteration. -/
theorem isArithmeticalComplexity_iff_haltsAt {M : ℕ} :
    scheme.IsArithmeticalComplexity oracleWork methodWork M ↔
      ∃ N : ℕ,
        scheme.HaltsAt N ∧
          (∀ m < N, ¬ scheme.HaltsAt m) ∧
          M = scheme.totalArithmeticWork oracleWork methodWork N := by
  rw [scheme.isArithmeticalComplexity_iff]
  constructor
  · rintro ⟨N, hN, hM⟩
    rw [scheme.isAnalyticalComplexity_iff] at hN
    exact ⟨N, hN.1, hN.2, hM⟩
  · rintro ⟨N, hN, hlt, hM⟩
    refine ⟨N, ?_, hM⟩
    rw [scheme.isAnalyticalComplexity_iff]
    exact ⟨hN, hlt⟩

end GeneralIterativeScheme

/-! ### Definition_1_2_12 (from Items/Chap01) -/
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

/-! ### Definition_1_2_13 (from Chap01) -/
universe u v w

variable {Problem : Type u} {Query : Type v} {Answer : Type w}

/- Definition 1.2.13 lies in the informational-state/locality domain of black-box optimization.

Layer targeted by this refinement:
* source-facing informational-state and locality declarations built from the core/canonical owner
  expressions already used in Chapter 1

Primary domain:
* information-set-based black-box methods and local optimization oracles

Relevant owner-style declarations sampled before refining:
* `#check (Problem → Query → Answer)` in `Definition_1_2_8.lean`, the class-level oracle owner;
* `GeneralIterativeScheme.query`, `GeneralIterativeScheme.shouldStop`, and
  `GeneralIterativeScheme.output` in `Algorithm_1_2_10.lean`, which use the informational state
  `Set (Query × Answer)`;
* `Set.insert` in mathlib, the canonical update operation for adjoining one new oracle sample to
  an informational set;
* `DeterministicValueOracleMethod.oracleTranscript` in `Theorem_1_3_9.lean`, a downstream ordered
  sample-history view kept separate from the owner informational set.

Owner abstractions:
* the informational state is the oracle-sample set `Set (Query × Answer)`;
* locality for a class of optimization problems is `OptimizationOracle.IsLocal oracle
  sameDataNear`.

Primitive data:
* query/answer pairs `(x, oracle x)` recorded as members of an accumulated informational set;
* an oracle `Problem → Query → Answer` together with the local-data relation `sameDataNear`.

Derived API:
* information-set-based query, stopping, and output rules in `Algorithm_1_2_10.lean`;
* direct use of the locality hypothesis by application, without an extra wrapper lemma.

This file therefore exposes the informational-state type expression directly and defines the owner
locality predicate where the chapter first uses that notion, instead of keeping a parallel public
wrapper for "informational state" or "local method". -/

#check (Set (Query × Answer))

namespace OptimizationOracle

/-- A local optimization oracle has the same answer at `x` for any two problem instances whose
data agree near `x`; the relation `sameDataNear` abstracts the condition that their difference is
supported sufficiently far from the query point. -/
def IsLocal
    (oracle : Problem → Query → Answer)
    (sameDataNear : Problem → Problem → Query → Prop) : Prop :=
  ∀ ⦃problem₁ problem₂ x⦄,
    sameDataNear problem₁ problem₂ x → oracle problem₁ x = oracle problem₂ x

end OptimizationOracle

/-! ### Definition_1_2_13 (from Items/Chap01) -/
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
