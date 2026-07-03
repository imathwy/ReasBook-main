import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_1_2_1 (from Chap01) -/
universe u

/-
Definition 1.2.1 is a source-facing recall item in the Chapter 1 black-box optimization domain.

Sampled owner-style declarations:
- `Type u`, the core/canonical owner of the problem/query carrier itself
- `BlackBoxOptimizationProblemClass.model` in `Definition_1_2_4.lean`, which stores the model `Σ`
  directly as `Type u`
- `OptimizationOracle.IsLocal` in `Definition_1_2_13.lean`, whose problem parameter is again just a
  carrier type
- `GeneralIterativeScheme` in `Algorithm_1_2_10.lean`, which likewise uses the query space itself
  as a bare type parameter

Source/core/bridge triage:
- source-facing: the textbook model `Σ` of optimization problems
- core/canonical: the carrier type `Type u`
- bridge/view: downstream owner declarations such as oracle and stopping-rule maps built from this
  carrier

Owner abstraction:
- the visible problem or query space itself, namely a type `σ : Type u`

Primitive data:
- the carrier type `σ`

Derived API:
- oracle answer maps `σ → Answer` from Definition 1.2.2
- stopping predicates on an informational state from Definition 1.2.3
- transcript-based iterative schemes built from those owner objects in later files

There is no separate public wrapper such as `ProblemModel` or `ProblemState`. Later chapter files
use the carrier type directly, so the canonical main entry here is the type expression itself.
-/

/- Definition 1.2.1: for a problem `P`, its model `Σ` is the part of `P` known to a numerical
method; in this source-facing black-box optimization layer, that model is represented directly by
its carrier type. -/
#check (Type u)

/-! ### Definition_1_2_1 (from Items/Chap01) -/
universe u

/- Definition 1.2.1 is a source-facing recall item in the Chapter 1 black-box optimization
domain.

Layer targeted by this refinement:
* source-facing recall of the core/canonical owner expression already used elsewhere in Chapter 1

Primary domain:
* models of optimization problems in the black-box setting

Relevant owner-style declarations sampled before refining:
* `Type u`, the core/canonical owner of a visible carrier;
* `BlackBoxOptimizationProblemClass.model` in `Definition_1_2_4.lean`, which stores the model `Σ`
  directly as `Type u`;
* `OptimizationOracle.IsLocal` in `Definition_1_2_13.lean`, whose problem parameter is again just
  a carrier type;
* `GeneralIterativeScheme` in `Algorithm_1_2_10.lean`, which likewise uses its query space as a
  bare type parameter rather than a wrapper.

Source/core/bridge triage:
* source-facing: the textbook model `Σ` of optimization problems;
* core/canonical: the carrier type `Type u`;
* bridge/view: downstream owner declarations such as oracle maps `Σ → Answer` and stopping rules
  on informational states.

Owner abstraction:
* the visible problem or query space itself, namely a type `σ : Type u`

Primitive data:
* the carrier type `σ`

Derived API:
* oracle answer maps `σ → Answer` from Definition 1.2.2;
* stopping predicates on informational states from Definition 1.2.3;
* transcript-based iterative schemes built from those owner objects in later files.

This recall file intentionally introduces no separate public wrapper such as `ProblemModel` or
`ProblemState`. The canonical main entry is the type expression itself. -/

/- Definition 1.2.1: for a problem `P`, its model `Σ` is the part of `P` known to a numerical
method; in this source-facing black-box optimization layer, that model is represented directly by
its carrier type. -/
#check Type u

/-! ### Definition_1_2_2 (from Chap01) -/
universe u v

variable {Query : Type u} {Answer : Type v}

/- Definition 1.2.2 is a source-facing recall item in the Chapter 1 black-box optimization
domain.

Layer targeted by this refinement:
* source-facing recall of the core/canonical owner object already used elsewhere in the chapter

Primary domain:
* black-box optimization oracles as answer maps on a query space

Relevant owner-style declarations sampled before refining:
* `GeneralIterativeScheme.oracle` in `Algorithm_1_2_10.lean`, which stores a single-problem
  oracle directly as `Query → Answer`;
* `OptimizationOracle.IsLocal` in `Definition_1_2_13.lean`, which treats class-level oracles as
  the curried answer rule `Problem → Query → Answer`;
* the direct zero-, first-, and second-order answer maps in `Definition_1_2_9.lean`, which use
  the same owner shape without introducing separate wrapper objects.

Owner abstraction:
* the function type `Query → Answer`

Primitive data:
* the query type `Query`
* the answer type `Answer`

Derived API:
* the class-of-problems generalization `Problem → Query → Answer` from Definition 1.2.8
* locality properties such as `OptimizationOracle.IsLocal` from Definition 1.2.13
* transcript-based algorithms that consume the oracle by evaluation

This recall file intentionally introduces no separate public wrapper such as `ProblemOracle`.
Downstream chapter files should use the function type `Query → Answer` directly. -/

#check (Query → Answer)

/-! ### Definition_1_2_2 (from Items/Chap01) -/
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

/-! ### Definition_1_2_3 (from Chap01) -/
universe u

variable {State : Type u}

/- Definition 1.2.3 is a source-facing recall in the black-box stopping-criterion domain.

Layer targeted by this refinement:
* source-facing recall of the core/canonical owner expression already used elsewhere in Chapter 1

Primary domain:
* stopping predicates on the informational state of a black-box method

Relevant owner-style declarations sampled before refining:
* `Set` in mathlib, the owner type of accepted-state predicates;
* `Set.mem_setOf` in mathlib, the canonical bridge between the set and predicate views;
* `GeneralIterativeScheme.shouldStop` in `Algorithm_1_2_10.lean`, which stores the stopping rule
  directly as `Set (Set (Query × Answer))`;
* `GeneralIterativeScheme.HaltsAt` in `Algorithm_1_2_10.lean`, which derives halting from
  membership in that accepted-state set.

Source/core/bridge triage:
* source-facing: the `ε`-stopping rule itself;
* core/canonical: the accepted-state set `Set State`;
* bridge/view: `Set.mem_setOf`, which converts between set-builder and predicate syntax.

Owner abstraction:
* the accepted-state predicate/set `Set State`

Primitive data:
* the informational-state type `State`
* the accepted-state set itself

Derived API:
* set-builder membership via `Set.mem_setOf`
* downstream consumers such as `GeneralIterativeScheme.shouldStop`
* halting predicates such as `GeneralIterativeScheme.HaltsAt`

This recall file intentionally introduces no separate public wrapper such as `StoppingCriterion`.
The positivity witness `0 < ε` belongs to the ambient method/problem data that owns the stopping
rule, not to the stopping rule itself. -/

#check (Set State)

recall Set.mem_setOf
    {x : State} {p : State → Prop} :
    x ∈ {y | p y} ↔ p x

/-! ### Definition_1_2_3 (from Items/Chap01) -/
universe u

variable {State : Type u}

/- Definition 1.2.3 is a source-facing recall in the black-box stopping-criterion domain.

Layer targeted by this refinement:
* source-facing recall of the core/canonical owner expression already used elsewhere in Chapter 1

Primary domain:
* stopping predicates on the informational state of a black-box method

Relevant owner-style declarations sampled before refining:
* `Set` in mathlib, the owner type of accepted-state predicates;
* `Set.mem_setOf` in mathlib, the canonical bridge between the set and predicate views;
* `GeneralIterativeScheme.shouldStop` in `Algorithm_1_2_10.lean`, which stores the stopping rule
  directly as `Set (Set (Query × Answer))`;
* `GeneralIterativeScheme.HaltsAt` in `Algorithm_1_2_10.lean`, which derives halting from
  membership in that accepted-state set.

Source/core/bridge triage:
* source-facing: the `ε`-stopping rule itself;
* core/canonical: the accepted-state set `Set State`;
* bridge/view: `Set.mem_setOf`, which converts between set-builder and predicate syntax.

Owner abstraction:
* the accepted-state predicate/set `Set State`

Primitive data:
* the informational-state type `State`
* the accepted-state set itself

Derived API:
* set-builder membership via `Set.mem_setOf`
* downstream consumers such as `GeneralIterativeScheme.shouldStop`
* halting predicates such as `GeneralIterativeScheme.HaltsAt`

This recall file intentionally introduces no separate public wrapper such as `StoppingCriterion`.
The positivity witness `0 < ε` belongs to the ambient method/problem data that owns the stopping
rule, not to the stopping rule itself. -/

#check (Set State)

recall Set.mem_setOf
    {x : State} {p : State → Prop} :
    x ∈ {y | p y} ↔ p x

/-! ### Definition_1_2_4 (from Chap01) -/
universe u v w x

/- Definition 1.2.4 lies in the Chapter 1 black-box optimization problem-class domain.

Sampled owner declarations:
* `#check (Type u)` in `Definition_1_2_1.lean` for the model `Σ`;
* `#check (Query → Answer)` in `Definition_1_2_2.lean` for each fixed-problem oracle;
* `#check (Set State)` in `Definition_1_2_3.lean` for the stopping criterion `𝒯_ε`;
* `GeneralIterativeScheme.shouldStop` in `Algorithm_1_2_10.lean` for a downstream consumer of the
  same stopping-criterion owner.

Source/core/bridge triage:
* source-facing: the textbook triple `𝒫 ≡ (Σ, 𝒪, 𝒯_ε)`;
* core/canonical: the owner expressions `Type`, `Query → Answer`, and `Set State`;
* bridge/view: for fixed `σ : 𝒫.model`, the evaluation `𝒫.oracle σ : Query → Answer`.

The owner abstraction stays source-facing: the primitive data are exactly the model, class oracle,
and stopping criterion, each stored in its canonical owner type. -/

/-- Definition 1.2.4: a black-box optimization problem class is the triple
`𝒫 ≡ (Σ, 𝒪, 𝒯_ε)`, where `Σ` is a model of problems, `𝒪` is the class oracle, and `𝒯_ε` is the
chosen stopping criterion. The accuracy threshold is already part of the source-facing stopping
criterion `𝒯_ε`, so it is not stored as separate primitive data in the owner. -/
structure BlackBoxOptimizationProblemClass
    (Query : Type v) (Answer : Type w) (State : Type x) where
  /-- The model `Σ` of optimization problems. -/
  model : Type u
  /-- The class oracle `𝒪`, as a model-indexed family of fixed-problem oracles. -/
  oracle : model → Query → Answer
  /-- The fixed `ε`-stopping criterion `𝒯_ε`, in the canonical owner form `Set State`. -/
  stoppingCriterion : Set State

/-! ### Definition_1_2_4 (from Items/Chap01) -/
universe u v w x

/- Definition 1.2.4 lies in the Chapter 1 black-box optimization problem-class domain.

Relevant owner-style declarations sampled before refining:
* `#check (Type u)` in `Definition_1_2_1.lean`, the canonical owner of the model `Σ`;
* `#check (Query → Answer)` in `Definition_1_2_2.lean`, the canonical owner of a fixed-problem
  oracle;
* `#check (Set State)` in `Definition_1_2_3.lean`, the canonical owner of the stopping criterion
  `𝒯_ε`;
* `BlackBoxOptimizationProblemClass` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_2_4.lean`, which already
  packages exactly the source-facing triple from those primitive owners.

Best owner abstraction:
* `BlackBoxOptimizationProblemClass Query Answer State`

Primitive data:
* `model`
* `oracle`
* `stoppingCriterion`

Derived API:
* fixed-problem oracle evaluation `problemClass.oracle σ : Query → Answer`
* no separate function-view wrapper: downstream usage stays on the owner field `problemClass.oracle`

Source/core/bridge triage:
* source-facing: the textbook triple `𝒫 ≡ (Σ, 𝒪, 𝒯_ε)`;
* core/canonical: the chapter owner `BlackBoxOptimizationProblemClass Query Answer State`;
* bridge/view: the primitive projections `model`, `oracle`, and `stoppingCriterion`.

The exact source-facing owner already exists in the chapter file, so this item is refined to a
recall-only surface instead of reintroducing a parallel local structure and duplicate coercion
API. -/

/- Definition 1.2.4: a black-box optimization problem class is the chapter owner
`BlackBoxOptimizationProblemClass Query Answer State`. -/
recall BlackBoxOptimizationProblemClass
    (Query : Type v) (Answer : Type w) (State : Type x) :
    Type (max (max (max (u + 1) v) w) x)

section

variable {Query : Type v} {Answer : Type w} {State : Type x}

/- The problem model `Σ` is the owner field `problemClass.model`. -/
recall BlackBoxOptimizationProblemClass.model
    (problemClass : BlackBoxOptimizationProblemClass Query Answer State) : Type u

/- The class oracle `𝒪` is the owner field `problemClass.oracle`. -/
recall BlackBoxOptimizationProblemClass.oracle
    (problemClass : BlackBoxOptimizationProblemClass Query Answer State) :
    problemClass.model → Query → Answer

/- The stopping criterion `𝒯_ε` is the owner field `problemClass.stoppingCriterion`. -/
recall BlackBoxOptimizationProblemClass.stoppingCriterion
    (problemClass : BlackBoxOptimizationProblemClass Query Answer State) : Set State

end

/-! ### Definition_1_2_5 (from Chap01) -/
variable {r : ℕ → ℝ}

/- Primary domain: scalar convergence rates.

Source/core/bridge triage for Definition 1.2.5:
* source-facing: the power-law sublinear statement
  `∃ c > 0, ∃ p > 0, ∀ ⦃k : ℕ⦄, 0 < k → r k ≤ c / Real.rpow (k : ℝ) p`
* core/canonical: under optimization-error-sequence hypotheses, the later eventual-bound owner
  `HasConvergenceRateOfOrder`
* bridge/view: the concrete square-root estimate `r k ≤ c / Real.sqrt (k : ℝ)` and the resulting
  specialization `HasConvergenceRateOfOrder r (fun N ↦ 1 / Real.sqrt (N : ℝ))`

Relevant declarations sampled before refining:
* `HasGeometricRateOfConvergence` in `Definition_1_2_6.lean`, the neighboring source-facing
  rate predicate in the same chapter
* `HasConvergenceRateOfOrder` in `Definition_1_6_9.lean`, the later source-facing eventual-bound
  owner organized around `IsOptimizationErrorSequence`
* the direct square-root specialization
  `HasConvergenceRateOfOrder r (fun N ↦ 1 / Real.sqrt (N : ℝ))` in
  `Definition_1_6_9.lean`

Primitive data:
* the sequence `r`
* witnesses `c > 0` and `p > 0`
* the positive-index estimate `r k ≤ c / Real.rpow (k : ℝ) p`

Derived API:
* the source-facing recalled statement itself
* the square-root special case
* the bridge from a square-root bound plus `IsOptimizationErrorSequence` to the eventual-bound
  owner `HasConvergenceRateOfOrder r (fun N ↦ 1 / Real.sqrt (N : ℝ))`
* the explicit `(c / ε)^2` complexity threshold for the square-root example -/

/- Definition 1.2.5 is the source-facing existential statement

`∃ c > 0, ∃ p > 0, ∀ ⦃k : ℕ⦄, 0 < k → r k ≤ c / Real.rpow (k : ℝ) p`.

Unlike Definitions 1.2.6 and 1.2.7, this file has no reused fixed-parameter owner elsewhere in
the chapter. The previous alias `HasSublinearRateOfConvergence` therefore added no owner-level
mathematics and only duplicated the source statement. The numbered item is now recalled directly,
while the square-root specialization and later-rate bridge remain as the actual reusable API. -/
#check (∃ c > 0, ∃ p > 0, ∀ ⦃k : ℕ⦄, 0 < k → r k ≤ c / Real.rpow (k : ℝ) p)

private theorem div_sqrt_le_max_div_sqrt (c : ℝ) (k : ℕ) :
    c / Real.sqrt (k : ℝ) ≤ max c 1 / Real.sqrt (k : ℝ) :=
  div_le_div_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)

/-- A square-root decay bound yields the source-facing power-law estimate from Definition 1.2.5. -/
theorem exists_power_law_bound_of_sqrt_bound
    {c : ℝ}
    (h : ∀ ⦃k : ℕ⦄, 0 < k → r k ≤ c / Real.sqrt (k : ℝ)) :
    ∃ C > 0, ∃ p > 0, ∀ ⦃k : ℕ⦄, 0 < k → r k ≤ C / Real.rpow (k : ℝ) p := by
  refine ⟨max c 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), (1 / 2 : ℝ), by positivity, ?_⟩
  intro k hk
  refine (h hk).trans ?_
  simpa [Real.sqrt_eq_rpow] using div_sqrt_le_max_div_sqrt c k

namespace IsOptimizationErrorSequence

variable {r : ℕ → ℝ} {c : ℝ}

/-- Under the optimization-error-sequence hypotheses from Definition 1.6.9, a pointwise
`1 / sqrt N` estimate yields the later source-facing eventual-bound owner
`HasConvergenceRateOfOrder r (fun N ↦ 1 / Real.sqrt (N : ℝ))`. -/
theorem hasConvergenceRateOfOrder_of_sqrt_bound
    (hr : IsOptimizationErrorSequence r)
    (h : ∀ ⦃N : ℕ⦄, 0 < N → r N ≤ c / Real.sqrt (N : ℝ)) :
    HasConvergenceRateOfOrder r (fun N : ℕ ↦ 1 / Real.sqrt (N : ℝ)) := by
  refine ⟨hr, max c 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  refine Filter.eventually_atTop.2 ⟨1, fun N hN ↦ ?_⟩
  have hN_pos : 0 < N := Nat.succ_le_iff.mp hN
  refine (h hN_pos).trans ?_
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    div_sqrt_le_max_div_sqrt c N

end IsOptimizationErrorSequence

/-- A `1 / sqrt k` convergence estimate yields the complexity threshold `(c / ε)^2`. -/
theorem sqrt_rate_complexity_bound
    {r : ℕ → ℝ} {c ε : ℝ}
    (h : ∀ ⦃k : ℕ⦄, 0 < k → r k ≤ c / Real.sqrt (k : ℝ))
    (hε : 0 < ε)
    {k : ℕ} (hk : 0 < k)
    (hkComplexity : (c / ε) ^ (2 : ℕ) ≤ (k : ℝ)) :
    r k ≤ ε := by
  have hk_real : 0 < (k : ℝ) := by
    exact_mod_cast hk
  have hsqrt_pos : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hk_real
  refine (h hk).trans ?_
  by_cases hc : c ≤ 0
  · have hnonpos : c / Real.sqrt (k : ℝ) ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg hc (Real.sqrt_nonneg _)
    exact hnonpos.trans hε.le
  · have hle_sqrt : c / ε ≤ Real.sqrt (k : ℝ) := by
      have hc_pos : 0 < c := lt_of_not_ge hc
      have hdiv_nonneg : 0 ≤ c / ε := by
        positivity
      have hsq : (c / ε) ^ (2 : ℕ) ≤ (Real.sqrt (k : ℝ)) ^ (2 : ℕ) := by
        simpa [Real.sq_sqrt hk_real.le] using hkComplexity
      exact
        (sq_le_sq₀ hdiv_nonneg (by positivity : 0 ≤ Real.sqrt (k : ℝ))).1 hsq
    exact (div_le_iff₀ hsqrt_pos).2 <| by
      simpa [mul_comm] using (div_le_iff₀ hε).1 hle_sqrt

/-! ### Definition_1_2_5 (from Items/Chap01) -/
variable {r : ℕ → ℝ}

/- Definition 1.2.5 lies in the chapter's scalar convergence-rate domain.

Layer targeted by this refinement:
* source-facing recall of the Chapter 1 owner file, plus direct recall of its canonical bridge
  theorems

Primary domain:
* power-law and square-root decay bounds for real-valued error sequences

Relevant owner-style declarations sampled before refining:
* `exists_power_law_bound_of_sqrt_bound` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_2_5.lean`, the
  chapter theorem realizing the `1 / sqrt k` specialization of the textbook power-law bound;
* `IsOptimizationErrorSequence.hasConvergenceRateOfOrder_of_sqrt_bound` in the same file, the
  canonical bridge from the source-facing square-root estimate to the later owner
  `HasConvergenceRateOfOrder`;
* `HasConvergenceRateOfOrder` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_6_9.lean`, the later Chapter 1
  owner abstraction for eventual comparison rates of optimization-error sequences;
* `sqrt_rate_complexity_bound` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_2_5.lean`, the explicit
  complexity-threshold consequence used later in the chapter.

Source/core/bridge triage:
* source-facing: the existential power-law statement
  `∃ c > 0, ∃ p > 0, ∀ ⦃k : ℕ⦄, 0 < k → r k ≤ c / Real.rpow (k : ℝ) p`;
* core/canonical: the chapter owner file `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_2_5.lean`;
* bridge/view: the square-root specialization and the later
  `IsOptimizationErrorSequence.hasConvergenceRateOfOrder_of_sqrt_bound`.

Primitive data:
* the sequence `r`
* witnesses `c > 0` and `p > 0`
* the positive-index estimate `r k ≤ c / Real.rpow (k : ℝ) p`

Derived API:
* the square-root specialization of the source-facing statement;
* the bridge to `HasConvergenceRateOfOrder`;
* the explicit `(c / ε)^2` complexity threshold.

This item file intentionally introduces no parallel owner such as
`HasSublinearRateOfConvergence`. The numbered definition is recalled directly, and all reusable
companion API is taken from the Chapter 1 owner file instead of being restated locally. -/

/- Definition 1.2.5: a sublinear rate of convergence is the direct existential power-law bound. -/
#check (∃ c > 0, ∃ p > 0, ∀ ⦃k : ℕ⦄, 0 < k → r k ≤ c / Real.rpow (k : ℝ) p)

/- The square-root decay estimate is recalled from the chapter owner file as the canonical
specialization of Definition 1.2.5. -/
recall exists_power_law_bound_of_sqrt_bound
    {r : ℕ → ℝ} {c : ℝ}
    (h : ∀ ⦃k : ℕ⦄, 0 < k → r k ≤ c / Real.sqrt (k : ℝ)) :
    ∃ C > 0, ∃ p > 0, ∀ ⦃k : ℕ⦄, 0 < k → r k ≤ C / Real.rpow (k : ℝ) p

/- Under the later optimization-error-sequence hypotheses, the same square-root estimate recalls
the canonical bridge to `HasConvergenceRateOfOrder`. -/
recall IsOptimizationErrorSequence.hasConvergenceRateOfOrder_of_sqrt_bound
    {r : ℕ → ℝ} {c : ℝ}
    (hr : IsOptimizationErrorSequence r)
    (h : ∀ ⦃N : ℕ⦄, 0 < N → r N ≤ c / Real.sqrt (N : ℝ)) :
    HasConvergenceRateOfOrder r (fun N : ℕ ↦ 1 / Real.sqrt (N : ℝ))

/- The textbook `(c / ε)^2` complexity threshold is also recalled directly from the owner file. -/
recall sqrt_rate_complexity_bound
    {r : ℕ → ℝ} {c ε : ℝ}
    (h : ∀ ⦃k : ℕ⦄, 0 < k → r k ≤ c / Real.sqrt (k : ℝ))
    (hε : 0 < ε)
    {k : ℕ} (hk : 0 < k)
    (hkComplexity : (c / ε) ^ (2 : ℕ) ≤ (k : ℝ)) :
    r k ≤ ε

/-! ### Definition_1_2_6 (from Chap01) -/
open Asymptotics Filter

/-
Primary domain: scalar convergence rates for real sequences.

Source/core/bridge triage:
* source-facing condition
  `∃ c > 0, ∃ q : ℝ, 0 < q ∧ q ≤ 1 ∧ HasGeometricRateOfConvergence r q c`
* core owner for this scalar notion `HasGeometricRateOfConvergence`
* bridge/view: the canonical asymptotic estimate
  `HasGeometricRateOfConvergence.isBigO : r =O[atTop] (fun k ↦ (1 - q)^k)` under
  nonnegativity hypotheses, and then the later owner `HasConvergenceRateOfOrder` from
  `Definition_1_6_9.lean`, which additionally packages optimization-error-sequence data

Relevant declarations sampled before refining:
* `IsBigO.of_bound` in mathlib, the canonical asymptotic owner constructor for a pointwise norm
  bound
* `HasConvergenceRateOfOrder` in `Definition_1_6_9.lean`, the later project owner built from
  `IsOptimizationErrorSequence` and `=O[atTop]`
* `linear_iteration_contraction_estimate` in `Proposition_1_6_13.lean`
* `constrainedMinimizationInternalGap_hasGeometricRateOfConvergence` in
  `Chap02/Proposition_2_30.lean`
* `tendsto_pow_atTop_nhds_zero_of_lt_one` in mathlib for the geometric-to-zero consequence

Primitive data:
* the sequence `r`
* the constants `q` and `c`
* the global pointwise bound `r k ≤ c * (1 - q)^k`

Derived API:
* the source-facing linear-rate existence statement
* the asymptotic bridge to `=O[atTop]`
* the exponential bound, convergence-to-zero consequence, and complexity threshold
-/

/-- A rate of convergence controlled by a geometric factor in the iteration counter. -/
def HasGeometricRateOfConvergence (r : ℕ → ℝ) (q c : ℝ) : Prop :=
  ∀ k : ℕ, r k ≤ c * (1 - q) ^ k

variable {r : ℕ → ℝ}

/- Definition 1.2.6 is the source-facing existence statement

`∃ c > 0, ∃ q : ℝ, 0 < q ∧ q ≤ 1 ∧ HasGeometricRateOfConvergence r q c`.

The owner abstraction is `HasGeometricRateOfConvergence`; the numbered item only restricts the
admissible witnesses `c` and `q`. -/
#check (∃ c > 0, ∃ q : ℝ, 0 < q ∧ q ≤ 1 ∧ HasGeometricRateOfConvergence r q c)

namespace HasGeometricRateOfConvergence

variable {q c : ℝ}

/-- A one-step contraction estimate with factor `1 - q` and initial bound `c` yields the
corresponding geometric-rate owner statement. -/
theorem of_step_bound
    (hq₁ : q ≤ 1)
    (h0 : r 0 ≤ c)
    (hstep : ∀ k : ℕ, r (k + 1) ≤ (1 - q) * r k) :
    HasGeometricRateOfConvergence r q c := by
  intro k
  induction k with
  | zero =>
      simpa using h0
  | succ k ih =>
      calc
        r (k + 1) ≤ (1 - q) * r k := hstep k
        _ ≤ (1 - q) * (c * (1 - q) ^ k) := by
          gcongr
          exact sub_nonneg.mpr hq₁
        _ = c * (1 - q) ^ (k + 1) := by
          rw [pow_succ]
          ring

/-- A nonnegative geometric-rate bound gives the canonical asymptotic estimate
`r =O[atTop] (fun k ↦ (1 - q)^k)`. -/
theorem isBigO
    (h : HasGeometricRateOfConvergence r q c)
    (hr_nonneg : ∀ k : ℕ, 0 ≤ r k)
    (hc : 0 ≤ c) :
    r =O[atTop] (fun k : ℕ ↦ (1 - q) ^ k) := by
  refine IsBigO.of_bound c <| Filter.Eventually.of_forall fun k ↦ ?_
  calc
    ‖r k‖ = r k := by simp [Real.norm_eq_abs, abs_of_nonneg (hr_nonneg k)]
    _ ≤ c * (1 - q) ^ k := h k
    _ ≤ c * ‖(1 - q) ^ k‖ := by
      exact mul_le_mul_of_nonneg_left (le_abs_self ((1 - q) ^ k)) hc

/-- Helper for Definition 1.2.6: the geometric factor `(1 - q)^k` is dominated by the exponential
majorant `exp (-q k)` when `q ≤ 1`. -/
lemma geometric_factor_le_exp_neg_mul_nat
    (hq₁ : q ≤ 1) (k : ℕ) :
    (1 - q) ^ k ≤ Real.exp (-(q * (k : ℝ))) := by
  -- Reduce the comparison to the standard estimate `(1 - t / n)^n ≤ exp (-t)`.
  cases k with
  | zero =>
      simp
  | succ k =>
      have haux : q * ((k + 1 : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
        nlinarith
      have hbase :=
        Real.one_sub_div_pow_le_exp_neg (n := k + 1) (t := q * ((k + 1 : ℕ) : ℝ)) haux
      have hdiv : q * ((k + 1 : ℕ) : ℝ) / (((k + 1 : ℕ) : ℝ)) = q := by
        field_simp
      -- Rewrite the normalized factor back to the original contraction parameter `q`.
      calc
        (1 - q) ^ (k + 1) =
            (1 - q * ((k + 1 : ℕ) : ℝ) / (((k + 1 : ℕ) : ℝ))) ^ (k + 1) := by
          rw [hdiv]
        _ ≤ Real.exp (-(q * ((k + 1 : ℕ) : ℝ))) := hbase

/-- A geometric decay estimate with nonnegative constant `c` and `0 < q ≤ 1` is bounded above by
the corresponding exponential estimate `c * exp (-q k)`. -/
-- Proof sketch: combine the pointwise geometric bound with the standard inequality
-- `(1 - q)^k ≤ exp (-q k)` valid for `0 < q ≤ 1`, then multiply by the nonnegative constant `c`.
theorem exp_bound
    (h : HasGeometricRateOfConvergence r q c)
    (hc : 0 ≤ c)
    (hq₀ : 0 < q) (hq₁ : q ≤ 1)
    (k : ℕ) :
    r k ≤ c * Real.exp (-(q * (k : ℝ))) := by
  have hq_nonneg : 0 ≤ q := hq₀.le
  -- First use the geometric owner bound, then replace the geometric factor by the exponential one.
  calc
    r k ≤ c * (1 - q) ^ k := h k
    _ ≤ c * Real.exp (-(q * (k : ℝ))) := by
      gcongr
      exact geometric_factor_le_exp_neg_mul_nat hq₁ k

/-- A nonnegative sequence with a geometric rate and factor `0 < q < 1` converges to `0`. -/
-- Proof sketch: combine the geometric upper bound with the convergence
-- `(1 - q)^k → 0`, then squeeze `r k` between `0` and `c * (1 - q)^k`.
theorem tendsto_zero
    (h : HasGeometricRateOfConvergence r q c)
    (hr_nonneg : ∀ k : ℕ, 0 ≤ r k) (hc : 0 ≤ c)
    (hq₀ : 0 < q) (hq₁ : q < 1) :
    Tendsto r atTop (nhds 0) := by
  have hcontract_nonneg : 0 ≤ 1 - q := by
    linarith
  have hupper_nonneg : ∀ k : ℕ, 0 ≤ c * (1 - q) ^ k := by
    intro k
    exact mul_nonneg hc (pow_nonneg hcontract_nonneg k)
  have hpow : Tendsto (fun k : ℕ ↦ (1 - q) ^ k) atTop (nhds 0) := by
    -- The contraction factor lies in `[0, 1)`, so its powers tend to `0`.
    apply tendsto_pow_atTop_nhds_zero_of_lt_one
    · exact hcontract_nonneg
    · linarith
  have hmajorant : Tendsto (fun k : ℕ ↦ c * (1 - q) ^ k) atTop (nhds 0) := by
    -- Multiplying by the fixed constant `c` preserves convergence to `0`.
    simpa using tendsto_const_nhds.mul hpow
  -- Squeeze the sequence between `0` and the vanishing majorant.
  exact squeeze_zero hr_nonneg (fun k ↦ h k) hmajorant

/-- Helper for Definition 1.2.6: a logarithmic lower bound on the iteration counter forces the
exponential majorant `c * exp (-q k)` below the target level `ε`. -/
lemma exp_threshold_le_target
    {ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (hq₀ : 0 < q)
    {k : ℕ} (hk : Real.log (c / ε) / q ≤ (k : ℝ)) :
    c * Real.exp (-(q * (k : ℝ))) ≤ ε := by
  have hk' : Real.log (c / ε) ≤ q * (k : ℝ) := by
    -- Clear the positive denominator `q` to put the threshold in exponential form.
    have hk'' := (div_le_iff₀ hq₀).mp hk
    simpa [mul_comm] using hk''
  have hratio_pos : 0 < c / ε := by
    positivity
  have hratio : c / ε ≤ Real.exp (q * (k : ℝ)) := by
    -- Convert the logarithmic bound into a direct bound on `c / ε`.
    exact (Real.log_le_iff_le_exp hratio_pos).mp hk'
  have hce : c ≤ ε * Real.exp (q * (k : ℝ)) := by
    -- Restore the target scale by multiplying through by the positive tolerance `ε`.
    simpa [mul_comm] using (div_le_iff₀ hε).mp hratio
  have hexp_pos : 0 < Real.exp (q * (k : ℝ)) := Real.exp_pos _
  have hdiv : c / Real.exp (q * (k : ℝ)) ≤ ε := by
    -- Divide by the positive exponential term to recover the desired decay estimate.
    exact (div_le_iff₀ hexp_pos).2 hce
  simpa [Real.exp_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv

/-- The geometric estimate `r k ≤ c * (1 - q)^k` yields the logarithmic complexity threshold
`log (c / ε) / q`. -/
-- Proof sketch: first replace the geometric factor by the exponential bound
-- `c * exp (-q k)`, then solve `c * exp (-q k) ≤ ε` by taking logarithms and using
-- the lower bound on `k`.
theorem complexity_bound
    {ε : ℝ} (h : HasGeometricRateOfConvergence r q c)
    (hc : 0 < c) (hq₀ : 0 < q) (hq₁ : q ≤ 1) (hε : 0 < ε)
    {k : ℕ} (hkComplexity : Real.log (c / ε) / q ≤ (k : ℝ)) :
    r k ≤ ε := by
  -- Chain the exponential bridge with the logarithmic threshold estimate.
  calc
    r k ≤ c * Real.exp (-(q * (k : ℝ))) := exp_bound h hc.le hq₀ hq₁ k
    _ ≤ ε := exp_threshold_le_target hc hε hq₀ hkComplexity

/-- The exact logarithmic iteration threshold attached to the bound
`r k ≤ c * (1 - q)^k`, written with base `(1 - q)⁻¹`. -/
noncomputable abbrev iterationThreshold (q c ε : ℝ) : ℝ :=
  Real.logb ((1 - q)⁻¹) (c / ε)

/-- The exact geometric estimate `r k ≤ c * (1 - q)^k` yields the logarithmic threshold with base
`(1 - q)⁻¹`. -/
-- Proof sketch: rewrite the geometric factor as `((1 - q)⁻¹)⁻k`, then solve
-- `c * ((1 - q)⁻¹)⁻k ≤ ε` directly by taking logarithms in the base `(1 - q)⁻¹`.
theorem le_target_of_iterationThreshold_le
    {ε : ℝ} (h : HasGeometricRateOfConvergence r q c)
    (hq_contract : 1 < (1 - q)⁻¹) (hε : 0 < ε)
    {k : ℕ} (hk : iterationThreshold q c ε ≤ (k : ℝ)) :
    r k ≤ ε := by
  have hgeom : r k ≤ c * ((1 - q)⁻¹)⁻¹ ^ k := by
    simpa using h k
  have hbase_pos : 0 < (1 - q)⁻¹ := lt_trans zero_lt_one hq_contract
  have hterm : c * ((1 - q)⁻¹)⁻¹ ^ k ≤ ε := by
    by_cases hratio : 0 < c / ε
    · have hpow : c / ε ≤ ((1 - q)⁻¹) ^ (k : ℝ) := by
        exact (Real.logb_le_iff_le_rpow hq_contract hratio).1 <| by
          simpa [iterationThreshold] using hk
      have hmul : c ≤ ((1 - q)⁻¹) ^ (k : ℝ) * ε := (div_le_iff₀ hε).1 hpow
      have hpow_pos : 0 < ((1 - q)⁻¹) ^ (k : ℝ) := Real.rpow_pos_of_pos hbase_pos _
      have : c * (((1 - q)⁻¹) ^ (k : ℝ))⁻¹ ≤ ε := by
        rw [← div_eq_mul_inv, div_le_iff₀ hpow_pos]
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
      simpa [Real.rpow_natCast, inv_pow] using this
    · have hc_nonpos : c ≤ 0 := by
        by_contra hc_nonpos
        have hc_pos : 0 < c := lt_of_not_ge hc_nonpos
        have : 0 < c / ε := by positivity
        exact hratio this
      have hpow_nonneg : 0 ≤ ((1 - q)⁻¹)⁻¹ ^ k := by
        exact pow_nonneg (inv_nonneg.mpr hbase_pos.le) _
      exact (mul_nonpos_of_nonpos_of_nonneg hc_nonpos hpow_nonneg).trans hε.le
  exact hgeom.trans hterm

/-- The natural ceiling of the exact logarithmic iteration threshold gives a valid iterate index at
which the target error level is reached. -/
theorem le_target_at_natCeil_iterationThreshold
    {ε : ℝ} (h : HasGeometricRateOfConvergence r q c)
    (hq_contract : 1 < (1 - q)⁻¹) (hε : 0 < ε) :
    r ⌈iterationThreshold q c ε⌉₊ ≤ ε := by
  simpa using le_target_of_iterationThreshold_le h hq_contract hε (Nat.le_ceil _)

end HasGeometricRateOfConvergence

/-! ### Definition_1_2_6 (from Items/Chap01) -/
open Asymptotics Filter

variable {r : ℕ → ℝ}

/- Definition 1.2.6 lies in the chapter's scalar geometric-convergence domain.

Layer targeted by this refinement:
* source-facing recall of the Chapter 1 owner file, plus direct recall of its canonical
  constructor and companion bridge theorems

Primary domain:
* geometric decay bounds for real-valued error sequences

Relevant owner-style declarations sampled before refining:
* `HasGeometricRateOfConvergence` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_2_6.lean`, the chapter owner
  for the fixed-parameter geometric estimate `r k ≤ c * (1 - q)^k`;
* `HasGeometricRateOfConvergence.of_step_bound` in the same file, the canonical constructor from
  a one-step contraction estimate;
* `HasGeometricRateOfConvergence.isBigO`, the canonical asymptotic bridge to
  `r =O[atTop] (fun k ↦ (1 - q)^k)`;
* `HasGeometricRateOfConvergence.le_target_of_iterationThreshold_le`, the exact logarithmic
  threshold consequence attached to the owner estimate.

Source/core/bridge triage:
* source-facing: the existential textbook statement
  `∃ c > 0, ∃ q : ℝ, 0 < q ∧ q ≤ 1 ∧ HasGeometricRateOfConvergence r q c`;
* core/canonical: the chapter owner `HasGeometricRateOfConvergence`;
* bridge/view: the one-step constructor, the asymptotic `=O[atTop]` consequence, the convergence
  consequence, and the exact iteration-threshold consequence.

Primitive data:
* the sequence `r`;
* witnesses `q` and `c`;
* the owner bound `HasGeometricRateOfConvergence r q c`.

Derived API:
* the source-facing existential recall;
* the one-step contraction constructor;
* the asymptotic and convergence-to-zero bridges;
* the exact logarithmic iteration-threshold consequence.

This item file intentionally introduces no parallel local owner or alias. The numbered definition
is recalled directly, and the reusable API is taken from the chapter owner file. -/

/- Definition 1.2.6: a geometric rate of convergence is the direct existential textbook bound. -/
#check (∃ c > 0, ∃ q : ℝ, 0 < q ∧ q ≤ 1 ∧ HasGeometricRateOfConvergence r q c)

namespace HasGeometricRateOfConvergence

/- A one-step contraction estimate is recalled from the chapter owner file as the canonical
constructor for `HasGeometricRateOfConvergence`. -/
recall of_step_bound
    {r : ℕ → ℝ} {q c : ℝ}
    (hq₁ : q ≤ 1)
    (h0 : r 0 ≤ c)
    (hstep : ∀ k : ℕ, r (k + 1) ≤ (1 - q) * r k) :
    HasGeometricRateOfConvergence r q c

/- A nonnegative geometric-rate bound recalls the canonical asymptotic bridge to `=O[atTop]`. -/
recall isBigO
    {r : ℕ → ℝ} {q c : ℝ}
    (h : HasGeometricRateOfConvergence r q c)
    (hr_nonneg : ∀ k : ℕ, 0 ≤ r k)
    (hc : 0 ≤ c) :
    r =O[atTop] (fun k : ℕ ↦ (1 - q) ^ k)

/- Under the standard positivity range `0 < q < 1`, the owner estimate recalls the canonical
convergence-to-zero consequence. -/
recall tendsto_zero
    {r : ℕ → ℝ} {q c : ℝ}
    (h : HasGeometricRateOfConvergence r q c)
    (hr_nonneg : ∀ k : ℕ, 0 ≤ r k) (hc : 0 ≤ c)
    (hq₀ : 0 < q) (hq₁ : q < 1) :
    Tendsto r atTop (nhds 0)

/- The exact logarithmic stopping threshold is recalled directly from the chapter owner file. -/
recall le_target_of_iterationThreshold_le
    {r : ℕ → ℝ} {q c ε : ℝ}
    (h : HasGeometricRateOfConvergence r q c)
    (hq_contract : 1 < (1 - q)⁻¹) (hε : 0 < ε)
    {k : ℕ} (hk : iterationThreshold q c ε ≤ (k : ℝ)) :
    r k ≤ ε

end HasGeometricRateOfConvergence

/-! ### Definition_1_2_7 (from Chap01) -/
variable {r : ℕ → ℝ}

/-
Primary domain: scalar convergence rates for real error sequences.

Source/core/bridge triage for Definition 1.2.7:
* source-facing: the textbook quadratic-rate statement
  `∃ c > 0, ∀ k, r (k + 1) ≤ c * r k^2`;
* core/canonical: `HasEventuallySuperlinearErrorBound r 0 c 0`;
* bridge/view: the equivalence between that owner specialization and the explicit quadratic
  recurrence.

Relevant owner-style declarations sampled before refining:
* the scalar owner `HasEventuallySuperlinearErrorBound`, introduced below and reused by
  `HasSuperlinearRateOfConvergence` in `Definition_1_8_15.lean`;
* the owner `HasGeometricRateOfConvergence` and the source-facing linear-rate condition in
  `Definition_1_2_6.lean`;
* the direct square-root specialization
  `HasConvergenceRateOfOrder r (fun N ↦ 1 / Real.sqrt (N : ℝ))` in
  `Definition_1_6_9.lean`.

Owner abstraction:
* `HasEventuallySuperlinearErrorBound r 0 c 0`

Primitive data:
* the sequence `r`
* the constant `c`
* the owner recurrence witness `HasEventuallySuperlinearErrorBound r 0 c 0`

Derived API:
* the textbook quadratic recurrence `r (k + 1) ≤ c * r k^2`
* the source-facing existential statement from Definition 1.2.7
* the linear one-step estimate derived once `c * r k ≤ 1 / 2`
* the Proposition 1.7.6 tail estimate and logarithmic threshold consequence in the quadratic case

This file therefore recalls the owner specialization directly and removes the redundant alias
`HasQuadraticRateOfConvergence`. The numbered item is the canonical specialization
`∃ c > 0, HasEventuallySuperlinearErrorBound r 0 c 0`, while the explicit quadratic recurrence
remains available through the two atomic bridge lemmas below.
-/

/-- An error sequence has an eventual superlinear bound with lag `lag` from index `N` onward if
the textbook estimate
`r_{k+1} ≤ c * r_k * r_{k-lag}`
holds for every `k ≥ N`, with `N` chosen large enough that the lagged term is available. -/
def HasEventuallySuperlinearErrorBound
    (r : ℕ → ℝ) (lag : ℕ) (c : ℝ) (N : ℕ) : Prop :=
  lag ≤ N ∧ ∀ ⦃k : ℕ⦄, N ≤ k → r (k + 1) ≤ c * r k * r (k - lag)

/- Definition 1.2.7 is recalled by the canonical specialization
`∃ c > 0, HasEventuallySuperlinearErrorBound r 0 c 0`. -/
#check (∃ c > 0, HasEventuallySuperlinearErrorBound r 0 c 0)

namespace HasEventuallySuperlinearErrorBound

variable {c : ℝ}

/-- The starting index `N` is large enough that the lagged term `r (k - lag)` is available. -/
theorem lag_le
    {lag N : ℕ}
    (h : HasEventuallySuperlinearErrorBound r lag c N) :
    lag ≤ N :=
  h.1

/-- The textbook recurrence estimate holds at every index `k ≥ N`. -/
theorem bound
    {lag N : ℕ}
    (h : HasEventuallySuperlinearErrorBound r lag c N) :
    ∀ ⦃k : ℕ⦄, N ≤ k → r (k + 1) ≤ c * r k * r (k - lag) :=
  h.2

/-- A quadratic recurrence bound immediately gives the corresponding one-step estimate. -/
-- Proof sketch: specialize `HasEventuallySuperlinearErrorBound.bound` to `lag = 0` and `N = 0`,
-- then simplify `r (k - 0)` to `r k`.
theorem quadratic_bound
    (h : HasEventuallySuperlinearErrorBound r 0 c 0)
    (k : ℕ) :
    r (k + 1) ≤ c * (r k)^2 := by
  simpa [pow_two, Nat.sub_zero, mul_assoc] using h.bound (Nat.zero_le k)

/-- The textbook quadratic recurrence defines the owner specialization with `lag = 0` and
starting index `0`. -/
theorem of_quadratic_bound
    (h : ∀ k : ℕ, r (k + 1) ≤ c * (r k)^2) :
    HasEventuallySuperlinearErrorBound r 0 c 0 := by
  refine ⟨le_rfl, ?_⟩
  intro k hk
  simpa [pow_two, Nat.sub_zero, mul_assoc] using h k

/-- Once `c * r k ≤ 1 / 2`, a quadratic recurrence implies the linear estimate
`r (k + 1) ≤ (1 / 2) * r k` at the next iterate. -/
-- Proof sketch: combine `quadratic_bound` with `c * r k ≤ 1 / 2`, rewrite
-- `c * (r k)^2` as `(c * r k) * r k`, and use `0 ≤ r k` to preserve the inequality after
-- multiplying by `r k`.
theorem linear_bound_of_mul_le_half
    (h : HasEventuallySuperlinearErrorBound r 0 c 0)
    {k : ℕ}
    (hrk : 0 ≤ r k)
    (hthreshold : c * r k ≤ (1 / 2 : ℝ)) :
    r (k + 1) ≤ (1 / 2 : ℝ) * r k := by
  refine (quadratic_bound h k).trans ?_
  have hmul := mul_le_mul_of_nonneg_right hthreshold hrk
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hmul

/-- Helper for Definition 1.2.7: after scaling by `c`, the quadratic recurrence becomes the
repeated-squaring step `a_{k+1} ≤ a_k^2`. -/
-- Proof sketch: multiply `quadratic_bound` by the positive factor `c` and regroup the product
-- into the square of the scaled quantity.
lemma scaled_quadratic_step
    (h : HasEventuallySuperlinearErrorBound r 0 c 0)
    (hc : 0 < c)
    (k : ℕ) :
    c * r (k + 1) ≤ (c * r k)^2 := by
  have hmul :=
    mul_le_mul_of_nonneg_left (quadratic_bound h k) (le_of_lt hc)
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hmul

/-- Helper for Definition 1.2.7: the scaled quadratic recurrence yields a repeated-squaring tail
bound for every offset `j`. -/
-- Proof sketch: induct on the offset, apply `scaled_quadratic_step` at the current index, and
-- use monotonicity of squaring on nonnegative reals to square the induction hypothesis.
lemma scaled_tail_bound
    (h : HasEventuallySuperlinearErrorBound r 0 c 0)
    (hr_nonneg : ∀ k : ℕ, 0 ≤ r k) (hc : 0 < c)
    (k0 j : ℕ) :
    c * r (k0 + j) ≤ (c * r k0) ^ (2 ^ j : ℕ) := by
  induction j with
  | zero =>
      -- At offset `0`, the claimed bound is exactly the identity `a ≤ a`.
      simp
  | succ j ih =>
      -- The recurrence turns the next scaled iterate into a square, and the induction
      -- hypothesis bounds the previous scaled iterate by the previous repeated square.
      have hstep := scaled_quadratic_step h hc (k0 + j)
      have hscaled_nonneg : 0 ≤ c * r (k0 + j) := by
        exact mul_nonneg (le_of_lt hc) (hr_nonneg (k0 + j))
      have hpow_nonneg : 0 ≤ (c * r k0) ^ (2 ^ j : ℕ) := by
        exact pow_nonneg (mul_nonneg (le_of_lt hc) (hr_nonneg k0)) _
      have hsquare :
          (c * r (k0 + j)) ^ 2 ≤ ((c * r k0) ^ (2 ^ j : ℕ)) ^ 2 := by
        exact (sq_le_sq₀ hscaled_nonneg hpow_nonneg).2 ih
      calc
        c * r (k0 + j.succ) = c * r ((k0 + j) + 1) := by
          simp [Nat.add_assoc]
        _ ≤ (c * r (k0 + j)) ^ 2 := by
          simpa [Nat.add_assoc] using hstep
        _ ≤ ((c * r k0) ^ (2 ^ j : ℕ)) ^ 2 := hsquare
        _ = (c * r k0) ^ (2 ^ j.succ : ℕ) := by
          rw [show (2 ^ j.succ : ℕ) = (2 ^ j : ℕ) * 2 by rw [Nat.pow_succ], pow_mul]

/-- Helper for Definition 1.2.7: a base-two logarithmic lower bound implies that the repeated
square `(a ^ (2^j))` has already dropped below the target `b`. -/
-- Proof sketch: convert the `logb` inequality into a bound on the ratio of positive logarithms,
-- rewrite the resulting real power as the natural power `2 ^ j`, compare logarithms, and then
-- invert the positive quantities.
lemma scaled_pow_le_target_of_logb_bound
    {a b : ℝ} {j : ℕ}
    (ha0 : 0 < a) (ha1 : a < 1)
    (hb0 : 0 < b) (hb1 : b < 1)
    (hj : Real.logb 2 (Real.log (1 / b) / Real.log (1 / a)) ≤ (j : ℝ)) :
    a ^ (2 ^ j : ℕ) ≤ b := by
  have hlog_a_pos : 0 < Real.log (1 / a) := by
    -- Since `0 < a < 1`, its reciprocal is larger than `1`, so its logarithm is positive.
    have h_inv : 1 < 1 / a := by
      rw [one_div]
      exact (one_lt_inv₀ ha0).2 ha1
    exact Real.log_pos h_inv
  have hlog_b_pos : 0 < Real.log (1 / b) := by
    -- The same reciprocal-log positivity applies to the target scale `b`.
    have h_inv : 1 < 1 / b := by
      rw [one_div]
      exact (one_lt_inv₀ hb0).2 hb1
    exact Real.log_pos h_inv
  have hratio_pos : 0 < Real.log (1 / b) / Real.log (1 / a) := by
    exact div_pos hlog_b_pos hlog_a_pos
  have hpow_real : Real.log (1 / b) / Real.log (1 / a) ≤ (2 : ℝ) ^ (j : ℝ) := by
    exact (Real.logb_le_iff_le_rpow (by norm_num) hratio_pos).1 hj
  have hmul : Real.log (1 / b) ≤ ((2 : ℝ) ^ (j : ℝ)) * Real.log (1 / a) := by
    exact (div_le_iff₀ hlog_a_pos).1 hpow_real
  have hpow_cast : ((2 : ℝ) ^ (j : ℝ)) = (2 ^ j : ℕ) := by
    rw [Real.rpow_natCast]
    norm_num [Nat.cast_pow]
  have hmul_nat : Real.log (1 / b) ≤ (2 ^ j : ℕ) * Real.log (1 / a) := by
    simpa [hpow_cast] using hmul
  have hlog_le : Real.log (1 / b) ≤ Real.log ((1 / a) ^ (2 ^ j : ℕ)) := by
    -- This is the logarithmic form of the desired power comparison.
    rw [← Real.rpow_natCast, Real.log_rpow (by positivity), mul_comm]
    simpa [mul_comm] using hmul_nat
  have hle_inv : 1 / b ≤ (1 / a) ^ (2 ^ j : ℕ) := by
    -- Strict monotonicity of `log` on positive reals turns the logarithmic inequality back into
    -- an inequality of the positive arguments themselves.
    refine le_of_not_gt ?_
    intro hgt
    have hlt_log : Real.log ((1 / a) ^ (2 ^ j : ℕ)) < Real.log (1 / b) := by
      exact Real.strictMonoOn_log
        (by simpa using show 0 < (1 / a) ^ (2 ^ j : ℕ) by positivity)
        (by simpa using hb0)
        hgt
    linarith
  have ha_pow_pos : 0 < a ^ (2 ^ j : ℕ) := by
    exact pow_pos ha0 _
  have hle_inv' : b⁻¹ ≤ (a ^ (2 ^ j : ℕ))⁻¹ := by
    simpa [one_div, inv_pow] using hle_inv
  exact (inv_le_inv₀ hb0 ha_pow_pos).1 hle_inv'

/-- Proposition 1.7.6, owner form: under a quadratic recurrence, the tail is bounded by
repeated squaring of `c * r K`. -/
theorem quadratic_tail_bound
    (h : HasEventuallySuperlinearErrorBound r 0 c 0)
    (hr_nonneg : ∀ k : ℕ, 0 ≤ r k) (hc : 0 < c)
    (k0 j : ℕ) :
    r (k0 + j) ≤ (1 / c) * (c * r k0) ^ (2 ^ j : ℕ) := by
  -- We first bound the scaled tail `c * r (k0 + j)` by repeated squaring and then divide by the
  -- positive constant `c`.
  have hscaled := scaled_tail_bound h hr_nonneg hc k0 j
  simpa [one_div] using
    (le_inv_mul_iff₀ hc).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled)

/-- Proposition 1.7.6, owner form: a base-two logarithmic lower bound on `j` forces the tail
estimate `r (K + j) ≤ ε` under the quadratic recurrence assumptions. -/
theorem quadratic_tail_le_of_logb_bound
    (h : HasEventuallySuperlinearErrorBound r 0 c 0)
    (hr_nonneg : ∀ k : ℕ, 0 ≤ r k) (hc : 0 < c)
    (k0 j : ℕ) (ε : ℝ)
    (hK0 : 0 < c * r k0) (hK1 : c * r k0 < 1)
    (hε : ε ∈ Set.Ioo (0 : ℝ) (1 / c))
    (hj :
      Real.logb 2 (Real.log (1 / (c * ε)) / Real.log (1 / (c * r k0))) ≤ (j : ℝ)) :
    r (k0 + j) ≤ ε := by
  -- Route correction: keep the source-owner route. First use the repeated-squaring tail bound,
  -- then show that the logarithmic threshold forces the repeated square below `c * ε`.
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hε0 : 0 < ε := hε.1
  have hb0 : 0 < c * ε := by
    exact mul_pos hc hε0
  have hb1 : c * ε < 1 := by
    have hmul : c * ε < c * (1 / c) := by
      exact mul_lt_mul_of_pos_left hε.2 hc
    simpa [one_div, hc0, mul_assoc] using hmul
  have hpow_le :
      (c * r k0) ^ (2 ^ j : ℕ) ≤ c * ε := by
    exact scaled_pow_le_target_of_logb_bound hK0 hK1 hb0 hb1 hj
  have htail := quadratic_tail_bound h hr_nonneg hc k0 j
  have hfinal :
      (1 / c) * (c * r k0) ^ (2 ^ j : ℕ) ≤ ε := by
    -- Multiplying by `1 / c` preserves the inequality and collapses `((1 / c) * c)` to `1`.
    have hscaled :
        (1 / c) * (c * r k0) ^ (2 ^ j : ℕ) ≤ (1 / c) * (c * ε) := by
      exact mul_le_mul_of_nonneg_left hpow_le (by positivity)
    simpa [one_div, hc0, mul_assoc, mul_left_comm, mul_comm] using hscaled
  exact htail.trans hfinal

end HasEventuallySuperlinearErrorBound

/-! ### Definition_1_2_7 (from Items/Chap01) -/
variable {r : ℕ → ℝ} {c : ℝ}

/- Definition 1.2.7 lies in the chapter's scalar superlinear-convergence domain.

Layer targeted by this refinement:
* source-facing recall of the Chapter 1 owner file, plus direct recall of its canonical bridge
  theorems

Primary domain:
* quadratic recurrence bounds for real-valued error sequences

Relevant owner-style declarations sampled before refining:
* `HasEventuallySuperlinearErrorBound` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_2_7.lean`, the chapter
  owner abstraction for eventual superlinear scalar recurrences;
* `HasSuperlinearRateOfConvergence` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_8_15.lean`, which reuses
  that owner for trajectory-level superlinear convergence;
* `HasConvergenceRateOfOrder` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_6_9.lean`, a neighboring
  source-facing owner for eventual scalar comparison rates;
* `quadratic_tail_bound` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Proposition_1_7_6.lean`, a downstream owner-level
  consequence of the same quadratic recurrence.

Best owner abstraction:
* `HasEventuallySuperlinearErrorBound r 0 c 0`

Primitive data:
* the sequence `r`
* the constant `c`
* the owner recurrence witness `HasEventuallySuperlinearErrorBound r 0 c 0`

Derived API:
* the textbook quadratic recurrence `r (k + 1) ≤ c * (r k)^2`
* the converse packaging of that recurrence into the owner
* the one-step linear estimate once `c * r k ≤ 1 / 2`

Source/core/bridge triage:
* source-facing: the quadratic-rate existential statement from Definition 1.2.7
* core/canonical: the owner `HasEventuallySuperlinearErrorBound`
* bridge/view: the three recalled companion theorems below

This item intentionally keeps no parallel local definition of `HasEventuallySuperlinearErrorBound`
and no duplicate local proofs of its bridge lemmas. The numbered item is recalled directly through
the canonical chapter owner surface. -/

/- Definition 1.2.7: a quadratic rate of convergence is the canonical specialization
`∃ c > 0, HasEventuallySuperlinearErrorBound r 0 c 0`. -/
#check (∃ c > 0, HasEventuallySuperlinearErrorBound r 0 c 0)

namespace HasEventuallySuperlinearErrorBound

/- The textbook quadratic recurrence is recalled directly from the owner specialization. -/
recall quadratic_bound
    (h : HasEventuallySuperlinearErrorBound r 0 c 0)
    (k : ℕ) :
    r (k + 1) ≤ c * (r k)^2

/- The explicit quadratic recurrence packages back into the canonical owner specialization. -/
recall of_quadratic_bound
    (h : ∀ k : ℕ, r (k + 1) ≤ c * (r k)^2) :
    HasEventuallySuperlinearErrorBound r 0 c 0

/- Once `c * r k ≤ 1 / 2`, the quadratic owner specialization yields the one-step linear bound. -/
recall linear_bound_of_mul_le_half
    (h : HasEventuallySuperlinearErrorBound r 0 c 0)
    {k : ℕ}
    (hrk : 0 ≤ r k)
    (hthreshold : c * r k ≤ (1 / 2 : ℝ)) :
    r (k + 1) ≤ (1 / 2 : ℝ) * r k

end HasEventuallySuperlinearErrorBound

/-! ### Definition_1_2_8 (from Chap01) -/
universe u v w

variable {Problem : Type u} {Query : Type v} {Answer : Type w}

/- Definition 1.2.8 is a recall item in the Chapter 1 black-box optimization-oracle domain.
The canonical owner is the curried class-oracle type `Problem → Query → Answer`; fixed-problem
evaluations `oracle problem : Query → Answer` and locality predicates such as
`OptimizationOracle.IsLocal` are derived views built on top of this owner. -/

/- Definition 1.2.8: an optimization oracle for problem instances in `Problem` and query points in
`Query` is just a curried answer rule `Problem → Query → Answer`. -/
#check (Problem → Query → Answer)

/-! ### Definition_1_2_8 (from Items/Chap01) -/
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

/-! ### Definition_1_2_9 (from Chap01) -/
open scoped Gradient

universe u

/- Definition 1.2.9 lies in the black-box optimization-oracle / differential-answer-map domain.

Source/core/bridge triage:
* source-facing: the textbook zero-, first-, and second-order oracle replies attached to an
  objective function;
* core/canonical: the Chapter 1 owner abstraction `Query → Answer` from Definition 1.2.2, with
  first- and second-order replies constrained by the pointwise owners `HasGradientAt` and
  `HasFDerivAt (∇ f)`;
* bridge/view: the Hessian matrix view from `Definition_1_4_16.lean`, which presents the owner
  Hessian operator `hessian f x` in coordinates.

Relevant owner-style declarations sampled before refining:
* `#check (Query → Answer)` in `Definition_1_2_2.lean`;
* `HasGradientAt` in `Definition_1_4_6.lean`, the pointwise owner for genuine first-order data;
* `SatisfiesExactLineSearch` in `Definition_1_6_3.lean`, which keeps `HasGradientAt` explicit
  rather than trusting the totalized gradient alone;
* `HasWeightedGradientSecondOrderExpansionAt` in `Definition_1_8_4.lean`, whose canonical bridge
  target is `HasGradientAt f g x ∧ HasFDerivAt (∇ f) H x`.

Owner abstraction:
* the oracle answer-map type `Query → Answer`

Primitive data:
* the objective function itself

Derived API:
* the zero-order value map `f`
* the first-order value-gradient map `x ↦ (f x, ∇ f x)` under the genuine-gradient owner
  `∀ x, HasGradientAt f (∇ f x) x`
* the second-order value-gradient-Hessian map `x ↦ (f x, ∇ f x, hessian f x)` under the genuine
  first- and second-order owners `HasGradientAt` and `HasFDerivAt (∇ f)`

Accordingly, this file recalls the canonical answer maps directly and introduces no parallel
public wrapper names for them. The zero-order clause stays at the bare function level, while the
first- and second-order clauses make the needed regularity assumptions explicit so that the
displayed answers are genuine differential data rather than totalized placeholders. -/

variable {E : Type u}
variable (f : E → ℝ)

/- Definition 1.2.9 (1): a zero-order oracle for the objective function `f` returns the value
`f x` at the query point `x`. -/
#check (f : E → ℝ)

section HigherOrder

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 1.2.9 (2): for an objective whose displayed gradient answers are genuine, a
first-order oracle returns both the value and the gradient at the query point. -/
#check
  ((fun _ x ↦ (f x, ∇ f x)) :
    (∀ x : E, HasGradientAt f (∇ f x) x) → E → ℝ × E)

/- Definition 1.2.9 (3): for an objective whose displayed gradient and Hessian answers are
genuine, a second-order oracle returns the value, the gradient, and the Hessian operator at the
query point. -/
#check
  ((fun _ _ x ↦ (f x, ∇ f x, hessian f x)) :
    (∀ x : E, HasGradientAt f (∇ f x) x) →
      (∀ x : E, HasFDerivAt (∇ f) (hessian f x) x) →
        E → ℝ × E × (E →L[ℝ] E))

end HigherOrder

/-! ### Definition_1_2_9 (from Items/Chap01) -/
open scoped Gradient

universe u

/- Definition 1.2.9 lies in the black-box optimization-oracle / differential-answer-map domain.

Source/core/bridge triage:
* source-facing: the textbook zero-, first-, and second-order oracle replies attached to an
  objective function;
* core/canonical: the Chapter 1 owner abstraction `Query → Answer` from Definition 1.2.2, with
  first- and second-order replies constrained by the pointwise owners `HasGradientAt` and
  `HasFDerivAt (∇ f)`;
* bridge/view: the Hessian matrix view from `Definition_1_4_16.lean`, which presents the owner
  Hessian operator `hessian f x` in coordinates.

Relevant owner-style declarations sampled before refining:
* `#check (Query → Answer)` in `Definition_1_2_2.lean`;
* `HasGradientAt` in `Definition_1_4_6.lean`, the pointwise owner for genuine first-order data;
* `SatisfiesExactLineSearch` in `Definition_1_6_3.lean`, which keeps `HasGradientAt` explicit
  rather than trusting the totalized gradient alone;
* `HasWeightedGradientHessianAt` in `Definition_1_8_4.lean`, whose canonical core is
  `HasGradientAt f g x ∧ HasFDerivAt (∇ f) H.toContinuousLinearMap x`.

Owner abstraction:
* the oracle answer-map type `Query → Answer`

Primitive data:
* the objective function itself

Derived API:
* the zero-order value map `f`
* the first-order value-gradient map `x ↦ (f x, ∇ f x)` under the genuine-gradient owner
  `∀ x, HasGradientAt f (∇ f x) x`
* the second-order value-gradient-Hessian map `x ↦ (f x, ∇ f x, hessian f x)` under the genuine
  first- and second-order owners `HasGradientAt` and `HasFDerivAt (∇ f)`

Accordingly, this file recalls the canonical answer maps directly and introduces no parallel
public wrapper names for them. The zero-order clause stays at the bare function level, while the
first- and second-order clauses make the needed regularity assumptions explicit so that the
displayed answers are genuine differential data rather than totalized placeholders. -/

variable {E : Type u}
variable (f : E → ℝ)

/- Definition 1.2.9 (1): a zero-order oracle for the objective function `f` returns the value
`f x` at the query point `x`. -/
#check (f : E → ℝ)

section HigherOrder

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 1.2.9 (2): for an objective whose displayed gradient answers are genuine, a
first-order oracle returns both the value and the gradient at the query point. -/
#check
  (show (∀ x : E, HasGradientAt f (∇ f x) x) → E → ℝ × E from
    fun _ x ↦ (f x, ∇ f x))

/- Definition 1.2.9 (3): for an objective whose displayed gradient and Hessian answers are
genuine, a second-order oracle returns the value, the gradient, and the Hessian operator at the
query point. -/
#check
  (show
      (∀ x : E, HasGradientAt f (∇ f x) x) →
        (∀ x : E, HasFDerivAt (∇ f) (hessian f x) x) →
          E → ℝ × E × (E →L[ℝ] E) from
    fun _ _ x ↦ (f x, ∇ f x, hessian f x))

end HigherOrder

/-! ### Definition_1_2_11 (from Chap01) -/
universe u v

variable {Query : Type u} {Answer : Type v}

/- Primary domain: analytical complexity of information-set-based black-box iterative schemes.

Source/core/bridge triage for Definition 1.2.11:
* source-facing: `GeneralIterativeScheme.IsAnalyticalComplexity`, the textbook predicate saying
  that `N` oracle-call/update cycles are required to reach the `ε`-stopping criterion;
* core/canonical: `IsLeast {k : ℕ | scheme.HaltsAt k} N` on the halting set;
* bridge/view: `GeneralIterativeScheme.isAnalyticalComplexity_iff`, which unpacks the source
  predicate as “halts at `N` and not earlier”.

Relevant declarations sampled before refining:
* `GeneralIterativeScheme.HaltsAt` in `Algorithm_1_2_10.lean`;
* `IsLeast` in mathlib `Order.Bounds.Defs`;
* `Nat.isLeast_find` in mathlib `Order/Nat.lean`;
* `Nat.find_eq_iff` in mathlib `Data/Nat/Find.lean`.

Primitive data:
* the scheme and its halting predicate `HaltsAt`.

Derived API:
* the source-facing analytical-complexity predicate and its owner/textbook bridge lemmas. -/

namespace GeneralIterativeScheme

variable (scheme : GeneralIterativeScheme Query Answer)

/-- Definition 1.2.11: a natural number `N` is the analytical complexity of a general iterative
scheme when `N` is the first oracle-call count at which the scheme reaches the chosen stopping
criterion. If the scheme never reaches that stopping criterion, no such `N` exists. -/
def IsAnalyticalComplexity (N : ℕ) : Prop :=
  IsLeast {k : ℕ | scheme.HaltsAt k} N

variable {scheme}
variable {N : ℕ}

/-- Analytical complexity means that the scheme reaches the chosen stopping criterion at `N` and
at no smaller oracle-call count. -/
-- Proof sketch: unfold the owner predicate `IsLeast`; the lower-bound clause says every halting
-- index is at least `N`, which on `ℕ` is equivalent to the absence of smaller halting indices.
@[simp] theorem isAnalyticalComplexity_iff :
    scheme.IsAnalyticalComplexity N ↔
      scheme.HaltsAt N ∧ ∀ m < N, ¬ scheme.HaltsAt m := by
  change IsLeast {k : ℕ | scheme.HaltsAt k} N ↔
    scheme.HaltsAt N ∧ ∀ m < N, ¬ scheme.HaltsAt m
  constructor
  · rintro ⟨hN, hleast⟩
    refine ⟨hN, fun m hm hmhalts ↦ ?_⟩
    exact (not_le_of_gt hm) (hleast hmhalts)
  · rintro ⟨hN, hlt⟩
    refine ⟨hN, fun m hm ↦ le_of_not_gt fun hmn ↦ ?_⟩
    exact hlt m hmn hm

end GeneralIterativeScheme

/-! ### Definition_1_2_11 (from Items/Chap01) -/
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
