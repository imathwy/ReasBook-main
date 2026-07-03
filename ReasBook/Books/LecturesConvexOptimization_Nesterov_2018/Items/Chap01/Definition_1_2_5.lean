import Mathlib.Tactic.Recall
import Nesterov.Chap01.Definition_1_2_5

-- Declarations for this item will be appended below by the statement pipeline.

variable {r : ℕ → ℝ}

/- Definition 1.2.5 lies in the chapter's scalar convergence-rate domain.

Layer targeted by this refinement:
* source-facing recall of the Chapter 1 owner file, plus direct recall of its canonical bridge
  theorems

Primary domain:
* power-law and square-root decay bounds for real-valued error sequences

Relevant owner-style declarations sampled before refining:
* `exists_power_law_bound_of_sqrt_bound` in `Nesterov/Chap01/Definition_1_2_5.lean`, the
  chapter theorem realizing the `1 / sqrt k` specialization of the textbook power-law bound;
* `IsOptimizationErrorSequence.hasConvergenceRateOfOrder_of_sqrt_bound` in the same file, the
  canonical bridge from the source-facing square-root estimate to the later owner
  `HasConvergenceRateOfOrder`;
* `HasConvergenceRateOfOrder` in `Nesterov/Chap01/Definition_1_6_9.lean`, the later Chapter 1
  owner abstraction for eventual comparison rates of optimization-error sequences;
* `sqrt_rate_complexity_bound` in `Nesterov/Chap01/Definition_1_2_5.lean`, the explicit
  complexity-threshold consequence used later in the chapter.

Source/core/bridge triage:
* source-facing: the existential power-law statement
  `∃ c > 0, ∃ p > 0, ∀ ⦃k : ℕ⦄, 0 < k → r k ≤ c / Real.rpow (k : ℝ) p`;
* core/canonical: the chapter owner file `Nesterov/Chap01/Definition_1_2_5.lean`;
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
