import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_6_1_4_1_Oracle_Complexity_Preserved_Under_Entropic_Smoothing (from Chap06) -/
universe u v

variable {Query : Type u} {Answer : Type v}

/- Text 6.1.4.1 lies in the chapter's oracle/arithmetic-complexity bridge domain for dense
simplex matrix-game oracles.

Mandatory domain-style sampling before refinement:
* `GeneralIterativeScheme.iterationArithmeticWork`,
  `GeneralIterativeScheme.totalArithmeticWork`, and
  `GeneralIterativeScheme.IsArithmeticalComplexity` in `Chap01/Definition_1_2_12`, the project
  owners for accumulated arithmetic work and arithmetical complexity on an iterative scheme;
* `HasEllipsoidMethodComplexityBounds` in `Chap05/Definition_5_4_9_2`, the nearby chapter pattern
  where primitive per-iteration cost data feed a higher-level complexity statement;
* `semidefiniteNewtonStepDenseArithmeticWorkBound` in `Chap05/Proposition_5_4_4_3`, the nearby
  source-facing one-shot dense arithmetic-work owner on primitive size parameters;
* `fastGradient_oracleComplexity_le_const_div_epsilon_of_smoothApproximation` in
  `Chap06/Text_6_1_1_Complexity_Insight`, the Chapter 6 oracle-count bridge showing how a
  smoothing estimate is meant to feed a genuine complexity conclusion rather than stop at a local
  scalar or per-call bound.

Best owner abstraction:
* source-facing: `GeneralIterativeScheme.IsAnalyticalComplexity`, the Chapter 1 owner for
  oracle-call complexity, together with the original and entropy-smoothed dense one-call simplex
  matrix-game oracle work bounds on the primitive simplex dimensions `Δ[n]` and `Δ[m]`;
* core/canonical: `GeneralIterativeScheme.totalArithmeticWork` and
  `GeneralIterativeScheme.IsArithmeticalComplexity`;
* bridge/view: the constant-factor comparison passing from the per-call dense bounds to the
  Chapter 1 arithmetical-complexity owner.

Primitive data:
* the two schemes whose halting indices encode oracle complexity;
* the positive simplex dimensions `n` and `m`;
* the two dense one-call oracle arithmetic-work bounds.

Derived API:
* the oracle-complexity preservation theorem on `GeneralIterativeScheme.IsAnalyticalComplexity`;
* the per-iteration and total-work comparisons on `GeneralIterativeScheme`;
* the Chapter 1 arithmetical-complexity preservation theorem.

Source/core/bridge triage:
* source-facing: the oracle-complexity preservation statement on
  `GeneralIterativeScheme.IsAnalyticalComplexity`;
* core/canonical: `GeneralIterativeScheme.totalArithmeticWork` and
  `GeneralIterativeScheme.IsArithmeticalComplexity`;
* bridge/view: the dense one-call oracle work bounds and the theorems showing that the smoothed
  dense oracle model changes arithmetical complexity by at most a constant factor.

The review issue in the previous round was that the main theorem had drifted from oracle
complexity to the Chapter 1 arithmetic-cost bridge. This refinement keeps the dense one-call
arithmetic bounds as companion data, restores the main public outcome to the Chapter 1
oracle-complexity owner `GeneralIterativeScheme.IsAnalyticalComplexity`, and leaves the
arithmetical-complexity consequence below as an explicit companion bridge. -/

namespace GeneralIterativeScheme

variable (scheme : GeneralIterativeScheme Query Answer)
variable (oracleWork originalOracleWork smoothedOracleWork : Query → Answer → ℕ)
variable (methodWork originalMethodWork smoothedMethodWork : Set (Query × Answer) → ℕ)

/-- A pointwise constant-factor bound on iteration work accumulates to the same constant-factor
bound on total arithmetic work. -/
theorem totalArithmeticWork_le_mul_of_iterationArithmeticWork_le_mul
    (C N : ℕ)
    (hiter :
      ∀ k,
        scheme.iterationArithmeticWork smoothedOracleWork smoothedMethodWork k ≤
          C * scheme.iterationArithmeticWork originalOracleWork originalMethodWork k) :
    scheme.totalArithmeticWork smoothedOracleWork smoothedMethodWork N ≤
      C * scheme.totalArithmeticWork originalOracleWork originalMethodWork N := by
  unfold GeneralIterativeScheme.totalArithmeticWork
  refine le_trans (Finset.sum_le_sum fun k hk ↦ hiter k) ?_
  simp [Finset.mul_sum]

/-- If one arithmetic-work model is bounded termwise by a constant multiple of another along the
same informational trajectory, then any arithmetical complexity for the original model yields an
arithmetical complexity for the new model with the same constant-factor bound. -/
theorem exists_isArithmeticalComplexity_le_mul_of_iterationArithmeticWork_le_mul
    {C M : ℕ}
    (hM :
      scheme.IsArithmeticalComplexity originalOracleWork originalMethodWork M)
    (hiter :
      ∀ k,
        scheme.iterationArithmeticWork smoothedOracleWork smoothedMethodWork k ≤
          C * scheme.iterationArithmeticWork originalOracleWork originalMethodWork k) :
    ∃ M',
      scheme.IsArithmeticalComplexity smoothedOracleWork smoothedMethodWork M' ∧
        M' ≤ C * M := by
  rcases hM with ⟨N, hN, rfl⟩
  refine ⟨scheme.totalArithmeticWork smoothedOracleWork smoothedMethodWork N, ?_, ?_⟩
  · exact ⟨N, hN, rfl⟩
  · exact
      scheme.totalArithmeticWork_le_mul_of_iterationArithmeticWork_le_mul
        originalOracleWork smoothedOracleWork originalMethodWork smoothedMethodWork C N hiter

end GeneralIterativeScheme

/-- A dense arithmetic-work upper bound for one call to the original simplex matrix-game
first-order oracle on `Δ[n] × Δ[m]`, under the convention that each scalar affine update,
comparison, and vector entry write has constant cost. The bound consists of one dense scan of the
`m` affine payoffs, one maximizing-coordinate pass, and one length-`n` subgradient assembly. -/
def simplexMatrixGameOriginalFirstOrderOracleDenseArithmeticWorkBound (n m : ℕ+) : ℕ :=
  (m : ℕ) * (n : ℕ) + (m : ℕ) + (n : ℕ)

/-- A dense arithmetic-work upper bound for one call to the entropy-smoothed simplex matrix-game
first-order oracle on `Δ[n] × Δ[m]`, under the same dense convention and the additional
convention that each scalar `exp`, `log`, division, and normalization update in the softmax /
log-sum-exp evaluation has constant cost per coordinate. The bound consists of one dense affine
scan, one softmax / log-sum-exp normalization pass, and one dense averaged-gradient back
substitution. -/
def simplexMatrixGameEntropicSmoothingFirstOrderOracleDenseArithmeticWorkBound
    (n m : ℕ+) : ℕ :=
  2 * (m : ℕ) * (n : ℕ) + 4 * (m : ℕ) + (n : ℕ) + 1

-- Proof sketch: both oracle models require the same dense matrix-vector scan of the `m` affine
-- coordinates. The entropy-smoothed oracle adds only the softmax normalization and one averaged
-- back-substitution for the gradient, which is a fixed-constant multiple of the original dense
-- oracle bound once the simplex dimensions are positive.
/-- For each dense simplex matrix-game oracle call, the entropy-smoothed arithmetic-work model is
bounded by eight times the original dense oracle arithmetic-work model. -/
theorem
    simplexMatrixGameEntropicSmoothingFirstOrderOracleDenseArithmeticWorkBound_le_eight_mul_original
    (n m : ℕ+) :
    simplexMatrixGameEntropicSmoothingFirstOrderOracleDenseArithmeticWorkBound n m ≤
      8 * simplexMatrixGameOriginalFirstOrderOracleDenseArithmeticWorkBound n m := by
  have hn : (1 : ℤ) ≤ (n : ℕ) := by
    exact_mod_cast Nat.succ_le_of_lt n.pos
  have hm : (1 : ℤ) ≤ (m : ℕ) := by
    exact_mod_cast Nat.succ_le_of_lt m.pos
  exact_mod_cast (show
    (2 : ℤ) * (m : ℕ) * (n : ℕ) + 4 * (m : ℕ) + (n : ℕ) + 1 ≤
      8 * ((m : ℕ) * (n : ℕ) + (m : ℕ) + (n : ℕ)) by
    nlinarith)

/-- Replacing the original dense simplex matrix-game oracle cost by the entropy-smoothed dense
oracle cost changes each iteration's oracle-only arithmetic work by at most a factor of `8`. -/
theorem simplexMatrixGameEntropicSmoothing_iterationArithmeticWork_le_eight_mul_original
    (scheme : GeneralIterativeScheme Query Answer) (n m : ℕ+) (k : ℕ) :
    scheme.iterationArithmeticWork
        (fun _ _ ↦ simplexMatrixGameEntropicSmoothingFirstOrderOracleDenseArithmeticWorkBound n m)
        (fun _ ↦ 0) k ≤
      8 * scheme.iterationArithmeticWork
        (fun _ _ ↦ simplexMatrixGameOriginalFirstOrderOracleDenseArithmeticWorkBound n m)
        (fun _ ↦ 0) k := by
  simpa [GeneralIterativeScheme.iterationArithmeticWork] using
    simplexMatrixGameEntropicSmoothingFirstOrderOracleDenseArithmeticWorkBound_le_eight_mul_original
      n m

/-- Replacing the original dense simplex matrix-game oracle cost by the entropy-smoothed dense
oracle cost changes the Chapter 1 total arithmetic work of an oracle-only scheme by at most a
factor of `8`. -/
theorem simplexMatrixGameEntropicSmoothing_totalArithmeticWork_le_eight_mul_original
    (scheme : GeneralIterativeScheme Query Answer) (n m : ℕ+) (N : ℕ) :
    scheme.totalArithmeticWork
        (fun _ _ ↦ simplexMatrixGameEntropicSmoothingFirstOrderOracleDenseArithmeticWorkBound n m)
        (fun _ ↦ 0) N ≤
      8 * scheme.totalArithmeticWork
        (fun _ _ ↦ simplexMatrixGameOriginalFirstOrderOracleDenseArithmeticWorkBound n m)
        (fun _ ↦ 0) N := by
  exact
    scheme.totalArithmeticWork_le_mul_of_iterationArithmeticWork_le_mul
      (fun _ _ ↦ simplexMatrixGameOriginalFirstOrderOracleDenseArithmeticWorkBound n m)
      (fun _ _ ↦ simplexMatrixGameEntropicSmoothingFirstOrderOracleDenseArithmeticWorkBound n m)
      (fun _ ↦ 0) (fun _ ↦ 0) 8 N
      (fun k ↦
        simplexMatrixGameEntropicSmoothing_iterationArithmeticWork_le_eight_mul_original
          scheme n m k)

-- Proof sketch: pass from the one-call dense comparison to the Chapter 1 owner
-- `GeneralIterativeScheme.IsArithmeticalComplexity` using the accumulation theorem above, with
-- zero additional method work because this source item isolates oracle arithmetic cost.
/-- Text 6.1.4.1-Oracle Complexity Preserved Under Entropic Smoothing: if the entropy-smoothed
and original simplex matrix-game schemes halt at exactly the same oracle-call counts, then any
analytical-complexity witness for the original scheme is also an analytical-complexity witness for
the smoothed scheme. Thus entropic smoothing preserves oracle complexity on the Chapter 1 owner
surface `GeneralIterativeScheme.IsAnalyticalComplexity`; the factor-`8` arithmetic-work theorem
below is only a companion bridge. -/
theorem simplexMatrixGameEntropicSmoothing_preserves_analyticalComplexity
    {originalScheme smoothedScheme : GeneralIterativeScheme Query Answer} {N : ℕ}
    (hhalt : ∀ k, originalScheme.HaltsAt k ↔ smoothedScheme.HaltsAt k)
    (hN : originalScheme.IsAnalyticalComplexity N) :
    smoothedScheme.IsAnalyticalComplexity N := by
  rcases (originalScheme.isAnalyticalComplexity_iff).mp hN with ⟨hhalts, hminimal⟩
  refine (smoothedScheme.isAnalyticalComplexity_iff).mpr ?_
  refine ⟨(hhalt N).mp hhalts, ?_⟩
  intro m hm hmhalts
  exact hminimal m hm ((hhalt m).mpr hmhalts)

/-- Companion Chapter 1 arithmetic-complexity bridge: if a general iterative scheme has
arithmetical complexity `M` when each oracle call is charged by the original dense simplex
matrix-game first-order oracle model and no additional method work is counted, then under the
entropy-smoothed dense oracle model there exists an arithmetical complexity `M'` with
`M' ≤ 8 M`. This is an arithmetic-cost consequence of the dense one-call comparison, not the main
oracle-complexity statement of Text 6.1.4.1. -/
theorem simplexMatrixGameEntropicSmoothing_isArithmeticalComplexity_le_eight_mul_original
    (scheme : GeneralIterativeScheme Query Answer) (n m : ℕ+) {M : ℕ}
    (hM :
      scheme.IsArithmeticalComplexity
        (fun _ _ ↦ simplexMatrixGameOriginalFirstOrderOracleDenseArithmeticWorkBound n m)
        (fun _ ↦ 0) M) :
    ∃ M',
      scheme.IsArithmeticalComplexity
        (fun _ _ ↦ simplexMatrixGameEntropicSmoothingFirstOrderOracleDenseArithmeticWorkBound n m)
        (fun _ ↦ 0) M' ∧
        M' ≤ 8 * M := by
  exact
    scheme.exists_isArithmeticalComplexity_le_mul_of_iterationArithmeticWork_le_mul
      (fun _ _ ↦ simplexMatrixGameOriginalFirstOrderOracleDenseArithmeticWorkBound n m)
      (fun _ _ ↦ simplexMatrixGameEntropicSmoothingFirstOrderOracleDenseArithmeticWorkBound n m)
      (fun _ ↦ 0) (fun _ ↦ 0) hM
      (fun k ↦
        simplexMatrixGameEntropicSmoothing_iterationArithmeticWork_le_eight_mul_original
          scheme n m k)

/-! ### Text_6_1_4_2_Average_Individual_Expense_Bound (from Chap06) -/
universe u

noncomputable section

section

variable {X : Type u}

open scoped BigOperators

/-
Text 6.1.4.2 lies in the whole-space objective-scaling / optimal-value domain.

Mandatory domain-style sampling before refinement:
- pointwise scalar multiplication on function spaces, the canonical owner for scaling a real-valued
  objective;
- `SetConstrainedMinimizationProblem` and `SetConstrainedMinimizationProblem.optimalValue` in
  `Chap01/Definition_1_3_7`, the Chapter 1 owner for exact optimal values in `EReal`;
- `scaledObjective_convergence_rate_bound` in `Chap06/Proposition_6_18`, the direct downstream
  specialization to a finite population split.

Best owner abstraction:
- source-facing: `averageIndividualExpense`, the textbook average-cost objective;
- core/canonical: pointwise scalar multiplication on `X → ℝ` together with the whole-space owner
  `SetConstrainedMinimizationProblem.mk Set.univ`;
- bridge/view: `averageIndividualExpense P f = P⁻¹ • f`.

Primitive data:
- the population factor `P`;
- the total-expense objective `f`.

Derived API:
- the pointwise evaluation lemma below;
- the whole-space optimal values of `f` and `averageIndividualExpense P f`.

Source/core/bridge triage:
- source-facing: the average individual expense objective and its suboptimality bound;
- core/canonical: function-space scaling and `SetConstrainedMinimizationProblem.optimalValue`;
- bridge/view: the identification of the source-facing average objective with `P⁻¹ • f`.
-/

/-- The average individual expense objective `x ↦ f(x) / P` obtained by dividing the total
expense by the positive population factor `P`. -/
abbrev averageIndividualExpense (P : ℝ) (f : X → ℝ) : X → ℝ :=
  P⁻¹ • f

/-- Evaluating `averageIndividualExpense P f` at `x` gives `f(x) / P`. -/
@[simp] theorem averageIndividualExpense_apply (P : ℝ) (f : X → ℝ) (x : X) :
    averageIndividualExpense P f x = f x / P := by
  simp [averageIndividualExpense, div_eq_mul_inv, mul_comm]

-- Proof sketch: rewrite `averageIndividualExpense P f` as the canonical scalar multiple `P⁻¹ • f`,
-- compare the Chapter 1 whole-space optimal values of `f` and `averageIndividualExpense P f`, and
-- divide the assumed total-expense bound by the positive factor `P`.
/-- Text 6.1.4.2-Average Individual Expense Bound: if
`f(xHat) - f* ≤ 2 P * rBar / √(N (N + 1))` with positive population factor `P`, then the average
individual expense `\bar f(x) = f(x) / P` satisfies
`\bar f(xHat) - \bar f* ≤ 2 rBar / √(N (N + 1))`, where both optimal values are taken through the
Chapter 1 whole-space owner in `EReal`. -/
theorem average_individual_expense_suboptimality_bound
    (P : ℝ) (f : X → ℝ) (xHat : X) {rBar : ℝ} {N : ℕ}
    (hP : 0 < P)
    (hbound :
      (f xHat : EReal) - (SetConstrainedMinimizationProblem.mk Set.univ f).optimalValue ≤
        (2 * P * rBar) / Real.sqrt (N * (N + 1) : ℝ)) :
    (averageIndividualExpense P f xHat : EReal) -
        (SetConstrainedMinimizationProblem.mk Set.univ
          (averageIndividualExpense P f)).optimalValue ≤
      (2 * rBar) / Real.sqrt (N * (N + 1) : ℝ) := sorry

end

/-! ### Text_6_1_4_2_Population_Interpretation (from Chap06) -/
open scoped BigOperators

noncomputable section

universe u v

variable {ι : Type u}

/-- The positive population weights `m_j` used in the continuous location model. -/
abbrev ContinuousLocationWeights (ι : Type u) :=
  ι → {m : ℝ // 0 < m}

namespace ContinuousLocationWeights

@[simp] theorem weights_pos (weights : ContinuousLocationWeights ι) (j : ι) :
    0 < (weights j : ℝ) :=
  (weights j).2

end ContinuousLocationWeights

section

variable [Fintype ι]
variable (E : Type v) [NormedAddCommGroup E]

/-- The dual feasible set `Q₂`, consisting of tuples whose components all have norm at most `1`. -/
def continuousLocationDualAdmissibleSet : Set (ι → E) :=
  {u | ∀ j, ‖u j‖ ≤ 1}

/-- The weighted Euclidean norm on dual tuples used to define the prox-function `d₂`. -/
def continuousLocationDualTupleNorm
    (weights : ContinuousLocationWeights ι) (u : ι → E) : ℝ :=
  Real.sqrt (∑ j, (weights j : ℝ) * ‖u j‖ ^ (2 : ℕ))

/-- The prox-function `d₂(u) = (1 / 2) \sum_j m_j \|u_j\|^2`, written via the weighted
tuple norm. -/
def continuousLocationDualProxFunction
    (weights : ContinuousLocationWeights ι) : (ι → E) → ℝ :=
  fun u ↦ (1 / 2 : ℝ) * (continuousLocationDualTupleNorm E weights u) ^ (2 : ℕ)

end

section

variable [Fintype ι]

/-- The total population weight `P = \sum_j m_j` in the continuous location model. -/
def continuousLocationTotalPopulation (weights : ContinuousLocationWeights ι) : ℝ :=
  ∑ j, (weights j : ℝ)

end

variable [Fintype ι]

-- Proof sketch: unfold `continuousLocationTotalPopulation`.
/-- Expanding `continuousLocationTotalPopulation` gives the finite sum `\sum_j m_j`. -/
theorem continuousLocationTotalPopulation_def
    (weights : ContinuousLocationWeights ι) :
    continuousLocationTotalPopulation weights = ∑ j, (weights j : ℝ) :=
  rfl

section

variable [Fintype ι]
variable (E : Type v) [NormedAddCommGroup E]

/-- The quantity `D₂`, defined as the maximal value of the prox-function `d₂` on the dual
feasible set `Q₂`. -/
def continuousLocationDualProxMaximum (weights : ContinuousLocationWeights ι) : ℝ :=
  sSup (continuousLocationDualProxFunction E weights '' continuousLocationDualAdmissibleSet E)

end

section

variable (E : Type v) [NormedAddCommGroup E]

-- Proof sketch: unfold `continuousLocationDualProxMaximum`.
/-- Expanding `continuousLocationDualProxMaximum` gives the supremum of `d₂` over `Q₂`. -/
theorem continuousLocationDualProxMaximum_def
    (weights : ContinuousLocationWeights ι) :
    continuousLocationDualProxMaximum E weights =
      sSup
        (continuousLocationDualProxFunction E weights ''
          continuousLocationDualAdmissibleSet E) :=
  rfl

-- Proof sketch: in a nontrivial real normed space, choose for each block `u_j` a unit vector;
-- then every component saturates the constraint `‖u_j‖ ≤ 1`, so `d₂(u) = (1 / 2) * ∑_j m_j`.
-- The reverse inequality follows because each admissible block has norm at most `1`, hence
-- `‖u_j‖^2 ≤ 1` in the weighted sum defining `d₂`.
/-- Text 6.1.4.2-Population Interpretation: in a nontrivial real normed space, the maximal value
`D₂` of the prox-function `d₂` on `Q₂` equals `P / 2`, where `P = \sum_j m_j` is the total
population weight of the model. -/
theorem continuousLocationDualProxMaximum_eq_half_totalPopulation
    [NormedSpace ℝ E] [Nontrivial E] (weights : ContinuousLocationWeights ι) :
    continuousLocationDualProxMaximum E weights = continuousLocationTotalPopulation weights / 2 :=
  sorry

end

end

/-! ### Text_6_1_5_1_Per_Iteration_Complexity_Decomposition (from Chap06) -/
open scoped ConstrainedArgmin

noncomputable section

universe u v

section

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/- Text 6.1.5.1 lies in the chapter's smoothed-dual-oracle / proximal-subproblem decomposition
domain.

Mandatory domain-style sampling before refinement:
- `smoothedPrimalObjectiveArgmax` in `Definition_6_30`, the Chapter 6 owner of the Step (b)
  regularized dual maximizer set;
- `mem_smoothedPrimalObjectiveArgmax_iff` in `Definition_6_30`, the bridge expanding that owner to
  the feasible-maximizer formulation;
- `proximalMinimizationProblem` in `Definition_6_26`, the Chapter 6 owner of the Step (c)
  estimating-function minimization problem;
- `argmin[Q]` in `Chap01/Definition_1_3_3`, the project owner of feasible minimizer sets.

Best owner abstraction:
- source-facing: the per-iteration split into the Step (b) dual-oracle maximization problem and
  the Step (c) proximal minimization problem;
- core/canonical: `smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ yk`,
  `proximalMinimizationProblem Q₁ d₁ s`, `argmin[Set.univ]`, and `Set.prod`;
- bridge/view: the product of those two canonical solution sets, with membership expanded by
  `Set.mem_prod`.

Primitive data:
- the fixed iterate `y_k`, feasible sets `Q₁`, `Q₂`, linear map `A`, dual penalty `hatφ`,
  prox-terms `d₁`, `d₂`, smoothing parameter `μ`, and linear functional `s`.

Derived API:
- the Step (b) solution set `smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ yk`;
- the Step (c) solution set `argmin[Set.univ] (proximalMinimizationProblem Q₁ d₁ s)`;
- their combined decomposition view as a product of canonical solution sets.

Source/core/bridge triage:
- source-facing: Text 6.1.5.1's statement that one iteration decomposes into two canonical
  subproblems;
- core/canonical: the Chapter 6 dual-oracle argmax owner and the Chapter 1 constrained-argmin
  owner;
- bridge/view: the product-set view combining those two owners without introducing a second
  solution package.

The previous version introduced a public structure `SmoothedMethodIterationDecomposition` whose
primitive fields were a chosen dual maximizer and a chosen proximal minimizer. That was too
low-level for this text item: the source mathematics is the intrinsic decomposition into the two
canonical subproblems, not an auxiliary package of chosen outputs. This refinement therefore keeps
only the owner-level surface and the canonical product view of the two solution sets.
-/

variable
  {Q₁ : Set E₁} (Q₂ : Set E₂) (hatφ : E₂ → ℝ)
  (A : E₁ →L[ℝ] StrongDual ℝ E₂) (d₂ : E₂ → ℝ) (μ : ℝ)
  (d₁ : Q₁ → ℝ) (yk : Q₁) (s : StrongDual ℝ E₁)

/- Text 6.1.5.1 uses the Chapter 6 dual-oracle argmax owner for Step (b) and the Chapter 6
proximal minimization problem together with the Chapter 1 argmin owner for Step (c). -/
recall smoothedPrimalObjectiveArgmax
recall mem_smoothedPrimalObjectiveArgmax_iff
recall proximalMinimizationProblem

/-- Text 6.1.5.1-Per-Iteration Complexity Decomposition: the per-iteration work of the smoothed
method at `y_k` is encoded by the product of the Step (b) smoothed-dual argmax set over `Q₂` and
the Step (c) proximal minimizer set over `Q₁`. -/
def smoothedMethodIterationSubproblemSolutions :
    Set (E₂ × Q₁) :=
  smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ yk ×ˢ
    argmin[Set.univ] (proximalMinimizationProblem Q₁ d₁ s)

-- Proof sketch: unfold `smoothedMethodIterationSubproblemSolutions`, rewrite pair membership in
-- the product set via `Set.mem_prod`, and expand the Step (b) factor with
-- `mem_smoothedPrimalObjectiveArgmax_iff`.
/-- A pair lies in `smoothedMethodIterationSubproblemSolutions` exactly when its first component is
a feasible maximizer for the Step (b) smoothed oracle subproblem and its second component solves
the Step (c) proximal minimization subproblem. -/
theorem mem_smoothedMethodIterationSubproblemSolutions_iff
    {u : E₂} {x : Q₁} :
    (u, x) ∈ smoothedMethodIterationSubproblemSolutions Q₂ hatφ A d₂ μ d₁ yk s ↔
      u ∈ Q₂ ∧
        IsMaxOn (smoothedPrimalObjectiveMaximand A hatφ d₂ μ yk) Q₂ u ∧
        x ∈ argmin[Set.univ] (proximalMinimizationProblem Q₁ d₁ s) := sorry

end

/-! ### Text_6_1_5_2_Stable_Log_Sum_Exp_Shift_Trick (from Chap06) -/
noncomputable section

open scoped Gradient

/- Text 6.1.5.2 lies in Chapter 6's finite-dimensional log-sum-exp stabilization domain.

Sampled owner-style declarations:
- `coordinateMaximum` in `Chap06/Proposition_6_23`, the chapter owner for the maximal coordinate;
- `centeredByCoordinateMaximum` in `Chap06/Proposition_6_23`, the canonical max-centered vector;
- `η` in `Chap06/Definition_6_27`, the recalled log-sum-exp potential;
- `eta_eq_coordinateMaximum_add_eta_centered` and
  `gradient_eta_eq_gradient_eta_centered` in `Chap06/Proposition_6_23`, the canonical stable
  shift identities.

Best owner abstraction:
- source-facing: the stable max-shift identity for the scaled log-sum-exp potential;
- core/canonical: `coordinateMaximum`, `centeredByCoordinateMaximum`, `η`, and the two stable
  shift theorems from `Proposition_6_23`;
- bridge/view: the coordinate observations that the centered vector is nonpositive and has a zero
  coordinate.

This item reuses the chapter owners directly for the stable shift formulas and keeps only the
centered-coordinate consequences as local statement skeletons.
-/

section

variable {m : ℕ} [NeZero m]

local notation "U" => EuclideanSpace ℝ (Fin m)

/- Text 6.1.5.2-Stable Log-Sum-Exp Shift Trick: if `v` is obtained by subtracting the maximal
coordinate `coordinateMaximum u` from every component of `u`, then the scaled log-sum-exp
potential satisfies the stable identity
`η μ u = coordinateMaximum u + η μ (centeredByCoordinateMaximum u)`. -/
recall eta_eq_coordinateMaximum_add_eta_centered

-- Proof sketch: `coordinateMaximum u` is the maximum of the finite coordinate family, so each
-- coordinate `u j` is bounded above by it. Rewriting
-- `centeredByCoordinateMaximum u j = u j - coordinateMaximum u` gives the claim.
/-- Every coordinate of the vector centered by its maximal coordinate is nonpositive. -/
theorem centeredByCoordinateMaximum_nonpos
    (u : U) (j : Fin m) :
    centeredByCoordinateMaximum u j ≤ 0 := sorry

-- Proof sketch: on the finite index type `Fin m`, the maximum defining `coordinateMaximum u` is
-- attained. At a maximizing coordinate, subtracting `coordinateMaximum u` leaves `0`.
/-- The vector centered by its maximal coordinate has at least one zero coordinate. -/
theorem centeredByCoordinateMaximum_exists_eq_zero
    (u : U) :
    ∃ j : Fin m, centeredByCoordinateMaximum u j = 0 := sorry

/- Subtracting the maximal coordinate from every component preserves the gradient of the scaled
log-sum-exp potential, so the same stable shift trick applies to gradient computation. -/
recall gradient_eta_eq_gradient_eta_centered

end
