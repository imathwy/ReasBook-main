import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_26 (from Chap06) -/
open scoped ConstrainedArgmin

noncomputable section

universe u

variable {E₁ : Type u} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]

/- Definition 6.26 lies in the chapter's proximal-subproblem / constrained-minimization domain.

Sampled owner-style declarations:
- `linearOptimizationOracleObjective` in `Chap06/Theorem_6_11`, the earlier chapter owner for the
  affine-plus-regularizer objective on a feasible subtype;
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner for a
  feasible set together with a real-valued objective;
- `constrainedArgmin` / `argmin[Q]` and `mem_constrainedArgmin_iff` in
  `Chap01/Definition_1_3_3`, the canonical owner of minimizer sets on a feasible set;
- `explicitModelSmoothedProblem` in `Chap06/Definition_6_9`, the chapter pattern of keeping the
  optimization problem itself as the source-facing owner and deriving its minimizers via the
  Chapter 1 argmin API.

Best owner abstraction:
- source-facing: `proximalMinimizationProblem`;
- core/canonical: `linearOptimizationOracleObjective`, `SetConstrainedMinimizationProblem Q₁`, and
  `argmin[Set.univ]`;
- bridge/view: the pointwise formula for the problem objective.

Primitive data:
- a feasible set `Q₁ : Set E₁`;
- a prox term `d₁ : Q₁ → ℝ`;
- a linear functional `s : StrongDual ℝ E₁`.

Derived API:
- the affine-plus-regularizer objective `linearOptimizationOracleObjective s d₁` on the feasible
  subtype `Q₁`;
- the associated problem owner on `Q₁` with feasible set `Set.univ`;
- the canonical minimizer set `argmin[Set.univ] (proximalMinimizationProblem Q₁ d₁ s)`.

Source/core/bridge triage:
- source-facing: the proximal minimization problem from the text;
- core/canonical: `linearOptimizationOracleObjective`, `SetConstrainedMinimizationProblem`, and
  `argmin[Q]`;
- bridge/view: the pointwise formula below.

The previous file introduced a second public objective owner with the same interface and
mathematical content as `linearOptimizationOracleObjective`. This refinement removes that duplicate
wheel and defines the proximal subproblem directly through the chapter's existing affine-plus-
regularizer owner.
-/

/-- Definition 6.26: the proximal minimization subproblem is the constrained problem on the
feasible subtype `Q₁` whose objective is the canonical affine-plus-regularizer owner
`linearOptimizationOracleObjective s d₁`. Its minimizer set is the canonical Chapter 1 owner
`argmin[Set.univ] (proximalMinimizationProblem Q₁ d₁ s)`. -/
def proximalMinimizationProblem
    (Q₁ : Set E₁) (d₁ : Q₁ → ℝ) (s : StrongDual ℝ E₁) :
    SetConstrainedMinimizationProblem Q₁ where
  feasibleSet := Set.univ
  objective := linearOptimizationOracleObjective s d₁

/-- Unfolding the proximal minimization problem recovers the constrained problem with feasible set
`Set.univ` on `Q₁` and objective `linearOptimizationOracleObjective s d₁`. -/
-- Proof sketch: unfold `proximalMinimizationProblem`.
@[simp] theorem proximalMinimizationProblem_def
    (Q₁ : Set E₁) (d₁ : Q₁ → ℝ) (s : StrongDual ℝ E₁) :
    proximalMinimizationProblem Q₁ d₁ s =
      { feasibleSet := Set.univ
        objective := linearOptimizationOracleObjective s d₁ } := sorry

/-- The feasible set of the proximal minimization problem is the whole feasible subtype `Q₁`. -/
-- Proof sketch: unfold `proximalMinimizationProblem`.
@[simp] theorem proximalMinimizationProblem_feasibleSet
    (Q₁ : Set E₁) (d₁ : Q₁ → ℝ) (s : StrongDual ℝ E₁) :
    (proximalMinimizationProblem Q₁ d₁ s).feasibleSet = Set.univ := sorry

/-- The objective field of the proximal minimization problem is the canonical affine-plus-
regularizer objective `linearOptimizationOracleObjective s d₁`. -/
-- Proof sketch: unfold `proximalMinimizationProblem`.
@[simp] theorem proximalMinimizationProblem_objective
    (Q₁ : Set E₁) (d₁ : Q₁ → ℝ) (s : StrongDual ℝ E₁) :
    (proximalMinimizationProblem Q₁ d₁ s).objective =
      linearOptimizationOracleObjective s d₁ := sorry

/-- Evaluating the proximal minimization problem at a feasible point gives the prox term plus the
linear pairing. -/
-- Proof sketch: use `proximalMinimizationProblem_objective` and
-- `linearOptimizationOracleObjective_apply`, then commute the summands.
theorem proximalMinimizationProblem_spec
    (Q₁ : Set E₁) (d₁ : Q₁ → ℝ) (s : StrongDual ℝ E₁) (x : Q₁) :
    proximalMinimizationProblem Q₁ d₁ s x =
      d₁ x + s x := sorry

/-- Evaluating the proximal minimization problem gives the prox term plus the linear pairing. -/
-- Proof sketch: apply `proximalMinimizationProblem_spec`.
@[simp] theorem proximalMinimizationProblem_apply
    (Q₁ : Set E₁) (d₁ : Q₁ → ℝ) (s : StrongDual ℝ E₁) (x : Q₁) :
    proximalMinimizationProblem Q₁ d₁ s x =
      d₁ x + s x := sorry

/-- The canonical minimizer set of the proximal minimization problem is exactly the argmin set of
`linearOptimizationOracleObjective s d₁` on the feasible subtype `Q₁`. -/
-- Proof sketch: unfold `proximalMinimizationProblem`; both sides reduce to the same argmin set on
-- `Set.univ`.
@[simp] theorem proximalMinimizationProblem_argmin
    (Q₁ : Set E₁) (d₁ : Q₁ → ℝ) (s : StrongDual ℝ E₁) :
    argmin[Set.univ] (proximalMinimizationProblem Q₁ d₁ s) =
      argmin[Set.univ] (linearOptimizationOracleObjective s d₁) := sorry

end

/-! ### Proposition_6_26 (from Chap06) -/
universe u v

section

variable {X : Type u} {U : Type v}

/- Proposition 6.26 lies in the Chapter 6 scalar duality-gap / smoothing-parameter algebra domain.

Mandatory domain-style sampling before refinement:
- `raw_duality_gap_le_excessive_gap_budget` in `Chap06/Lemma_6_2_1`, the chapter owner turning an
  excessive-gap certificate into the source-level budget estimate
  `f xBar - φ uBar ≤ μ₁ D₁ + μ₂ D₂`;
- `scaled_smoothing_parameter_product_eq` in `Chap06/Proposition_6_28`, the nearby scalar owner
  for the same parametrization of `μ₁` and `μ₂`;
- mathlib `Real.sqrt_div` and `Real.sqrt_mul`, the canonical square-root simplification API behind
  the identities `√(D₂ / D₁) * D₁ = √(D₁ D₂)` and `√(D₁ / D₂) * D₂ = √(D₁ D₂)`.

Best owner abstraction:
- source-facing: the raw duality-gap estimate obtained after substituting the symmetric
  parametrization of the smoothing parameters;
- core/canonical: a single real inequality for `f xBar - φ uBar`;
- bridge/view: the budget expression `μ₁ D₁ + μ₂ D₂` rewritten via the defining formulas for `μ₁`
  and `μ₂`.

Primitive data:
- the primal and dual objective values `f xBar` and `φ uBar`;
- the positive constants `D₁` and `D₂`;
- the induced norm value `‖A‖_{1,2}`, recorded directly as the scalar `opNorm12`;
- the smoothing parameters `μ₁` and `μ₂`.

Derived API:
- the symmetric bound `(λ₁ + λ₂) ‖A‖_{1,2} √(D₁ D₂)` obtained by substituting the parametrization
  into the budget estimate.

Source/core/bridge triage:
- source-facing: Proposition 6.26's symmetric duality-gap estimate under parametrization;
- core/canonical: the scalar theorem below;
- bridge/view: the substitution of the parametrized smoothing parameters into the raw budget.

The source mentions a linear operator `A`, but only its induced norm `‖A‖_{1,2}` enters the
statement. Following the statement-stage binder minimization rule, the Lean theorem keeps only this
norm value as explicit data. -/

-- Proof sketch: substitute the defining formulas for `μ₁` and `μ₂` into the assumed bound
-- `f xBar - φ uBar ≤ μ₁ D₁ + μ₂ D₂`, simplify
-- `Real.sqrt (D₂ / D₁) * D₁ = Real.sqrt (D₁ * D₂)` and
-- `Real.sqrt (D₁ / D₂) * D₂ = Real.sqrt (D₁ * D₂)` using `hD₁` and `hD₂`, and then factor out
-- the common term `opNorm12 * Real.sqrt (D₁ * D₂)`.
/-- Proposition 6.26 [Chapter6_2.json:74]: if the raw duality gap is bounded by `μ₁ D₁ + μ₂ D₂`
and the smoothing parameters satisfy
`μ₁ = λ₁ ‖A‖_{1,2} √(D₂ / D₁)` and `μ₂ = λ₂ ‖A‖_{1,2} √(D₁ / D₂)`,
then the gap is bounded by `(λ₁ + λ₂) ‖A‖_{1,2} √(D₁ D₂)`. -/
theorem raw_duality_gap_le_symmetric_bound_of_parametrized_smoothing_parameters
    {f : X → ℝ} {φ : U → ℝ} {xBar : X} {uBar : U}
    {D₁ D₂ lambda₁ lambda₂ μ₁ μ₂ opNorm12 : ℝ}
    (hD₁ : 0 < D₁) (hD₂ : 0 < D₂)
    (hμ₁ : μ₁ = lambda₁ * opNorm12 * Real.sqrt (D₂ / D₁))
    (hμ₂ : μ₂ = lambda₂ * opNorm12 * Real.sqrt (D₁ / D₂))
    (hgap : f xBar - φ uBar ≤ μ₁ * D₁ + μ₂ * D₂) :
    f xBar - φ uBar ≤ (lambda₁ + lambda₂) * opNorm12 * Real.sqrt (D₁ * D₂) := sorry

end
