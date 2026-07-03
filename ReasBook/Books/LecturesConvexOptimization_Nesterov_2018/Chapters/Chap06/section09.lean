import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_9 (from Chap06) -/
universe u

/- Definition 6.9 lies in the constrained smoothing / set-constrained minimization domain.

Sampled owner-style declarations:
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner for a
  feasible set together with a real-valued objective;
- `constrainedArgmin` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the canonical
  owner of feasible minimizers on a set;
- the derivative/Lipschitz theorem in `Chap06/Proposition_6_10`, which should talk directly about
  the present owner instead of introducing a second pointwise-sum wrapper.

Best owner abstraction:
- source-facing: the explicit-model smoothed optimization problem over `Q₁`;
- core/canonical: `SetConstrainedMinimizationProblem X`, with `argmin[Q₁] f` as derived API;
- bridge/view: the pointwise evaluation formula for the inherited objective.

Primitive data:
- a feasible set `Q₁ : Set X`;
- a model objective `hatf : X → ℝ`;
- a smoothing term `fμ : X → ℝ`.

Derived API:
- the objective coercion of `explicitModelSmoothedProblem Q₁ hatf fμ`;
- the canonical optimal set
  `argmin[(explicitModelSmoothedProblem Q₁ hatf fμ).feasibleSet]
    (explicitModelSmoothedProblem Q₁ hatf fμ)`;
- the standard membership bridge `mem_constrainedArgmin_iff`.

Source/core/bridge triage:
- source-facing: `explicitModelSmoothedProblem`;
- core/canonical: `SetConstrainedMinimizationProblem`;
- bridge/view: the evaluation lemma below.

The previous file stored the argmin set as a second public definition, but that data is already
owned upstream by `constrainedArgmin`. This refinement keeps only the source-facing problem owner
and lets minimizer sets be derived canonically.
-/

variable {X : Type u}

/-- Definition 6.9: for a model objective `\hat f` and smoothing term `f_μ`, the explicit-model
smoothed optimization problem on `Q₁` minimizes the sum `x ↦ \hat f(x) + f_μ(x)` over `Q₁`. -/
def explicitModelSmoothedProblem (Q₁ : Set X) (hatf fμ : X → ℝ) :
    SetConstrainedMinimizationProblem X where
  feasibleSet := Q₁
  objective := fun x ↦ hatf x + fμ x

/-- Unfolding `explicitModelSmoothedProblem Q₁ hatf fμ` recovers the feasible set `Q₁` together
with the summed objective `x ↦ \hat f(x) + f_μ(x)`. -/
-- Proof sketch: unfold `explicitModelSmoothedProblem`.
@[simp] theorem explicitModelSmoothedProblem_def
    (Q₁ : Set X) (hatf fμ : X → ℝ) :
    explicitModelSmoothedProblem Q₁ hatf fμ =
      { feasibleSet := Q₁, objective := fun x ↦ hatf x + fμ x } := sorry

/-- The feasible set of the explicit-model smoothed problem is exactly `Q₁`. -/
@[simp] theorem explicitModelSmoothedProblem_feasibleSet
    (Q₁ : Set X) (hatf fμ : X → ℝ) :
    (explicitModelSmoothedProblem Q₁ hatf fμ).feasibleSet = Q₁ :=
  rfl

/-- The objective field of the explicit-model smoothed problem is the sum
`x ↦ \hat f(x) + f_μ(x)`. -/
@[simp] theorem explicitModelSmoothedProblem_objective
    (Q₁ : Set X) (hatf fμ : X → ℝ) :
    (explicitModelSmoothedProblem Q₁ hatf fμ).objective = fun x ↦ hatf x + fμ x :=
  rfl

/-- The explicit-model smoothed problem evaluates to the summed objective
`\hat f(x) + f_μ(x)` at each point `x`. -/
theorem explicitModelSmoothedProblem_spec
    (Q₁ : Set X) (hatf fμ : X → ℝ) (x : X) :
    explicitModelSmoothedProblem Q₁ hatf fμ x = hatf x + fμ x :=
  rfl

/-- Evaluating the explicit-model smoothed problem gives the defining sum
`\hat f(x) + f_μ(x)`. -/
@[simp] theorem explicitModelSmoothedProblem_apply
    (Q₁ : Set X) (hatf fμ : X → ℝ) (x : X) :
    explicitModelSmoothedProblem Q₁ hatf fμ x = hatf x + fμ x :=
  explicitModelSmoothedProblem_spec Q₁ hatf fμ x

/-- The canonical argmin set of the explicit-model smoothed problem is exactly the argmin set of
the summed objective `x ↦ \hat f(x) + f_μ(x)` on `Q₁`. -/
-- Proof sketch: extensionality on points, then rewrite membership with
-- `mem_constrainedArgmin_iff`, `explicitModelSmoothedProblem_feasibleSet`, and
-- `explicitModelSmoothedProblem_isMinOn_iff`.
@[simp] theorem explicitModelSmoothedProblem_argmin
    (Q₁ : Set X) (hatf fμ : X → ℝ) :
    constrainedArgmin
        (explicitModelSmoothedProblem Q₁ hatf fμ).feasibleSet
        (explicitModelSmoothedProblem Q₁ hatf fμ) =
      constrainedArgmin Q₁ (fun y ↦ hatf y + fμ y) := sorry

/-- Minimizing the explicit-model smoothed problem on its feasible set is exactly minimizing the
summed objective `x ↦ \hat f(x) + f_μ(x)` on `Q₁`. -/
-- Proof sketch: unfold the feasible set and objective of `explicitModelSmoothedProblem`.
@[simp] theorem explicitModelSmoothedProblem_isMinOn_iff
    (Q₁ : Set X) (hatf fμ : X → ℝ) {x : X} :
    IsMinOn (explicitModelSmoothedProblem Q₁ hatf fμ)
        (explicitModelSmoothedProblem Q₁ hatf fμ).feasibleSet x ↔
      IsMinOn (fun y ↦ hatf y + fμ y) Q₁ x := sorry

/-- Membership in the canonical argmin set of the explicit-model smoothed problem means belonging
to `Q₁` and minimizing `x ↦ \hat f(x) + f_μ(x)` there. -/
-- Proof sketch: rewrite membership with `mem_constrainedArgmin_iff`, then use
-- `explicitModelSmoothedProblem_feasibleSet` and
-- `explicitModelSmoothedProblem_isMinOn_iff`.
@[simp] theorem mem_explicitModelSmoothedProblem_argmin_iff
    (Q₁ : Set X) (hatf fμ : X → ℝ) {x : X} :
    x ∈ constrainedArgmin
        (explicitModelSmoothedProblem Q₁ hatf fμ).feasibleSet
        (explicitModelSmoothedProblem Q₁ hatf fμ) ↔
      x ∈ Q₁ ∧ IsMinOn (fun y ↦ hatf y + fμ y) Q₁ x := sorry

/-! ### Lemma_6_9 (from Chap06) -/
/- Lemma 6.9 is the same switching-parameter recurrence statement already canonicalized in
`Lemma_6_2_4`. The owner theorem there now works directly with the pair-valued
`switching_parameters` sequence, so this file keeps only the direct recall surface. -/
recall alpha_succ_eq_one_sub_tau_mul_pred_of_alternating_scalar_updates

/-! ### Proposition_6_9 (from Chap06) -/
/- Proposition 6.9 lies in the Euclidean prox-function / radius-bound domain.

Sampled owner-style declarations:
- `quadraticDistanceTo` in `Remark_6_1_1`, the chapter owner of the Euclidean prox term
  `d(x) = (1 / 2) ‖x - x₀‖²`;
- `two_mul_quadraticDistanceTo` in `Remark_6_1_1`, the canonical bridge from the prox term back
  to the squared distance;
- `euclidean_prox_radius_bound` in `Remark_6_1_1`, the earlier chapter theorem with the exact
  source-facing radius estimate used here.

Best owner abstraction:
- source-facing: the Euclidean prox radius estimate from the squared-distance hypothesis;
- core/canonical: `euclidean_prox_radius_bound`;
- bridge/view: `two_mul_quadraticDistanceTo`.

Primitive data:
- the Euclidean prox center `x₀` and comparison point `xStar`;
- the iterate family `v : ℕ → E`;
- the source squared-distance hypothesis
  `‖v k - xStar‖ ^ (2 : ℕ) ≤ 2 * quadraticDistanceTo x₀ xStar`.

Derived API:
- the Euclidean prox owner `quadraticDistanceTo`;
- the expansion lemma `two_mul_quadraticDistanceTo`;
- the radius conclusion `‖v k - xStar‖ ≤ ‖x₀ - xStar‖`.

Source/core/bridge triage:
- source-facing: Proposition 6.9's Euclidean prox radius estimate;
- core/canonical: `euclidean_prox_radius_bound`;
- bridge/view: the helper conversion `two_mul_quadraticDistanceTo`.

The previous file duplicated the earlier chapter owner declaration, helper lemma, and theorem
verbatim. Proposition 6.9 adds no new mathematics beyond that earlier canonical theorem, so this
file is a pure recall item. -/

/- Proposition 6.9 is the earlier Euclidean prox radius theorem
`euclidean_prox_radius_bound`. -/
recall euclidean_prox_radius_bound

/-! ### Theorem_6_9 (from Chap06) -/
open RealSymmetricMatrixSpace
open scoped BigOperators MatrixOrder RealSymmetricMatrixSpace

noncomputable section

variable {n : ℕ}

local notation "SymmMat" => 𝕊^n

/- Theorem 6.9 lies in the chapter's symmetric-matrix trace-power / Hessian spectral domain.

Sampled owner-style declarations:
- Chapter 5 `𝕊^n` in `Definition_5_4_4_1`, the established owner for real symmetric matrices;
- Chapter 6 `RealSymmetricMatrixSpace.powerTrace`, written `π[k]`, the source-facing trace-power
  owner on `𝕊^n`;
- Chapter 5 `RealSymmetricMatrixSpace.eigenvalues`, the chapter's intrinsic ordered eigenvalue
  owner on `𝕊^n`;
- mathlib `CFC.abs`, together with `CFC.abs_nonneg` and Hermitian eigenvalues, as the canonical
  absolute-value owner for real symmetric matrices;
- mathlib `iteratedFDeriv`, the canonical Hessian quadratic-form owner for scalar-valued maps.

Best owner abstraction:
- source-facing: the Hessian quadratic-form bound for the Chapter 6 owner `π_k(X) = Trace (X^k)`
  on `𝕊^n`, together with the intrinsic spectral data coming from the matrix absolute values
  `CFC.abs X` and `CFC.abs H`;
- core/canonical: `π[k] : 𝕊^n → ℝ`, `iteratedFDeriv ℝ 2`, `eigenvalues`, and `CFC.abs`;
- bridge/view: Proposition 6.33's second-derivative expansion and the spectral inequality from
  Lemma 6.14.

Primitive data:
- `k : ℕ`;
- `X H : 𝕊^n`.

Derived API:
- the source-facing trace-power owner `π[k]`;
- the Hessian quadratic form `iteratedFDeriv ℝ 2 (π[k] : 𝕊^n → ℝ) X ![H, H]`;
- the Hermitian eigenvalue vectors of the matrix absolute values `CFC.abs X` and `CFC.abs H`.

Source/core/bridge triage:
- source-facing: Theorem 6.9's Hessian quadratic-form inequality on `𝕊^n`;
- core/canonical: `π[k]`, `iteratedFDeriv`, `eigenvalues`, and `CFC.abs`;
- bridge/view: the ambient trace/Frobenius expansion used only in Proposition 6.33.
-/

/-- Theorem 6.9: for every natural number `k`, the Hessian quadratic form of the Chapter 6
trace-power owner `π_k(X) = Trace (X^k)` at a symmetric matrix `X` in the symmetric direction `H`
is bounded above by `k(k - 1)` times the pairing of the eigenvalues of `(CFC.abs X)^(k - 2)` and
the squared eigenvalues of `CFC.abs H`. -/
theorem powerTrace_iteratedFDeriv_two_le_absEigenvaluePairing
    (k : ℕ) (X H : SymmMat) :
    iteratedFDeriv ℝ 2 (π[k] : SymmMat → ℝ) X ![H, H] ≤
      (((k * (k - 1) : ℕ) : ℝ) *
        ∑ i : Fin n,
          (((Matrix.nonneg_iff_posSemidef.mp
              (CFC.abs_nonneg ((X : Matrix (Fin n) (Fin n) ℝ)))).isHermitian.eigenvalues i) ^
            (k - 2)) *
            (((Matrix.nonneg_iff_posSemidef.mp
                (CFC.abs_nonneg ((H : Matrix (Fin n) (Fin n) ℝ)))).isHermitian.eigenvalues i) ^
              (2 : ℕ))) := sorry
