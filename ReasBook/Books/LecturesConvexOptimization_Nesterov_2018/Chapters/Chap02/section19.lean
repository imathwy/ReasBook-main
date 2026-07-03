import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_19 (from Chap02) -/
open scoped ConstrainedArgmin SmoothConvex

noncomputable section

universe u

/- Primary domain: smooth convex unconstrained minimization on finite-dimensional real
inner-product spaces.

Owner-style declarations sampled for this item:
* `IsMinOn f Set.univ xStar` in `Definition_2_1`, the Chapter 2 source-facing owner of the
  unconstrained minimizer part of `min_x f(x)`;
* `f ∈ 𝓕[L, normSeminorm ℝ E]¹¹` in `Theorem_2_5`, the objective-side owner for the whole-space
  smooth-convex class on the intrinsic ambient space `E`;
* `ConvexC1SeminormSmooth.gradient_lipschitz`, the derived norm-gradient-Lipschitz view of that
  owner predicate;
* `SetConstrainedMinimizationProblem.unconstrained` in `Chap01/Definition_1_3_3`, the Chapter 1
  owner for the associated whole-space minimization problem.

Best owner abstraction:
* source-facing core:
  `f ∈ 𝓕[L, normSeminorm ℝ E]¹¹` together with `IsMinOn f Set.univ xStar`;
* bridge/view:
  the associated Chapter 1 owner
  `SetConstrainedMinimizationProblem.unconstrained f`.

Primitive data:
* the objective `f : E → ℝ`;
* the owner smooth-convex hypothesis on `f`;
* a minimizing point `xStar : E` with `IsMinOn f Set.univ xStar`.

Derived API:
* convexity, whole-space `C¹` regularity, and norm-gradient Lipschitz continuity of `f`;
* the associated whole-space constrained-owner package
  `SetConstrainedMinimizationProblem.unconstrained f`;
* the Chapter 1 optimal-value and approximate-minimizer API for that package.

Source/core/bridge triage:
* source-facing: a smooth convex objective on `E` together with the unconstrained minimization
  problem `min_x f(x)` and a global minimizer `xStar`;
* core/canonical: `f ∈ 𝓕[L, normSeminorm ℝ E]¹¹` and `IsMinOn f Set.univ xStar`;
* bridge/view: the packaged owner problem on `Set.univ` and its `optimalValue` API.

Definition 2.19 is therefore recorded by reusing the Chapter 2 minimizer API from
`Definition_2_1` and the objective-side owner predicate from `Theorem_2_5`, without a parallel
local smooth-problem wrapper. The Chapter 1 packaged problem is kept only as a bridge for
downstream optimal-value language. The textbook `ℝⁿ` statement is the specialization
`E = EuclideanSpace ℝ (Fin n)`. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local notation "p" => normSeminorm ℝ E

variable (L : NNReal) (f : E → ℝ)
variable (xStar : E)

recall ConvexC1SeminormSmooth
recall ConvexC1SeminormSmooth.gradient_lipschitz
recall SetConstrainedMinimizationProblem.unconstrained
recall SetConstrainedMinimizationProblem.optimalValue

set_option linter.hashCommand false

/-
Definition 2.19: given a smooth convex objective `f ∈ 𝓕[L, p]¹¹`, the unconstrained
minimization problem `min_{x ∈ E} f(x)` is the Chapter 1 whole-space owner
`SetConstrainedMinimizationProblem.unconstrained f`.
-/
#check
  (SetConstrainedMinimizationProblem.unconstrained f : SetConstrainedMinimizationProblem E)

#check f ∈ 𝓕[L, p]¹¹

#check IsMinOn f Set.univ xStar

#check
  (show IsMinOn f Set.univ xStar ↔ ∀ x : E, f xStar ≤ f x from
    isMinOn_univ_iff)

#check ((SetConstrainedMinimizationProblem.unconstrained f).optimalValue : EReal)

/-! ### Lemma_2_19 (from Chap02) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E]

/- Primary domain: parameter comparison for exact values of quadratically regularized local models
on a feasible set in a real inner-product space.

Owner declarations sampled before refining:
* `quadraticallyRegularizedObjective` in `FirstOrderTaylorModel.lean`, which owns the regularized
  local model `x ↦ f(xBar; x) + (γ / 2) ‖x - xBar‖²`;
* `quadraticallyRegularizedObjective_apply`, the owner pointwise evaluation formula;
* `SetConstrainedMinimizationProblem.optimalValue` in `Definition_1_3_7`, the Chapter 1 owner for
  exact constrained values;
* `SetConstrainedMinimizationProblem.optimalValue_eq_of_isMinOn`, the attained-value bridge for
  that owner.

Best owner abstraction:
* the constrained problem
  `SetConstrainedMinimizationProblem.mk Q
    (quadraticallyRegularizedObjective (f xBar) γ xBar)`;
* source-facing exact values as the real view `modelValue γ` of that owner optimal value.

Source/core/bridge triage:
* source-facing: the lower quadratic model inequality for the triple `(x_f, g_f, f^*)`;
* core/canonical: the owner exact values above, built from the Chapter 1 constrained-minimization
  owner applied to `quadraticallyRegularizedObjective`;
* bridge/view: the theorem below, which converts the source lower-model inequality at `γ₁`
  into the canonical exact-value comparison between `γ₁` and `γ₂`.

Primitive data:
* the feasible set `Q`;
* the local model family `f : E → E → ℝ`;
* the base point `xBar`;
* the parameters `γ₁`, `γ₂`;
* the source-facing reduced-gradient vector `g₁`.

Derived API:
* the exact local values at `γ₁` and `γ₂` through the local source-facing notation `modelValue`,
  defined as the real view of the owner constrained optimal values.

The previous file-level theorem was keyed to a chosen minimizer at `γ₂`. That moved the public
API away from Lemma 2.19's source-facing lower-model hypothesis. This refinement restores the
source mathematics while keeping the exact-value terms as a bridge from the Chapter 1 constrained
minimization owner, and it removes the unnecessary coordinate model `EuclideanSpace ℝ (Fin n)`
from the public API because the statement uses only the real inner-product-space structure. -/

section

variable (Q : Set E) (f : E → E → ℝ) (xBar : E)

local notation "modelOptimalValue" => fun γ : ℝ ↦
  SetConstrainedMinimizationProblem.optimalValue
    ((SetConstrainedMinimizationProblem.mk Q
      (quadraticallyRegularizedObjective (f xBar) γ xBar)) :
        SetConstrainedMinimizationProblem E)
local notation "modelValue" => fun γ : ℝ ↦ EReal.toReal (modelOptimalValue γ)

/-- Any exact minimizer of the quadratically regularized local model realizes the real view of the
Chapter 1 owner exact value `modelValue γ` for that regularized local problem. -/
theorem regularizedModelOptimalValue_toReal_eq_of_isMinOn
    (x : E) (γ : ℝ)
    (hx : x ∈ Q)
    (hmin : IsMinOn (quadraticallyRegularizedObjective (f xBar) γ xBar) Q x) :
    modelValue γ = quadraticallyRegularizedObjective (f xBar) γ xBar x := by
  let problem : SetConstrainedMinimizationProblem E :=
    .mk Q (quadraticallyRegularizedObjective (f xBar) γ xBar)
  have hopt :
      problem.optimalValue =
        (quadraticallyRegularizedObjective (f xBar) γ xBar x : EReal) :=
    problem.optimalValue_eq_of_isMinOn hx hmin
  change EReal.toReal problem.optimalValue =
    quadraticallyRegularizedObjective (f xBar) γ xBar x
  simpa using congrArg EReal.toReal hopt

variable [InnerProductSpace ℝ E]

/-- Helper for Lemma 2.19: completing the square isolates the `γ₂`-quadratic term and the
comparison constant contributed by `g₁`. -/
lemma lower_affine_quadratic_eq_completed_square
    (value₁ γ₁ γ₂ : ℝ) (g₁ xBar x : E)
    (hγ₁ : γ₁ ≠ 0) (hγ₂ : γ₂ ≠ 0) :
    value₁ +
        inner ℝ g₁ (x - xBar) +
        (1 / (2 * γ₁)) * ‖g₁‖ ^ (2 : ℕ) +
        (γ₂ / 2) * ‖x - xBar‖ ^ (2 : ℕ) =
      value₁ +
        (γ₂ / 2) * ‖x - (xBar - γ₂⁻¹ • g₁)‖ ^ (2 : ℕ) +
        ((γ₂ - γ₁) / (2 * γ₁ * γ₂)) * ‖g₁‖ ^ (2 : ℕ) := by
  -- Complete the square around the shifted center `xBar - γ₂⁻¹ • g₁`.
  have hsub :
      x - (xBar - γ₂⁻¹ • g₁) = (x - xBar) + γ₂⁻¹ • g₁ := by
    abel_nf
  have hsq :
      (γ₂ / 2 : ℝ) * ‖x - (xBar - γ₂⁻¹ • g₁)‖ ^ (2 : ℕ) =
        (γ₂ / 2 : ℝ) * ‖x - xBar‖ ^ (2 : ℕ) +
          inner ℝ g₁ (x - xBar) +
          (1 / (2 * γ₂)) * ‖g₁‖ ^ (2 : ℕ) := by
    calc
      (γ₂ / 2 : ℝ) * ‖x - (xBar - γ₂⁻¹ • g₁)‖ ^ (2 : ℕ)
          = (γ₂ / 2 : ℝ) *
              inner ℝ (x - (xBar - γ₂⁻¹ • g₁)) (x - (xBar - γ₂⁻¹ • g₁)) := by
                rw [real_inner_self_eq_norm_sq]
      _ = (γ₂ / 2 : ℝ) *
            inner ℝ ((x - xBar) + γ₂⁻¹ • g₁) ((x - xBar) + γ₂⁻¹ • g₁) := by
              rw [hsub]
      _ = (γ₂ / 2 : ℝ) *
            (inner ℝ (x - xBar) (x - xBar) +
              inner ℝ (x - xBar) (γ₂⁻¹ • g₁) +
              inner ℝ (γ₂⁻¹ • g₁) (x - xBar) +
              inner ℝ (γ₂⁻¹ • g₁) (γ₂⁻¹ • g₁)) := by
                rw [inner_add_add_self]
      _ = (γ₂ / 2 : ℝ) * ‖x - xBar‖ ^ (2 : ℕ) +
            inner ℝ g₁ (x - xBar) +
            (1 / (2 * γ₂)) * ‖g₁‖ ^ (2 : ℕ) := by
              rw [real_inner_self_eq_norm_sq, inner_smul_right, real_inner_smul_left,
                real_inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq]
              have hcomm : inner ℝ (x - xBar) g₁ = inner ℝ g₁ (x - xBar) := by
                simpa using (real_inner_comm (x - xBar) g₁).symm
              rw [hcomm]
              field_simp [hγ₂]
              ring
  have hcoeff :
      (1 / (2 * γ₁) : ℝ) - 1 / (2 * γ₂) = (γ₂ - γ₁) / (2 * γ₁ * γ₂) := by
    field_simp [hγ₁, hγ₂]
  calc
    value₁ +
        inner ℝ g₁ (x - xBar) +
        (1 / (2 * γ₁)) * ‖g₁‖ ^ (2 : ℕ) +
        (γ₂ / 2) * ‖x - xBar‖ ^ (2 : ℕ)
      =
        value₁ +
          ((γ₂ / 2 : ℝ) * ‖x - xBar‖ ^ (2 : ℕ) +
            inner ℝ g₁ (x - xBar) +
            (1 / (2 * γ₂)) * ‖g₁‖ ^ (2 : ℕ)) +
          (((1 / (2 * γ₁) : ℝ) - 1 / (2 * γ₂)) * ‖g₁‖ ^ (2 : ℕ)) := by
            ring
    _ = value₁ +
          (γ₂ / 2) * ‖x - (xBar - γ₂⁻¹ • g₁)‖ ^ (2 : ℕ) +
          (((1 / (2 * γ₁) : ℝ) - 1 / (2 * γ₂)) * ‖g₁‖ ^ (2 : ℕ)) := by
            rw [← hsq]
    _ = value₁ +
          (γ₂ / 2) * ‖x - (xBar - γ₂⁻¹ • g₁)‖ ^ (2 : ℕ) +
          ((γ₂ - γ₁) / (2 * γ₁ * γ₂)) * ‖g₁‖ ^ (2 : ℕ) := by
            rw [hcoeff]

/-- Helper for Lemma 2.19: the source lower model at `γ₁` yields a pointwise lower bound for the
`γ₂`-regularized objective by a constant independent of `x`. -/
lemma regularized_objective_ge_comparison_constant
    (γ₁ γ₂ : ℝ) (g₁ : E) (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂)
    (hlower :
      ∀ x ∈ Q,
        f xBar x ≥
          modelValue γ₁ +
            inner ℝ g₁ (x - xBar) +
              (1 / (2 * γ₁)) * ‖g₁‖ ^ (2 : ℕ)) :
    ∀ x ∈ Q,
      modelValue γ₁ +
        ((γ₂ - γ₁) / (2 * γ₁ * γ₂)) * ‖g₁‖ ^ (2 : ℕ) ≤
      quadraticallyRegularizedObjective (f xBar) γ₂ xBar x := by
  intro x hx
  -- Add the `γ₂`-penalty to the source lower bound.
  have hregularized :
      modelValue γ₁ +
          inner ℝ g₁ (x - xBar) +
          (1 / (2 * γ₁)) * ‖g₁‖ ^ (2 : ℕ) +
          (γ₂ / 2) * ‖x - xBar‖ ^ (2 : ℕ) ≤
        quadraticallyRegularizedObjective (f xBar) γ₂ xBar x := by
    simpa [quadraticallyRegularizedObjective_apply, add_assoc, add_left_comm, add_comm] using
      add_le_add_right (hlower x hx) ((γ₂ / 2) * ‖x - xBar‖ ^ (2 : ℕ))
  -- Complete the square so the only extra term is nonnegative.
  rw [lower_affine_quadratic_eq_completed_square (value₁ := modelValue γ₁)
      (γ₁ := γ₁) (γ₂ := γ₂) (g₁ := g₁) (xBar := xBar) (x := x) hγ₁.ne' hγ₂.ne'] at hregularized
  have hnonneg :
      0 ≤ (γ₂ / 2) * ‖x - (xBar - γ₂⁻¹ • g₁)‖ ^ (2 : ℕ) := by
    positivity
  have hconst_le :
      modelValue γ₁ +
          ((γ₂ - γ₁) / (2 * γ₁ * γ₂)) * ‖g₁‖ ^ (2 : ℕ) ≤
        modelValue γ₁ +
          (γ₂ / 2) * ‖x - (xBar - γ₂⁻¹ • g₁)‖ ^ (2 : ℕ) +
          ((γ₂ - γ₁) / (2 * γ₁ * γ₂)) * ‖g₁‖ ^ (2 : ℕ) := by
    linarith
  exact hconst_le.trans hregularized

/-- Helper for Lemma 2.19: the comparison constant is bounded above by the owner optimal value of
the `γ₂`-regularized problem. -/
lemma comparison_constant_le_modelOptimalValue
    (hQ : Q.Nonempty) (γ₁ γ₂ : ℝ) (g₁ : E) (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂)
    (hlower :
      ∀ x ∈ Q,
        f xBar x ≥
          modelValue γ₁ +
            inner ℝ g₁ (x - xBar) +
              (1 / (2 * γ₁)) * ‖g₁‖ ^ (2 : ℕ)) :
    (((modelValue γ₁ +
        ((γ₂ - γ₁) / (2 * γ₁ * γ₂)) * ‖g₁‖ ^ (2 : ℕ)) : ℝ) : EReal) ≤
      modelOptimalValue γ₂ := by
  let comparisonValue : ℝ :=
    modelValue γ₁ + ((γ₂ - γ₁) / (2 * γ₁ * γ₂)) * ‖g₁‖ ^ (2 : ℕ)
  let comparisonProblem : SetConstrainedMinimizationProblem E :=
    .mk Q (fun _ : E ↦ comparisonValue)
  let regularizedProblem : SetConstrainedMinimizationProblem E :=
    .mk Q (quadraticallyRegularizedObjective (f xBar) γ₂ xBar)
  -- Compare the constant problem with the actual regularized problem on the shared feasible set.
  have hpointwise :
      ∀ x ∈ comparisonProblem.feasibleSet, comparisonProblem x ≤ regularizedProblem x := by
    intro x hx
    simpa [comparisonProblem, regularizedProblem, comparisonValue] using
      regularized_objective_ge_comparison_constant
        (Q := Q) (f := f) (xBar := xBar) γ₁ γ₂ g₁ hγ₁ hγ₂ hlower x hx
  have hopt_le :
      comparisonProblem.optimalValue ≤ regularizedProblem.optimalValue := by
    exact SetConstrainedMinimizationProblem.optimalValue_le_optimalValue_of_forall_le
      comparisonProblem regularizedProblem rfl hpointwise
  rcases hQ with ⟨xQ, hxQ⟩
  -- The constant problem attains its optimal value at any feasible point.
  have hcomparison_eq : comparisonProblem.optimalValue = (comparisonValue : EReal) := by
    simpa [comparisonProblem] using
      comparisonProblem.optimalValue_eq_of_isMinOn hxQ (isMinOn_const : IsMinOn _ Q xQ)
  rw [hcomparison_eq] at hopt_le
  change (comparisonValue : EReal) ≤ modelOptimalValue γ₂ at hopt_le
  simpa [regularizedProblem, comparisonValue] using hopt_le

/-- Lemma 2.19: if the source-facing lower quadratic model inequality holds at `xBar` with
parameter `γ₁ > 0` and reduced-gradient vector `g₁`, then the exact regularized model values
satisfy
`f^*(xBar; γ₂) ≥ f^*(xBar; γ₁) + ((γ₂ - γ₁) / (2 γ₁ γ₂)) ‖g₁‖²`
for every `γ₂ > 0`. Here the textbook value `f^*(xBar; γ)` is recorded by the local notation
`modelValue γ`, i.e. the real view of the Chapter 1 owner exact value of the constrained problem
with feasible set `Q` and objective
`quadraticallyRegularizedObjective (f xBar) γ xBar`. -/
-- Proof sketch: add the `γ₂`-regularization term to the assumed lower model inequality at `γ₁`.
-- The right-hand side becomes the owner exact value `modelValue γ₁` plus an
-- affine-quadratic
-- function of `x - xBar`
-- with linear part `g₁` and curvature `γ₂ / 2`; complete the square to identify its minimum as
-- `((γ₂ - γ₁) / (2 * γ₁ * γ₂)) * ‖g₁‖²` above that owner exact value. Taking the infimum over
-- the nonempty feasible set `Q` of the left-hand side gives the corresponding owner exact value
-- `modelValue γ₂`.
theorem exactValue_ge_of_lowerQuadraticModel
    (hQ : Q.Nonempty) (γ₁ γ₂ : ℝ) (g₁ : E) (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂)
    (hlower :
      ∀ x ∈ Q,
        f xBar x ≥
          modelValue γ₁ +
            inner ℝ g₁ (x - xBar) +
              (1 / (2 * γ₁)) * ‖g₁‖ ^ (2 : ℕ)) :
    modelValue γ₂ ≥
      modelValue γ₁ +
        ((γ₂ - γ₁) / (2 * γ₁ * γ₂)) * ‖g₁‖ ^ (2 : ℕ) := by
  let comparisonValue : ℝ :=
    modelValue γ₁ + ((γ₂ - γ₁) / (2 * γ₁ * γ₂)) * ‖g₁‖ ^ (2 : ℕ)
  -- Compare the owner optimal value with the constant lower bound produced by the source model.
  have hcomparison :
      ((comparisonValue : ℝ) : EReal) ≤
        modelOptimalValue γ₂ := by
    simpa [comparisonValue] using comparison_constant_le_modelOptimalValue
      (Q := Q) (f := f) (xBar := xBar) hQ γ₁ γ₂ g₁ hγ₁ hγ₂ hlower
  rcases hQ with ⟨xQ, hxQ⟩
  -- Any feasible point shows that the owner optimal value is not `⊤`.
  have hmodel_ne_top : modelOptimalValue γ₂ ≠ ⊤ := by
    exact ne_top_of_le_ne_top
      (EReal.coe_ne_top (quadraticallyRegularizedObjective (f xBar) γ₂ xBar xQ))
      (((SetConstrainedMinimizationProblem.mk Q
          (quadraticallyRegularizedObjective (f xBar) γ₂ xBar)) :
            SetConstrainedMinimizationProblem E).optimalValue_le_of_mem_feasibleSet hxQ)
  -- Convert the owner `EReal` inequality back to the source-facing real exact values.
  have htoReal :
      comparisonValue ≤
        modelValue γ₂ := by
    have htoReal' :=
      EReal.toReal_le_toReal hcomparison (EReal.coe_ne_bot _) hmodel_ne_top
    change comparisonValue ≤ EReal.toReal (modelOptimalValue γ₂) at htoReal'
    simpa using htoReal'
  simpa [comparisonValue] using htoReal

end

/-! ### Proposition_2_19 (from Chap02) -/
noncomputable section

universe u v

open scoped PrimalEqualityConstrainedProblem.LagrangianMinimizerSelectionNotation

/- Primary domain: equality-constrained Lagrangian duality with a chosen minimizing primal
selection.

Owner declarations sampled before refining this file:
* `PrimalEqualityConstrainedProblem.lagrangian`, `lagrangianMinimizers`, and
  `constraintResidual` in `LecturesConvexOptimization_Nesterov_2018/Chap02/Definition_2_30.lean`;
* `PrimalEqualityConstrainedProblem.LagrangianMinimizerSelection.isMinOn` in
  `LecturesConvexOptimization_Nesterov_2018/Chap02/Definition_2_31.lean`, the owner theorem expressing that a chosen section
  minimizes each fixed-multiplier Lagrangian subproblem;
* `PrimalEqualityConstrainedProblem.LagrangianMinimizerSelection.
  selectedDualProfile_eq_objective_add_inner_dualResidual` in
  `LecturesConvexOptimization_Nesterov_2018/Chap02/Definition_2_31.lean`, the canonical expansion of the selected profile.

Best owner abstraction: the equality problem's own Lagrangian layer, with
`selection : LagrangianMinimizerSelection problem` as the source-facing auxiliary choice data.

Primitive data:
* `problem`, `selection`, and the multipliers `u₁`, `u₂`.

Derived API:
* `selection.isMinOn u`;
* `selection.dualResidual`;
* `selection.selectedDualProfile_eq_objective_add_inner_dualResidual`.

Source/core/bridge triage:
* source-facing: Proposition 2.19 as the affine support inequality for the selected dual profile
  `u ↦ 𝓛(x(u), u)`;
* core/canonical: the equality-problem minimizing-section owner `selection.isMinOn`;
* bridge/view: rewriting the comparison bound through
  `selectedDualProfile_eq_objective_add_inner_dualResidual`.

No parallel local dual-function wrapper is kept here; this file stays as a thin source-facing
bridge to the equality-problem minimizing-section API. -/

namespace PrimalEqualityConstrainedProblem
namespace LagrangianMinimizerSelection

variable {E : Type u} {Λ : Type v} [AddCommMonoid E] [Module ℝ E]
variable [NormedAddCommGroup Λ] [InnerProductSpace ℝ Λ]
variable {problem : PrimalEqualityConstrainedProblem E Λ}

variable (selection : LagrangianMinimizerSelection problem)

local notation "φ" => φ[selection]
local notation "g" => g[selection]

/-- Proposition 2.19: for a chosen minimizer `x(u) ∈ argmin_x 𝓛(x, u)` of each equality-
constrained Lagrangian subproblem, the selected dual profile `u ↦ 𝓛(x(u), u)` satisfies the
affine support inequality `φ(u₁) ≤ φ(u₂) + ⟪u₁ - u₂, g(u₂)⟫`, where `g(u) = b - A x(u)`. -/
-- Proof sketch: evaluate the owner theorem `selection.isMinOn u₁` at the feasible comparison
-- point `selection u₂`, then expand the resulting `u₁`-Lagrangian value into the selected
-- profile at `u₂` plus the affine residual term.
theorem selectedDualProfile_le_affine_support
    (u₁ u₂ : Λ) :
    φ u₁ ≤ φ u₂ + inner ℝ (u₁ - u₂) (g u₂) := by
  have hu₂_mem : (selection u₂ : E) ∈ problem.feasibleSet :=
    (problem.mem_lagrangianMinimizers_iff.mp (selection u₂).2).1
  have hmin := selection.isMinOn u₁
  rw [isMinOn_iff] at hmin
  have hcompare :
      φ u₁ ≤ problem.lagrangian (selection u₂) u₁ := by
    simpa [selectedDualProfile] using hmin (selection u₂) hu₂_mem
  calc
    φ u₁ ≤ problem.lagrangian (selection u₂) u₁ := hcompare
    _ = problem (selection u₂) + inner ℝ u₁ (g u₂) := rfl
    _ = problem (selection u₂) + (inner ℝ u₂ (g u₂) + inner ℝ (u₁ - u₂) (g u₂)) := by
          congr 1
          calc
            inner ℝ u₁ (g u₂) = inner ℝ (u₂ + (u₁ - u₂)) (g u₂) := by
                    congr 1
                    abel
            _ = inner ℝ u₂ (g u₂) + inner ℝ (u₁ - u₂) (g u₂) := by
                    rw [inner_add_left]
    _ = (problem (selection u₂) + inner ℝ u₂ (g u₂)) + inner ℝ (u₁ - u₂) (g u₂) := by
          abel
    _ = φ u₂ + inner ℝ (u₁ - u₂) (g u₂) := by
          rw [← selection.selectedDualProfile_eq_objective_add_inner_dualResidual u₂]

end LagrangianMinimizerSelection
end PrimalEqualityConstrainedProblem

/-! ### Theorem_2_19 (from Chap02) -/
open AffineMap

universe u

/- Primary domain: estimating-sequence gap bounds with a quadratically regularized initial model.

Sampled declarations in this domain:
* `estimatingSequence_gap_mem_Icc`
* `quadraticallyRegularizedObjective`
* `quadraticallyRegularizedObjective_apply`
* `IsEstimatingSequence.gap_mem_Icc`

Best owner abstraction for this file:
* source-facing: the recursive scalar sequence `estimatingWeight α`;
* core/canonical: the stagewise gap-control theorem `estimatingSequence_gap_mem_Icc` together with
  the initial quadratic owner `quadraticallyRegularizedObjective`;
* bridge/view: the later packaged API `IsEstimatingSequence.gap_mem_Icc`, which adds the
  asymptotic hypothesis `λ_k → 0` and is therefore stronger than Theorem 2.19 needs, and the
  pointwise formula from `quadraticallyRegularizedObjective_apply`.

Primitive data kept here:
* the recursive weight family `estimatingWeight α`;
* the initial quadratic owner
  `φ 0 = quadraticallyRegularizedObjective (fun _ ↦ f (x 0)) γ0 (x 0)`;
* the canonical function-space affine upper bound `φ k ≤ lineMap f (φ 0) (estimatingWeight α k)`.

Derived API:
* the product formula for the recursive weight family;
* the textbook suboptimality estimate, kept as a thin specialization of the owner gap bound.

The algorithmic owner `OptimalMethodRecurrence.weight` is only a later specialization of the same
recursion to a method object, so it is not the public owner for this source-facing file. -/

/-- The recursively defined coefficients `λₖ` attached to the estimating-sequence recursion
`λ₀ = 1`, `λₖ₊₁ = (1 - αₖ) λₖ`. -/
def estimatingWeight (α : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => (1 - α k) * estimatingWeight α k

/-- The recursively defined estimating-sequence weights are the finite products
`∏_{i=0}^{k-1} (1 - αᵢ)`. -/
-- Proof sketch: argue by induction on `k`. The base case is `k = 0`, where both sides equal `1`.
-- For the step, unfold `estimatingWeight` at `k + 1` and rewrite the finite product
-- over `Finset.range (k + 1)` as the last factor `(1 - α k)` times the product over
-- `Finset.range k`.
theorem estimatingWeight_eq_prod
    (α : ℕ → ℝ) (k : ℕ) :
    estimatingWeight α k =
      Finset.prod (Finset.range k) (fun i ↦ (1 - α i)) := by
  induction k with
  | zero =>
      -- At stage `0`, both the recursive owner and the empty product equal `1`.
      simp [estimatingWeight]
  | succ k hk =>
      -- Extend the product by its last factor and match the recursive definition of `λₖ₊₁`.
      rw [estimatingWeight, Finset.prod_range_succ, hk]
      ring

section

variable {E : Type u} [NormedAddCommGroup E]

/-- Theorem 2.19: if `xₖ`, `φₖ`, and the recursively defined weights
`λ₀ = 1`, `λₖ₊₁ = (1 - αₖ) λₖ` satisfy the estimating-sequence upper-model hypotheses,
`φ₀ = quadraticallyRegularizedObjective (fun _ ↦ f(x₀)) γ₀ x₀`, equivalently
`φ₀(z) = f(x₀) + (γ₀ / 2) ‖z - x₀‖²`, and `xStar` is a minimizer of `f`, then
`f(xₖ) - f(xStar)` is bounded by `λₖ * (f(x₀) - f(xStar) + (γ₀ / 2) ‖x₀ - xStar‖²)`, where
`λₖ = ∏_{i=0}^{k-1} (1 - αᵢ)`. -/
-- Proof sketch: use `hφmin k` and `hfx k` to get
-- `f (x k) ≤ φStar k ≤ φ k xStar`. Apply the owner gap theorem
-- `estimatingSequence_gap_mem_Icc` with `λ_k = estimatingWeight α k`, use the function-space upper
-- bound `hφupper`, and then evaluate the owner initial quadratic model from `hφ0` at `xStar`
-- using `quadraticallyRegularizedObjective_apply`. Since `xStar` minimizes `f`, simplify the
-- resulting interval upper endpoint to the displayed bound. The product formula for `λₖ` is
-- provided by `estimatingWeight_eq_prod`.
theorem estimating_sequence_suboptimality_le
    (f : E → ℝ)
    (x : ℕ → E)
    (φ : ℕ → E → ℝ)
    (φStar : ℕ → ℝ)
    (α : ℕ → ℝ)
    (xStar : E)
    (hxStar : IsMinOn f Set.univ xStar)
    (γ0 : ℝ)
    (hfx : ∀ k : ℕ, f (x k) ≤ φStar k)
    (hφmin : ∀ k : ℕ, IsLeast (Set.range (φ k)) (φStar k))
    (hφupper : ∀ k : ℕ, φ k ≤ lineMap f (φ 0) (estimatingWeight α k))
    (hφ0 : φ 0 = quadraticallyRegularizedObjective (fun _ ↦ f (x 0)) γ0 (x 0))
    (k : ℕ) :
    f (x k) - f xStar ≤
      estimatingWeight α k *
        (f (x 0) - f xStar + (γ0 / 2) * ‖x 0 - xStar‖ ^ (2 : ℕ)) := by
  -- Reuse Lemma 2.7 to control the stagewise gap by the initial-model gap at `xStar`.
  have hgap :
      f (x k) - f xStar ∈
        Set.Icc 0 (estimatingWeight α k * (φ 0 xStar - f xStar)) := by
    exact estimatingSequence_gap_mem_Icc xStar φStar x hxStar hφupper hφmin hfx k
  -- Rewrite the initial-model gap using the explicit quadratic formula for `φ₀`.
  have hInitial :
      φ 0 xStar - f xStar =
        f (x 0) - f xStar + (γ0 / 2) * ‖x 0 - xStar‖ ^ (2 : ℕ) := by
    have hφ0_at_xStar :
        φ 0 xStar =
          quadraticallyRegularizedObjective (fun _ ↦ f (x 0)) γ0 (x 0) xStar := by
      exact congrFun hφ0 xStar
    calc
      φ 0 xStar - f xStar
          = quadraticallyRegularizedObjective (fun _ ↦ f (x 0)) γ0 (x 0) xStar - f xStar := by
              rw [hφ0_at_xStar]
      _ = (f (x 0) + (γ0 / 2) * ‖xStar - x 0‖ ^ (2 : ℕ)) - f xStar := by
              rw [quadraticallyRegularizedObjective_apply]
      _ = f (x 0) - f xStar + (γ0 / 2) * ‖xStar - x 0‖ ^ (2 : ℕ) := by
              ring
      _ = f (x 0) - f xStar + (γ0 / 2) * ‖x 0 - xStar‖ ^ (2 : ℕ) := by
              rw [norm_sub_rev]
  -- Extract the upper endpoint from the interval estimate and substitute the rewritten model gap.
  simpa [hInitial] using hgap.2

end
