import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Remark_2_22_1 (from Chap02) -/
/- Remark 2.22.1 is recall-only.

The primary domain here is the simple-set estimate-sequence lower bound built from the
projected-gradient owner API on a nonempty closed convex feasible set.

Owner declarations sampled for this refinement:
* `gradientMapping` and `reducedGradient` in `Definition_2_35_1`;
* `gradientMapping_objective_lower_bound` in `Theorem_2_36`;
* `simple_set_phi_star_lower_bound_intermediate` and
  `simple_set_phi_star_lower_bound_of_objective_lower_bound` in `Text_2_1`.

Best owner abstraction:
* the two theorem-level lower bounds in `Text_2_1`, derived from the canonical projected-gradient
  data and the canonical objective lower bound.

Primitive data: the feasible set `Q`, the objective `f`, the iterate data `(y_k, x_k, v_k)`, and
the scalar parameters `(L, α_k, γ_k, γ_{k+1}, φ_k^*, φ_{k+1}^*)`.

Derived API: the projected-gradient point `x_Q(y_k; L)`, the reduced gradient `g_Q(y_k; L)`, and
the two algebraic lower bounds already packaged in `Text_2_1`.

Source/core/bridge triage:
* source-facing: the remark's lower bound obtained after inserting `(2.2.57)` into the
  estimate-sequence update;
* core/canonical: `gradientMapping`, `reducedGradient`, and
  `gradientMapping_objective_lower_bound`;
* bridge/view: the two theorem-level combination steps in `Text_2_1`.

Accordingly, this file adds no parallel local theorem wrappers; downstream use should refer
directly to the owner declarations from `Text_2_1`. -/

recall simple_set_phi_star_lower_bound_intermediate
recall simple_set_phi_star_lower_bound_of_objective_lower_bound

/-! ### Definition_2_22 (from Chap02) -/
open scoped StrongConvexSmooth

/- This item lies in the smooth strongly convex minimization domain.

Sampled owner-style declarations in this domain:
* `IsStrongConvexSmoothObjective` in `Definition_2_17`, which owns the objective-side
  `μ`-strong-convexity and `L`-gradient-Lipschitz assumptions;
* `𝓢[μ, L]¹¹` and `q[μ, L]` in `Definition_2_17`, which give the chapter's source-facing class
  and reciprocal-condition-number notation;
* `IsStrongConvexSmoothObjective.mu_pos`, showing that positivity of `μ` is primitive data of
  that owner predicate;
* `IsStrongConvexSmoothObjective.mu_le_L`, showing on nontrivial ambient spaces that admissible
  owner parameters satisfy `μ ≤ L`, so the ratio `μ / L` is the canonical reciprocal
  condition-number scalar seen downstream;
* `ConstantStepSchemeIII` in `Proposition_2_12`, a downstream chapter consumer that takes the
  reciprocal condition number directly as the scalar input `μ / L`.

Best abstraction triage:
* source-facing: the strongly convex smooth class `𝓢[μ, L]¹¹` together with the reciprocal
  condition-number notation `q[μ, L]`;
* core/canonical: `IsStrongConvexSmoothObjective μ L f`;
* bridge/view: the definitional identification `q[μ, L] = μ / L`.

Primitive data:
* the strong-convexity parameter `μ`;
* the gradient-Lipschitz constant `L`;
* an objective `f` together with the owner hypothesis
  `IsStrongConvexSmoothObjective μ L f`.

Derived API:
* the reciprocal condition number `q_f = q[μ, L] = μ / L`.

Definition 2.22 therefore uses the chapter owner and its source-facing notation directly. It adds
no wrapper predicate and no packaged reciprocal-condition-number object beyond the notation
`q[μ, L]`. -/

section

variable (μ L : ℝ)

/- Definition 2.22: for a `μ`-strongly convex function with `L`-Lipschitz continuous gradient,
the textbook reciprocal condition number `q_f` is the chapter scalar `q[μ, L]`, namely the
reciprocal of `Q_f` and concretely the ratio `μ / L`. -/
#check (rfl : q[μ, L] = μ / L)

end

/-! ### Lemma_2_22 (from Chap02) -/
noncomputable section

universe u

namespace LagrangianProblem

variable {Q : Type u} {m : ℕ}

/- Primary domain: parameter-shift bounds for the auxiliary max-violation optimal-value function
of an inequality-constrained problem.

Owner declarations sampled before refining:
* `LagrangianProblem` in `Definition_1_10_2`, the owner carrying the primitive objective and
  constraint family on the ambient type `Q`;
* `LagrangianProblem.constrainedAuxiliaryObjective` in `Lemma_2_21`, the owner max-violation
  objective `x ↦ max {f₀(x) - t, f₁(x), …, fₘ(x)}`;
* `LagrangianProblem.constrainedAuxiliaryOptimalValue` in `Lemma_2_21`, the owner extended-real
  value function attached to that auxiliary objective;
* `SetConstrainedMinimizationProblem.optimalValue_le_optimalValue_of_forall_le` and
  `SetConstrainedMinimizationProblem.optimalValue_sub_le_optimalValue_of_forall_sub_le` in
  `Definition_1_3_7`, the canonical feasible-set infimum comparison theorems;
* `LagrangianProblem.constrainedAuxiliaryObjective_shift_le` and
  `LagrangianProblem.constrainedAuxiliaryObjective_sub_le_shift` in `Lemma_2_21`, the pointwise
  parameter-shift bounds for the auxiliary objective.

Best owner abstraction:
* the source-facing value `f^*(t)` is the owner value
  `problem.constrainedAuxiliaryOptimalValue t`.

Primitive data:
* the owner problem `problem : LagrangianProblem Q m`;
* the scalar parameters `t` and `Δ`.

Derived API:
* the owner pointwise shift comparisons
  `problem.constrainedAuxiliaryObjective_shift_le hΔ x` and
  `problem.constrainedAuxiliaryObjective_sub_le_shift hΔ x`;
* the source-facing owner value comparison
  `problem.constrainedAuxiliaryOptimalValue_shift_bounds hΔ`.

Source/core/bridge triage:
* source-facing: Lemma 2.22's inequality between the owner values `f^*(t)` and
  `f^*(t + Δ)`;
* core/canonical: `problem.constrainedAuxiliaryOptimalValue t`;
* bridge/view: the pointwise bounds on
  `problem.constrainedAuxiliaryObjective (t + Δ)` and
  `problem.constrainedAuxiliaryObjective t`, which pass to the owner infima through the Chapter 1
  comparison theorems for `SetConstrainedMinimizationProblem.optimalValue`.

Lemma 2.22 therefore records the shift comparison directly at the owner value-function layer and
reuses the Chapter 1 optimal-value owner API instead of reproving the underlying `sInf`
monotonicity locally.
-/

/-- Lemma 2.22: increasing the parameter by `Δ ≥ 0` lowers the owner auxiliary optimal value by
at most `Δ` and never increases it. For the source value notation `f^*(t)` attached to
`x ↦ max {f₀(x) - t, f₁(x), …, fₘ(x)}`, one has
`f^*(t) - Δ ≤ f^*(t + Δ) ≤ f^*(t)` at the canonical
`problem.constrainedAuxiliaryOptimalValue` level. -/
-- Proof sketch: view the two auxiliary objectives as unconstrained
-- `SetConstrainedMinimizationProblem`s on the fixed feasible set `Set.univ`. Then apply the
-- Chapter 1 comparison theorems for `optimalValue` to the pointwise bounds from `Lemma_2_21`.
theorem constrainedAuxiliaryOptimalValue_shift_bounds
    (problem : LagrangianProblem Q m) {t Δ : ℝ} (hΔ : 0 ≤ Δ) :
    problem.constrainedAuxiliaryOptimalValue t - Δ ≤
        problem.constrainedAuxiliaryOptimalValue (t + Δ) ∧
      problem.constrainedAuxiliaryOptimalValue (t + Δ) ≤
        problem.constrainedAuxiliaryOptimalValue t := by
  constructor
  · simpa [constrainedAuxiliaryOptimalValue] using
      (SetConstrainedMinimizationProblem.optimalValue_sub_le_optimalValue_of_forall_sub_le
        (SetConstrainedMinimizationProblem.unconstrained
          (problem.constrainedAuxiliaryObjective t))
        (SetConstrainedMinimizationProblem.unconstrained
          (problem.constrainedAuxiliaryObjective (t + Δ)))
        rfl
        (fun x _ ↦ problem.constrainedAuxiliaryObjective_sub_le_shift hΔ x))
  · simpa [constrainedAuxiliaryOptimalValue] using
      (SetConstrainedMinimizationProblem.optimalValue_le_optimalValue_of_forall_le
        (SetConstrainedMinimizationProblem.unconstrained
          (problem.constrainedAuxiliaryObjective (t + Δ)))
        (SetConstrainedMinimizationProblem.unconstrained
          (problem.constrainedAuxiliaryObjective t))
        rfl
        (fun x _ ↦ problem.constrainedAuxiliaryObjective_shift_le hΔ x))

end LagrangianProblem

/-! ### Proposition_2_22 (from Chap02) -/
open AffineMap
open scoped Gradient ProjectedGradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain: simple-set estimating-sequence recurrences for projected-gradient lower models.

Sampled owner declarations in this domain:
* `gradientMapping` and `reducedGradient` from `Definition_2_35_1`, which own the projected-step
  point and reduced gradient;
* `quadraticallyRegularizedObjective` from `Definition_1_4_17.lean`, which owns the centered
  quadratic regularization added to each lower model;
* `lineMap` from `AffineMap`, which owns the affine-combination update of one stage from the
  previous stage and the new lower model;
* `estimatingSequenceCurvature` and `estimatingSequenceCenter` from `Lemma_2_9`, which already
  own the universal curvature and Euclidean center recurrences for this centered-quadratic
  pattern;
* `centered_quadratic_expand_about_point` from `Lemma_2_9`, the chapter owner for the algebraic
  recentering identity used when completing the square.

Best owner abstraction:
* source-facing: `simpleSetEstimatingModel`, `simpleSetEstimatingFunction`,
  `simpleSetEstimatingCenter`, and `simpleSetEstimatingValue`;
* core/canonical: `gradientMapping`, `reducedGradient`, `quadraticallyRegularizedObjective`,
  `lineMap`, and `estimatingSequenceCurvature`;
* bridge/view: the model evaluation formula, the zero/successor equations, and the canonical
  quadratic identity.

Primitive data:
* the feasible set `Q` with its nonempty / closed / convex structure;
* the projected-gradient stage data derived from `gradientMapping` and `reducedGradient`;
* the source-facing recursive objects `simpleSetEstimatingFunction`,
  `simpleSetEstimatingCenter`, and `simpleSetEstimatingValue`.

Derived API:
* the displayed formula for the stagewise lower model;
* function-level zero/successor equations for the recursive functions;
* the source-domain hypothesis that each successor curvature `γ_{k+1}` is nonzero, used only in
  the cancellation lemmas and canonical quadratic theorem;
* the canonical quadratic identity of Proposition 2.22.

Accordingly, this file keeps the source-facing simple-set objects, but reuses the owner
curvature recurrence from `Lemma_2_9` and the owner affine/quadratic combinators instead of
duplicating them as parallel local formulas. -/

section

variable
    (Q : Set E) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (f : E → ℝ) (x0 : E)
    (μ : ℝ) (L : NNRealˣ) (gamma0 : ℝ)
    (y : ℕ → E) (α : ℕ → ℝ)

local notation "xProj" =>
  fun k : ℕ ↦ x_Q[Q; hQ_nonempty; hQ_closed; hQ_convex | f; L](y k)

local notation "gProj" =>
  fun k : ℕ ↦ g_Q[Q; hQ_nonempty; hQ_closed; hQ_convex | f; L](y k)

local notation "gamma" => estimatingSequenceCurvature μ gamma0 α

/-- The lower quadratic model built directly from the projected-gradient point
`x_Q[Q; hQ_nonempty; hQ_closed; hQ_convex | f; L](y_k)` and reduced gradient
`g_Q[Q; hQ_nonempty; hQ_closed; hQ_convex | f; L](y_k)` at stage `k`. -/
def simpleSetEstimatingModel
    (k : ℕ) :
    E → ℝ :=
  let yk := y k
  let xQk := xProj k
  let gQk := gProj k
  quadraticallyRegularizedObjective
    (fun x ↦
      f xQk +
        (1 / (2 * L)) * ‖gQk‖ ^ (2 : ℕ) +
        inner ℝ gQk (x - yk))
    μ
    yk

/-- Evaluating the simple-set lower model recovers the displayed quadratic formula. -/
@[simp] theorem simpleSetEstimatingModel_apply
    (k : ℕ) (x : E) :
    simpleSetEstimatingModel Q hQ_nonempty hQ_closed hQ_convex f μ L y k x =
      let yk := y k
      let xQk := xProj k
      let gQk := gProj k
      f xQk +
        (1 / (2 * L)) * ‖gQk‖ ^ (2 : ℕ) +
        inner ℝ gQk (x - yk) +
        (μ / 2) * ‖x - yk‖ ^ (2 : ℕ) := rfl

/-- The recursively defined estimating-sequence functions for the simple-set method. -/
def simpleSetEstimatingFunction
    :
    ℕ → E → ℝ
  | 0 => quadraticallyRegularizedObjective (fun _ ↦ f x0) gamma0 x0
  | k + 1 =>
      lineMap
        (simpleSetEstimatingFunction k)
        (simpleSetEstimatingModel Q hQ_nonempty hQ_closed hQ_convex f μ L y k)
        (α k)

/-- The center sequence `v_k` in the canonical quadratic representation. The recurrence itself is
defined for every coefficient sequence; the later centered-quadratic proofs assume the successor
curvatures are nonzero when dividing by `γ_{k+1}`. -/
def simpleSetEstimatingCenter
    :
    ℕ → E
  | 0 => x0
  | k + 1 =>
      let gammaCurr := gamma k
      let gammaNext := gamma (k + 1)
      let yk := y k
      let gQk := gProj k
      (1 / gammaNext) •
        (((1 - α k) * gammaCurr) •
            simpleSetEstimatingCenter k +
          (α k * μ) • yk -
          α k • gQk)

/-- The scalar term `φ_k^*` in the canonical quadratic representation. The recurrence itself is
defined for every coefficient sequence; the later centered-quadratic proofs assume the successor
curvatures are nonzero when dividing by `γ_{k+1}`. -/
def simpleSetEstimatingValue
    :
    ℕ → ℝ
  | 0 => f x0
  | k + 1 =>
      let gammaNext := gamma (k + 1)
      let gammaCurr := gamma k
      let yk := y k
      let vCurr := simpleSetEstimatingCenter
        Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k
      let gCurr := gProj k
      let xQCurr := xProj k
      (1 - α k) * simpleSetEstimatingValue k +
        α k * f xQCurr +
        (α k / (2 * L) - α k ^ (2 : ℕ) / (2 * gammaNext)) * ‖gCurr‖ ^ (2 : ℕ) +
        (α k * (1 - α k) * gammaCurr / gammaNext) *
          ((μ / 2) * ‖yk - vCurr‖ ^ (2 : ℕ) + inner ℝ gCurr (vCurr - yk))

local notation "phi" =>
  simpleSetEstimatingFunction Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α

/-- The estimating-sequence functions start from the initial quadratic model at `x0`. -/
-- Proof sketch: unfold `simpleSetEstimatingFunction` at index `0`.
@[simp] theorem simpleSetEstimatingFunction_zero
    :
    phi 0 =
      quadraticallyRegularizedObjective (fun _ ↦ f x0) gamma0 x0 := rfl

/-- Evaluating the initial simple-set estimating function recovers the displayed quadratic
formula. -/
@[simp] theorem simpleSetEstimatingFunction_zero_apply
    (x : E) :
    phi 0 x =
      f x0 + (gamma0 / 2) * ‖x - x0‖ ^ (2 : ℕ) := rfl

/-- The estimating-sequence functions satisfy their defining affine update with the simple-set
lower model. -/
-- Proof sketch: unfold `simpleSetEstimatingFunction` at index `k + 1`.
theorem simpleSetEstimatingFunction_succ
    (k : ℕ) :
    phi (k + 1) =
      lineMap
        (phi k)
        (simpleSetEstimatingModel Q hQ_nonempty hQ_closed hQ_convex f μ L y k)
        (α k) := rfl

/-- Evaluating the successor stage recovers the textbook affine update formula. -/
@[simp] theorem simpleSetEstimatingFunction_succ_apply
    (k : ℕ) (x : E) :
    phi (k + 1) x =
      (1 - α k) * phi k x +
        α k * simpleSetEstimatingModel Q hQ_nonempty hQ_closed hQ_convex f μ L y k x := by
  simpa [lineMap_apply_module] using
    congrFun
      (simpleSetEstimatingFunction_succ
        Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k)
      x

/-- The center sequence starts from the initial point `x0`. -/
-- Proof sketch: unfold `simpleSetEstimatingCenter` at index `0`.
theorem simpleSetEstimatingCenter_zero
    :
    simpleSetEstimatingCenter
        Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α 0 = x0 := rfl

/-- The center sequence satisfies its defining recursion. -/
-- Proof sketch: unfold `simpleSetEstimatingCenter` at index `k + 1`.
theorem simpleSetEstimatingCenter_succ
    (k : ℕ) :
    simpleSetEstimatingCenter
        Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α (k + 1) =
      let gammaCurr := gamma k
      let gammaNext := gamma (k + 1)
      let yk := y k
      let gQk := gProj k
      (1 / gammaNext) •
        (((1 - α k) * gammaCurr) •
            simpleSetEstimatingCenter
              Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k +
          (α k * μ) • yk -
          α k • gQk) := rfl

/-- The scalar term `φ_k^*` starts from the initial value `f(x0)`. -/
-- Proof sketch: unfold `simpleSetEstimatingValue` at index `0`.
theorem simpleSetEstimatingValue_zero
    :
    simpleSetEstimatingValue
        Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α 0 = f x0 := rfl

/-- The scalar term `φ_k^*` satisfies its defining recursive update. -/
-- Proof sketch: unfold `simpleSetEstimatingValue` at index `k + 1`.
theorem simpleSetEstimatingValue_succ
    (k : ℕ) :
    simpleSetEstimatingValue
        Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α (k + 1) =
      let gammaNext := gamma (k + 1)
      let gammaCurr := gamma k
      let yk := y k
      let vCurr :=
        simpleSetEstimatingCenter
          Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k
      let gCurr := gProj k
      let xQCurr := xProj k
      (1 - α k) *
          simpleSetEstimatingValue
            Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k +
        α k * f xQCurr +
        (α k / (2 * L) - α k ^ (2 : ℕ) / (2 * gammaNext)) * ‖gCurr‖ ^ (2 : ℕ) +
        (α k * (1 - α k) * gammaCurr / gammaNext) *
          ((μ / 2) * ‖yk - vCurr‖ ^ (2 : ℕ) + inner ℝ gCurr (vCurr - yk)) := rfl

/- Helper for Proposition 2.22: rewrite the center update relative to the basepoint `y k`. -/
-- Proof sketch: subtract `y k` from the explicit recursion for `v_{k+1}` and use the curvature
-- recursion to absorb the `y k` coefficient.
private theorem simpleSetEstimatingCenter_succ_sub_eq
    (hγ : ∀ k, gamma (k + 1) ≠ 0)
    (k : ℕ) :
    simpleSetEstimatingCenter
        Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α (k + 1) - y k =
      (1 / gamma (k + 1)) •
        (((1 - α k) * gamma k) •
            (simpleSetEstimatingCenter
              Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k - y k) -
          α k • gProj k) := by
  let center := simpleSetEstimatingCenter
    Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α
  let gammaCurr : ℝ := gamma k
  let gammaNext : ℝ := gamma (k + 1)
  let vCurr : E :=
    simpleSetEstimatingCenter
      Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k
  let yk : E := y k
  let gk : E := gProj k
  have hgammaNext_ne : gammaNext ≠ 0 := by
    simpa [gammaNext] using hγ k
  have hyk : (1 / gammaNext) • (gammaNext • yk) = yk := by
    rw [smul_smul, one_div, inv_mul_cancel₀ hgammaNext_ne, one_smul]
  calc
    center (k + 1) - y k
        = (1 / gammaNext) •
            (((1 - α k) * gammaCurr) • vCurr + (α k * μ) • yk - α k • gk) - yk := by
              simpa [center, gammaCurr, gammaNext, vCurr, yk, gk] using
                congrArg (fun z : E ↦ z - y k)
                  (simpleSetEstimatingCenter_succ
                    Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k)
    _ = (1 / gammaNext) •
          (((1 - α k) * gammaCurr) • vCurr + (α k * μ) • yk - α k • gk) -
            (1 / gammaNext) • (gammaNext • yk) := by rw [hyk]
    _ = (1 / gammaNext) •
          ((((1 - α k) * gammaCurr) • vCurr + (α k * μ) • yk - α k • gk) - gammaNext • yk) := by
            conv_rhs => rw [smul_sub]
    _ = (1 / gammaNext) • (((1 - α k) * gammaCurr) • (vCurr - yk) - α k • gk) := by
      congr 1
      change
        ((1 - α k) * gammaCurr) • vCurr + (α k * μ) • yk - α k • gk -
            (((1 - α k) * gammaCurr + α k * μ) • yk) =
          ((1 - α k) * gammaCurr) • (vCurr - yk) - α k • gk
      calc
        ((1 - α k) * gammaCurr) • vCurr + (α k * μ) • yk - α k • gk -
            (((1 - α k) * gammaCurr + α k * μ) • yk)
            =
            ((1 - α k) * gammaCurr) • vCurr +
              ((α k * μ) • yk - (((1 - α k) * gammaCurr + α k * μ) • yk)) -
              α k • gk := by
                abel
        _ =
            ((1 - α k) * gammaCurr) • vCurr +
              (-(((1 - α k) * gammaCurr) • yk)) -
              α k • gk := by
                rw [add_smul]
                abel
        _ = ((1 - α k) * gammaCurr) • (vCurr - yk) - α k • gk := by
          rw [smul_sub]
          abel

/-- Helper for Proposition 2.22: the updated center gives the required linear term after
expanding the centered quadratic about `y k`. -/
-- Proof sketch: negate the previous center-difference formula, move the scalar inside the inner
-- product, and cancel the reciprocal with the nonzero next curvature.
private theorem simpleSetEstimatingCenter_succ_cross_term_eq
    (hγ : ∀ k, gamma (k + 1) ≠ 0)
    (k : ℕ)
    (x : E) :
    gamma (k + 1) *
        inner ℝ
          (x - y k)
          (y k -
            simpleSetEstimatingCenter
              Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α (k + 1)) =
      (1 - α k) * gamma k *
          inner ℝ
            (x - y k)
            (y k -
              simpleSetEstimatingCenter
                Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k) +
        α k * inner ℝ (gProj k) (x - y k) := by
  let center := simpleSetEstimatingCenter
    Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α
  let gammaCurr : ℝ := gamma k
  let gammaNext : ℝ := gamma (k + 1)
  let vCurr : E :=
    simpleSetEstimatingCenter
      Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k
  let vNext : E :=
    simpleSetEstimatingCenter
      Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α (k + 1)
  let yk : E := y k
  let gk : E := gProj k
  have hgammaNext_ne : gammaNext ≠ 0 := by
    simpa [gammaNext] using hγ k
  have hsub :
      yk - vNext =
        (1 / gammaNext) • (((1 - α k) * gammaCurr) • (yk - vCurr) + α k • gk) := by
    calc
      yk - vNext = -(vNext - yk) := by abel
      _ = -((1 / gammaNext) • (((1 - α k) * gammaCurr) • (vCurr - yk) - α k • gk)) := by
            rw [simpleSetEstimatingCenter_succ_sub_eq
              Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α hγ k]
      _ = (1 / gammaNext) • (((1 - α k) * gammaCurr) • (yk - vCurr) + α k • gk) := by
            simp [sub_eq_add_neg, add_comm]
  calc
    gammaNext * inner ℝ (x - yk) (yk - vNext)
        = gammaNext *
            inner ℝ (x - yk)
              ((1 / gammaNext) • (((1 - α k) * gammaCurr) • (yk - vCurr) + α k • gk)) := by
                rw [hsub]
    _ =
        (1 - α k) * gammaCurr * inner ℝ (x - yk) (yk - vCurr) +
          α k * inner ℝ gk (x - yk) := by
            rw [real_inner_smul_right, inner_add_right, real_inner_smul_right,
              real_inner_smul_right, real_inner_comm (x - yk) gk]
            field_simp [hgammaNext_ne]

/-- Helper for Proposition 2.22: the new center's squared distance to `y k` matches the scalar
recursion for `φ_{k+1}^*`. -/
-- Proof sketch: substitute the center-difference formula, scale out the nonzero next curvature,
-- and expand the remaining norm square with `norm_sub_sq_real`.
private theorem simpleSetEstimatingCenter_succ_norm_sq_eq
    (hγ : ∀ k, gamma (k + 1) ≠ 0)
    (k : ℕ) :
    (gamma (k + 1) / 2) *
        ‖simpleSetEstimatingCenter
            Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α (k + 1) - y k‖ ^ (2 : ℕ) =
      (((1 - α k) ^ (2 : ℕ) * gamma k ^ (2 : ℕ)) / (2 * gamma (k + 1))) *
        ‖simpleSetEstimatingCenter
            Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k - y k‖ ^ (2 : ℕ) -
        (α k * (1 - α k) * gamma k / gamma (k + 1)) *
          inner ℝ
            (gProj k)
            (simpleSetEstimatingCenter
              Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k - y k) +
        (α k ^ (2 : ℕ) / (2 * gamma (k + 1))) *
          ‖gProj k‖ ^ (2 : ℕ) := by
  let center := simpleSetEstimatingCenter
    Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α
  let gammaCurr : ℝ := gamma k
  let gammaNext : ℝ := gamma (k + 1)
  let vCurr : E :=
    simpleSetEstimatingCenter
      Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k
  let yk : E := y k
  let gk : E := gProj k
  have hgammaNext_ne : gammaNext ≠ 0 := by
    simpa [gammaNext] using hγ k
  have hscaled :
      (gammaNext / 2) *
          ‖(1 / gammaNext) • (((1 - α k) * gammaCurr) • (vCurr - yk) - α k • gk)‖ ^ (2 : ℕ) =
        (1 / (2 * gammaNext)) *
          ‖((1 - α k) * gammaCurr) • (vCurr - yk) - α k • gk‖ ^ (2 : ℕ) := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    field_simp [hgammaNext_ne]
  have hexpand :
      ‖((1 - α k) * gammaCurr) • (vCurr - yk) - α k • gk‖ ^ (2 : ℕ) =
        ((1 - α k) * gammaCurr) ^ (2 : ℕ) * ‖vCurr - yk‖ ^ (2 : ℕ) -
          2 * ((1 - α k) * gammaCurr) * α k * inner ℝ (vCurr - yk) gk +
          α k ^ (2 : ℕ) * ‖gk‖ ^ (2 : ℕ) := by
    rw [norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
      mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
    ring
  calc
    (gamma (k + 1) / 2) * ‖center (k + 1) - y k‖ ^ (2 : ℕ)
        =
        (gammaNext / 2) *
          ‖(1 / gammaNext) • (((1 - α k) * gammaCurr) • (vCurr - yk) - α k • gk)‖ ^ (2 : ℕ) := by
            simpa [gammaNext, gammaCurr, vCurr, yk, gk] using
              congrArg
                (fun z : E ↦ (gamma (k + 1) / 2) * ‖z‖ ^ (2 : ℕ))
                (simpleSetEstimatingCenter_succ_sub_eq
                  Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α hγ k)
    _ = (1 / (2 * gammaNext)) *
          ‖((1 - α k) * gammaCurr) • (vCurr - yk) - α k • gk‖ ^ (2 : ℕ) := hscaled
    _ =
        (1 / (2 * gammaNext)) *
          (((1 - α k) * gammaCurr) ^ (2 : ℕ) * ‖vCurr - yk‖ ^ (2 : ℕ) -
            2 * ((1 - α k) * gammaCurr) * α k * inner ℝ (vCurr - yk) gk +
            α k ^ (2 : ℕ) * ‖gk‖ ^ (2 : ℕ)) := by rw [hexpand]
    _ =
        (((1 - α k) ^ (2 : ℕ) * gammaCurr ^ (2 : ℕ)) / (2 * gammaNext)) *
          ‖vCurr - yk‖ ^ (2 : ℕ) -
          (α k * (1 - α k) * gammaCurr / gammaNext) * inner ℝ gk (vCurr - yk) +
          (α k ^ (2 : ℕ) / (2 * gammaNext)) * ‖gk‖ ^ (2 : ℕ) := by
            rw [real_inner_comm (vCurr - yk) gk]
            ring

/-- Proposition 2.22: if each successor curvature `γ_{k+1}` is nonzero, the recursively defined
estimating sequence over a simple set is exactly the centered quadratic
`quadraticallyRegularizedObjective (fun _ ↦ φ_k^*) γ_k v_k`, where `φ_k^*` and `v_k` are the
source-facing recursive sequences `simpleSetEstimatingValue` and `simpleSetEstimatingCenter`,
while `γ_k` is the owner curvature sequence `estimatingSequenceCurvature` from `Lemma_2_9`. -/
-- Proof sketch: prove the formula by induction on `k`. The base case is the initial quadratic
-- model centered at `x0`. For the inductive step, expand the recursion for
-- `simpleSetEstimatingFunction`, substitute the induction hypothesis, expand the projected lower
-- quadratic model, and complete the square in `x` to identify the new constant term, center, and
-- curvature with the recursive formulas defining `simpleSetEstimatingValue`,
-- `simpleSetEstimatingCenter`, and `estimatingSequenceCurvature`.
theorem simpleSetEstimatingFunction_eq_canonicalQuadratic
    (hγ : ∀ k, gamma (k + 1) ≠ 0)
    (k : ℕ) :
    phi k =
      quadraticallyRegularizedObjective
        (fun _ ↦
          simpleSetEstimatingValue
            Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k)
        (gamma k)
        (simpleSetEstimatingCenter
          Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k) := by
  let center := simpleSetEstimatingCenter
    Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α
  let value := simpleSetEstimatingValue
    Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α
  ext x
  induction k generalizing x with
  | zero =>
      simp [quadraticallyRegularizedObjective_apply, simpleSetEstimatingValue_zero,
        simpleSetEstimatingCenter_zero]
  | succ k hk =>
      let gammaCurr : ℝ := gamma k
      let gammaNext : ℝ := gamma (k + 1)
      let vCurr : E :=
        simpleSetEstimatingCenter
          Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k
      let vNext : E :=
        simpleSetEstimatingCenter
          Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α (k + 1)
      let yk : E := y k
      let gk : E := gProj k
      let xQk : E := xProj k
      have hrecx :
          phi (k + 1) x =
            (1 - α k) * (value k + (gammaCurr / 2) * ‖x - vCurr‖ ^ (2 : ℕ)) +
              α k *
                (f xQk + (1 / (2 * L)) * ‖gk‖ ^ (2 : ℕ) +
                  inner ℝ gk (x - yk) + (μ / 2) * ‖x - yk‖ ^ (2 : ℕ)) := by
        calc
          phi (k + 1) x =
              (1 - α k) * phi k x +
                α k * simpleSetEstimatingModel Q hQ_nonempty hQ_closed hQ_convex f μ L y k x := by
                  exact
                    simpleSetEstimatingFunction_succ_apply
                      Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k x
          _ =
              (1 - α k) *
                  quadraticallyRegularizedObjective
                    (fun _ : E ↦ value k)
                    (gamma k)
                    (center k) x +
                α k * simpleSetEstimatingModel Q hQ_nonempty hQ_closed hQ_convex f μ L y k x := by
                  rw [hk x]
          _ =
              (1 - α k) * (value k + (gammaCurr / 2) * ‖x - vCurr‖ ^ (2 : ℕ)) +
                α k * simpleSetEstimatingModel Q hQ_nonempty hQ_closed hQ_convex f μ L y k x := by
                  simp [quadraticallyRegularizedObjective_apply, center, gammaCurr, vCurr]
          _ =
              (1 - α k) * (value k + (gammaCurr / 2) * ‖x - vCurr‖ ^ (2 : ℕ)) +
                α k *
                  (f xQk + (1 / (2 * L)) * ‖gk‖ ^ (2 : ℕ) +
                    inner ℝ gk (x - yk) + (μ / 2) * ‖x - yk‖ ^ (2 : ℕ)) := by
                  rw [simpleSetEstimatingModel_apply]
      have hgammaNext_ne : gammaNext ≠ 0 := by
        simpa [gammaNext] using hγ k
      have hcurv :
          gammaNext = (1 - α k) * gammaCurr + α k * μ := by
        simpa [gammaCurr, gammaNext] using estimatingSequenceCurvature_succ μ gamma0 α k
      have hvalue :
          value (k + 1) =
            (1 - α k) * value k +
              α k * f xQk +
              (α k / (2 * L) - α k ^ (2 : ℕ) / (2 * gammaNext)) * ‖gk‖ ^ (2 : ℕ) +
              (α k * (1 - α k) * gammaCurr / gammaNext) *
                ((μ / 2) * ‖yk - vCurr‖ ^ (2 : ℕ) + inner ℝ gk (vCurr - yk)) := by
        simpa [gammaCurr, gammaNext, vCurr, yk, gk, xQk] using
          simpleSetEstimatingValue_succ
            Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k
      have hcross :
          gammaNext * inner ℝ (x - yk) (yk - vNext) =
            (1 - α k) * gammaCurr * inner ℝ (x - yk) (yk - vCurr) +
              α k * inner ℝ gk (x - yk) := by
        simpa [gammaCurr, gammaNext, vCurr, vNext, yk, gk] using
          simpleSetEstimatingCenter_succ_cross_term_eq
            Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α hγ k x
      have hnorm :
          (gammaNext / 2) * ‖yk - vNext‖ ^ (2 : ℕ) =
            (((1 - α k) ^ (2 : ℕ) * gammaCurr ^ (2 : ℕ)) / (2 * gammaNext)) *
              ‖vCurr - yk‖ ^ (2 : ℕ) -
              (α k * (1 - α k) * gammaCurr / gammaNext) * inner ℝ gk (vCurr - yk) +
              (α k ^ (2 : ℕ) / (2 * gammaNext)) * ‖gk‖ ^ (2 : ℕ) := by
        simpa [gammaCurr, gammaNext, vCurr, vNext, yk, gk, norm_sub_rev] using
          simpleSetEstimatingCenter_succ_norm_sq_eq
            Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α hγ k
      change
        phi (k + 1) x =
          value (k + 1) + (gammaNext / 2) * ‖(x - vNext : E)‖ ^ (2 : ℕ)
      rw [hrecx, hvalue,
        centered_quadratic_expand_about_point gammaCurr x yk vCurr,
        centered_quadratic_expand_about_point gammaNext x yk vNext, hcross, hnorm]
      let commonForm :=
        (1 - α k) * value k +
          α k * f xQk +
          (1 - α k) * (gammaCurr / 2) * ‖yk - vCurr‖ ^ (2 : ℕ) +
          ((1 - α k) * gammaCurr) * inner ℝ (x - yk) (yk - vCurr) +
          ((1 - α k) * (gammaCurr / 2) + α k * (μ / 2)) * ‖x - yk‖ ^ (2 : ℕ) +
          α k * inner ℝ gk (x - yk)
      have hconstCoeff :
          α k * (1 - α k) * gammaCurr / gammaNext * (μ / 2) +
            (1 - α k) ^ (2 : ℕ) * gammaCurr ^ (2 : ℕ) / (2 * gammaNext) =
            (1 - α k) * (gammaCurr / 2) := by
        field_simp [hgammaNext_ne]
        rw [hcurv]
        ring
      have hxCoeff :
          gammaNext / 2 = (1 - α k) * (gammaCurr / 2) + α k * (μ / 2) := by
        nlinarith [hcurv]
      have hleft :
          (1 - α k) *
              (value k +
                (gammaCurr / 2 * ‖yk - vCurr‖ ^ (2 : ℕ) +
                  gammaCurr * inner ℝ (x - yk) (yk - vCurr) +
                  gammaCurr / 2 * ‖x - yk‖ ^ (2 : ℕ))) +
            α k *
              (f xQk + 1 / (2 * L) * ‖gk‖ ^ (2 : ℕ) +
                inner ℝ gk (x - yk) + μ / 2 * ‖x - yk‖ ^ (2 : ℕ)) =
            commonForm + α k * (1 / (2 * L)) * ‖gk‖ ^ (2 : ℕ) := by
        simp [commonForm]
        ring
      have hright :
          (1 - α k) * value k +
              α k * f xQk +
              (α k / (2 * L) - α k ^ (2 : ℕ) / (2 * gammaNext)) * ‖gk‖ ^ (2 : ℕ) +
              α k * (1 - α k) * gammaCurr / gammaNext *
                ((μ / 2) * ‖yk - vCurr‖ ^ (2 : ℕ) + inner ℝ gk (vCurr - yk)) +
            (((1 - α k) ^ (2 : ℕ) * gammaCurr ^ (2 : ℕ) / (2 * gammaNext)) *
                  ‖vCurr - yk‖ ^ (2 : ℕ) -
                α k * (1 - α k) * gammaCurr / gammaNext * inner ℝ gk (vCurr - yk) +
                α k ^ (2 : ℕ) / (2 * gammaNext) * ‖gk‖ ^ (2 : ℕ) +
              ((1 - α k) * gammaCurr * inner ℝ (x - yk) (yk - vCurr) +
                α k * inner ℝ gk (x - yk)) +
              gammaNext / 2 * ‖x - yk‖ ^ (2 : ℕ)) =
            commonForm + α k * (1 / (2 * L)) * ‖gk‖ ^ (2 : ℕ) := by
        calc
          (1 - α k) * value k +
                α k * f xQk +
                (α k / (2 * L) - α k ^ (2 : ℕ) / (2 * gammaNext)) * ‖gk‖ ^ (2 : ℕ) +
                α k * (1 - α k) * gammaCurr / gammaNext *
                  ((μ / 2) * ‖yk - vCurr‖ ^ (2 : ℕ) + inner ℝ gk (vCurr - yk)) +
              (((1 - α k) ^ (2 : ℕ) * gammaCurr ^ (2 : ℕ) / (2 * gammaNext)) *
                    ‖vCurr - yk‖ ^ (2 : ℕ) -
                  α k * (1 - α k) * gammaCurr / gammaNext * inner ℝ gk (vCurr - yk) +
                  α k ^ (2 : ℕ) / (2 * gammaNext) * ‖gk‖ ^ (2 : ℕ) +
                ((1 - α k) * gammaCurr * inner ℝ (x - yk) (yk - vCurr) +
                  α k * inner ℝ gk (x - yk)) +
                gammaNext / 2 * ‖x - yk‖ ^ (2 : ℕ))
              =
              (1 - α k) * value k +
                α k * f xQk +
                α k * (1 / (2 * L)) * ‖gk‖ ^ (2 : ℕ) +
                (α k * (1 - α k) * gammaCurr / gammaNext * (μ / 2) +
                    (1 - α k) ^ (2 : ℕ) * gammaCurr ^ (2 : ℕ) / (2 * gammaNext)) *
                  ‖yk - vCurr‖ ^ (2 : ℕ) +
                ((1 - α k) * gammaCurr) * inner ℝ (x - yk) (yk - vCurr) +
                (gammaNext / 2) * ‖x - yk‖ ^ (2 : ℕ) +
                α k * inner ℝ gk (x - yk) := by
                  simp [norm_sub_rev]
                  ring
          _ = commonForm + α k * (1 / (2 * L)) * ‖gk‖ ^ (2 : ℕ) := by
            rw [hconstCoeff, hxCoeff]
            simp [commonForm]
            ring
      simpa [quadraticallyRegularizedObjective_apply, gammaCurr, gammaNext, vCurr, vNext, yk, gk,
        xQk] using hleft.trans hright.symm

/-- Companion evaluation formula for Proposition 2.22: the owner equality unfolds to the
displayed centered quadratic expression at each point `x`. -/
theorem simpleSetEstimatingFunction_eq_canonicalQuadratic_apply
    (hγ : ∀ k, gamma (k + 1) ≠ 0)
    (k : ℕ) (x : E) :
    phi k x =
      simpleSetEstimatingValue
          Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k +
        (gamma k / 2) *
          ‖x -
              simpleSetEstimatingCenter
                Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k‖ ^ (2 : ℕ) := by
  let center := simpleSetEstimatingCenter
    Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α
  let value := simpleSetEstimatingValue
    Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α
  calc
    phi k x =
        quadraticallyRegularizedObjective
          (fun _ ↦ value k)
          (gamma k)
          (center k) x :=
      congrFun
        (simpleSetEstimatingFunction_eq_canonicalQuadratic
          Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α hγ k)
        x
    _ = value k + (gamma k / 2) * ‖x - center k‖ ^ (2 : ℕ) := by
      simp [quadraticallyRegularizedObjective_apply]

end

end
