

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_30 (from Chap02) -/
noncomputable section

open scoped ConstrainedArgmin

universe u v

/- Primary domain: equality-constrained minimization and its Lagrangian dual layer.

Owner declarations sampled before refining this file:
* `SetConstrainedMinimizationProblem` and
  `SetConstrainedMinimizationProblem.optimalValue` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_3_7.lean`;
* `LagrangianProblem.lagrangian`, `LagrangianProblem.dualFunction`, and
  `LagrangianProblem.lagrangianMinimizers` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_10_2.lean`;
* `linearEqualityFeasibleSet` and `mem_linearEqualityFeasibleSet_iff` in
  `LecturesConvexOptimization_Nesterov_2018/Chap03/LinearEqualityFeasibleSet.lean`;
* `LinearEqualityConstrainedConvexProblem` in `LecturesConvexOptimization_Nesterov_2018/Chap03/Definition_3_27.lean`, which uses
  the same intrinsic linear-map owner for equality constraints.

Best owner abstractions:
* source-facing: `PrimalEqualityConstrainedProblem E Λ`;
* core/canonical: `SetConstrainedMinimizationProblem E` together with
  `linearEqualityFeasibleSet Q A b`;
* bridge/view: the Euclidean matrix presentation obtained by specializing `E`, `Λ`, and using
  `Matrix.toEuclideanLin`.

Primitive data:
* the ambient feasible set / objective owner `SetConstrainedMinimizationProblem E`;
* the linear map `A : E →ₗ[ℝ] Λ`;
* the right-hand side `b : Λ`.

Derived API:
* `equalityFeasibleSet`;
* `primalProblem` and `primalOptimalValue`;
* `constraintResidual` on the additive codomain layer;
* `lagrangianSubproblem`, `lagrangian`, `dualFunction`, and `lagrangianMinimizers`.

This refinement deletes the matrix-specific primitive owner layer from Definition 2.30 itself.
The textbook matrix realization remains available by passing `A.toEuclideanLin` to the intrinsic
owner. -/

/-- Definition 2.30: a primal equality-constrained problem consists of an ambient feasible set
`Q`, an objective `f`, a linear map `A`, and a right-hand side `b`, encoding
`f^* = min {f(x) | x ∈ Q, A x = b}`. In the textbook Euclidean presentation, the linear map is
represented by a matrix via `Matrix.toEuclideanLin`. -/
structure PrimalEqualityConstrainedProblem
    (E : Type u) (Λ : Type v) [AddCommMonoid E] [Module ℝ E] [AddCommMonoid Λ] [Module ℝ Λ]
    extends SetConstrainedMinimizationProblem E where
  /-- The linear equality map. -/
  A : E →ₗ[ℝ] Λ
  /-- The right-hand side of the equality constraint. -/
  b : Λ

/-- A primal equality-constrained problem can be used as its ambient objective function. -/
instance {E : Type u} {Λ : Type v} [AddCommMonoid E] [Module ℝ E] [AddCommMonoid Λ] [Module ℝ Λ] :
    CoeFun (PrimalEqualityConstrainedProblem E Λ) (fun _ ↦ E → ℝ) where
  coe problem := problem.objective

namespace SetConstrainedMinimizationProblem

variable {E : Type u} {Λ : Type v} [AddCommMonoid E] [Module ℝ E] [AddCommMonoid Λ] [Module ℝ Λ]

/-- The Chapter 2 equality-constrained owner attached to an ambient feasible set and objective,
together with linear equality data `A x = b`. -/
def toPrimalEqualityConstrainedProblem (problem : SetConstrainedMinimizationProblem E)
    (A : E →ₗ[ℝ] Λ) (b : Λ) : PrimalEqualityConstrainedProblem E Λ where
  toSetConstrainedMinimizationProblem := problem
  A := A
  b := b

@[simp] theorem toPrimalEqualityConstrainedProblem_feasibleSet
    (problem : SetConstrainedMinimizationProblem E) (A : E →ₗ[ℝ] Λ) (b : Λ) :
    (problem.toPrimalEqualityConstrainedProblem A b).feasibleSet = problem.feasibleSet :=
  rfl

@[simp] theorem toPrimalEqualityConstrainedProblem_apply
    (problem : SetConstrainedMinimizationProblem E) (A : E →ₗ[ℝ] Λ) (b : Λ) (x : E) :
    problem.toPrimalEqualityConstrainedProblem A b x = problem x :=
  rfl

@[simp] theorem toPrimalEqualityConstrainedProblem_A
    (problem : SetConstrainedMinimizationProblem E) (A : E →ₗ[ℝ] Λ) (b : Λ) :
    (problem.toPrimalEqualityConstrainedProblem A b).A = A :=
  rfl

@[simp] theorem toPrimalEqualityConstrainedProblem_b
    (problem : SetConstrainedMinimizationProblem E) (A : E →ₗ[ℝ] Λ) (b : Λ) :
    (problem.toPrimalEqualityConstrainedProblem A b).b = b :=
  rfl

end SetConstrainedMinimizationProblem

namespace PrimalEqualityConstrainedProblem

variable {E : Type u} {Λ : Type v} [AddCommMonoid E] [Module ℝ E] [AddCommMonoid Λ] [Module ℝ Λ]

/-- The equality-feasible region `Q ∩ {x | A x = b}` attached to the ambient problem. -/
def equalityFeasibleSet (problem : PrimalEqualityConstrainedProblem E Λ) : Set E :=
  linearEqualityFeasibleSet problem.feasibleSet problem.A problem.b

/-- Membership in the equality-feasible region means ambient feasibility together with
`A x = b`. -/
@[simp] theorem mem_equalityFeasibleSet_iff
    {problem : PrimalEqualityConstrainedProblem E Λ} {x : E} :
    x ∈ problem.equalityFeasibleSet ↔ x ∈ problem.feasibleSet ∧ problem.A x = problem.b := by
  rw [equalityFeasibleSet, mem_linearEqualityFeasibleSet_iff]

/-- The set-constrained minimization problem obtained by restricting the ambient feasible region
to the equality-feasible points. -/
def primalProblem (problem : PrimalEqualityConstrainedProblem E Λ) :
    SetConstrainedMinimizationProblem E where
  feasibleSet := problem.equalityFeasibleSet
  objective := problem

/-- The primal optimal value `f^*`, interpreted as the extended-real infimum of the objective
over the equality-feasible set. -/
def primalOptimalValue (problem : PrimalEqualityConstrainedProblem E Λ) : EReal :=
  problem.primalProblem.optimalValue

section AdditiveCodomain

variable [AddCommGroup Λ]

/-- The equality-constraint residual `b - A x`. -/
def constraintResidual (problem : PrimalEqualityConstrainedProblem E Λ) (x : E) : Λ :=
  problem.b - problem.A x

/-- Vanishing of the equality-constraint residual is exactly the linear equation `A x = b`. -/
theorem constraintResidual_eq_zero_iff
    {problem : PrimalEqualityConstrainedProblem E Λ} {x : E} :
    problem.constraintResidual x = 0 ↔ problem.A x = problem.b := by
  constructor
  · intro hx
    simpa [constraintResidual] using (sub_eq_zero.mp (by simpa [constraintResidual] using hx)).symm
  · intro hx
    simpa [constraintResidual] using sub_eq_zero.mpr hx.symm

/-- Membership in the equality-feasible region is equivalent to ambient feasibility together with
vanishing equality residual. -/
@[simp] theorem mem_equalityFeasibleSet_iff_constraintResidual_eq_zero
    {problem : PrimalEqualityConstrainedProblem E Λ} {x : E} :
    x ∈ problem.equalityFeasibleSet ↔
      x ∈ problem.feasibleSet ∧ problem.constraintResidual x = 0 := by
  rw [problem.mem_equalityFeasibleSet_iff, problem.constraintResidual_eq_zero_iff]

end AdditiveCodomain

section LagrangianDuality

variable [NormedAddCommGroup Λ] [InnerProductSpace ℝ Λ]

/-- The equality-problem Lagrangian `𝓛(x, u) = f(x) + ⟪u, b - A x⟫`. -/
def lagrangian (problem : PrimalEqualityConstrainedProblem E Λ) (x : E) (u : Λ) : ℝ :=
  problem x + inner ℝ u (problem.constraintResidual x)

/-- The set-constrained subproblem obtained by minimizing the Lagrangian over the ambient feasible
set `Q`. -/
def lagrangianSubproblem (problem : PrimalEqualityConstrainedProblem E Λ)
    (u : Λ) : SetConstrainedMinimizationProblem E where
  feasibleSet := problem.feasibleSet
  objective := fun x ↦ problem.lagrangian x u

/-- The equality-problem dual function `φ(u) = inf_{x ∈ Q} 𝓛(x, u)`. -/
def dualFunction (problem : PrimalEqualityConstrainedProblem E Λ) (u : Λ) : EReal :=
  (problem.lagrangianSubproblem u).optimalValue

/-- The Lagrangian minimizer set `X*(u) = argmin_{x ∈ Q} 𝓛(x, u)`. -/
def lagrangianMinimizers (problem : PrimalEqualityConstrainedProblem E Λ)
    (u : Λ) : Set E :=
  argmin[problem.feasibleSet] fun x ↦ problem.lagrangian x u

/-- Membership in `X*(u)` means minimizing the equality-problem Lagrangian on the ambient set
`Q`. -/
@[simp] theorem mem_lagrangianMinimizers_iff
    {problem : PrimalEqualityConstrainedProblem E Λ} {u : Λ} {x : E} :
    x ∈ problem.lagrangianMinimizers u ↔
      x ∈ problem.feasibleSet ∧
        IsMinOn (fun y ↦ problem.lagrangian y u) problem.feasibleSet x := by
  rw [lagrangianMinimizers, mem_constrainedArgmin_iff]

/-- A point of `X*(u)` realizes the equality-problem dual value by evaluating the Lagrangian. -/
theorem dualFunction_eq_lagrangian
    (problem : PrimalEqualityConstrainedProblem E Λ) {u : Λ} {x : E}
    (hx : x ∈ problem.lagrangianMinimizers u) :
    problem.dualFunction u = (problem.lagrangian x u : EReal) := by
  simpa [dualFunction, lagrangianSubproblem, lagrangianMinimizers] using
    (problem.lagrangianSubproblem u).optimalValue_eq_of_mem_argmin hx

end LagrangianDuality

end PrimalEqualityConstrainedProblem

/-! ### Proposition_2_30 (from Chap02) -/
open HasGeometricRateOfConvergence

section

universe u

variable {α : Type u}

/-
Primary domain: scalar convergence rates for fixed-parameter internal suboptimality gaps.

Owner declarations sampled before refining:
* `HasGeometricRateOfConvergence`
* `of_step_bound`
* `exp_bound` in `Chap01/Definition_1_2_6.lean`
* `IsGLB (Set.range (f tk)) optimalValue`, the canonical infimum-value owner interface used
  across the project for exact optimal values

Best owner abstractions:
* `HasGeometricRateOfConvergence` on the scalar gap sequence
  `j ↦ f tk (x j) - optimalValue`
* `IsGLB (Set.range (f tk)) optimalValue` for the fixed-`t_k` optimal value

Source/core/bridge triage:
* source-facing: Proposition 2.30 and its nonnegative-optimal-value corollary
* core/canonical: the exact optimal-value hypothesis above together with
  `HasGeometricRateOfConvergence Δ (√q_f) (2 * Δ 0)`
* bridge/view: the exponential estimate from `exp_bound`

Primitive data:
* the fixed-parameter objective `f tk`
* the exact optimal value `optimalValue`
* the internal trajectory `x`
* the one-step contraction hypothesis
* the exact optimal-value hypothesis

Derived API:
* the scalar gap sequence `Δ`
* the owner geometric-rate statement
* the owner exponential consequence via `exp_bound`
* the specialization using `0 ≤ optimalValue`

No public lower-bound-only surrogate for `optimalValue` is kept: the source-facing gap
`f(t_k; x_j) - f^*(t_k)` is recorded against the actual infimum value.
-/

variable
  (f : ℝ → α → ℝ) (tk optimalValue : ℝ) (x : ℕ → α)
  {qf : ℝ}
  (hqf : qf ∈ Set.Ioc (0 : ℝ) 1)
  (hoptimal : IsGLB (Set.range (f tk)) optimalValue)
  (hstep :
    ∀ j : ℕ,
      f tk (x (j + 1)) - optimalValue ≤
        (1 - Real.sqrt qf) * (f tk (x j) - optimalValue))

local notation "σ" => Real.sqrt qf
local notation "Δ" => fun j : ℕ ↦ f tk (x j) - optimalValue

/-- Helper for Proposition 2.30: exact optimality of `optimalValue` makes every internal gap
`f tk (x j) - optimalValue` nonnegative. -/
lemma sub_nonneg_of_isGLB_range
    {f : ℝ → α → ℝ} {tk optimalValue : ℝ} {x : ℕ → α}
    (hoptimal : IsGLB (Set.range (f tk)) optimalValue) (j : ℕ) :
    0 ≤ f tk (x j) - optimalValue := by
  -- The infimum property gives `optimalValue ≤ f tk (x j)`, which is exactly the desired gap
  -- nonnegativity after rearranging.
  exact sub_nonneg.mpr <| hoptimal.1 ⟨x j, rfl⟩

/-- Helper for Proposition 2.30: when the exact optimal value is nonnegative, the initial
suboptimality gap is bounded by the initial objective value. -/
lemma initial_gap_le_initial_objective
    {f : ℝ → α → ℝ} {tk optimalValue : ℝ} {x : ℕ → α}
    (hoptimal_nonneg : 0 ≤ optimalValue) :
    f tk (x 0) - optimalValue ≤ f tk (x 0) := by
  -- Subtracting a nonnegative number can only decrease the initial objective value.
  nlinarith

include hqf hoptimal hstep

/-- Proposition 2.30: if `optimalValue` is the exact optimal value of the fixed-parameter
objective `f tk`, then the internal suboptimality-gap sequence
`j ↦ f tk (x j) - optimalValue` has geometric rate with contraction factor `1 - √q_f`. -/
-- Proof sketch: apply the one-step contraction inductively to the scalar sequence `Δ`; the
-- pointwise geometric and exponential bounds are then direct owner consequences.
theorem constrainedMinimizationInternalGap_hasGeometricRateOfConvergence :
    HasGeometricRateOfConvergence Δ σ (2 * Δ 0) := by
  have hgap0 : 0 ≤ Δ 0 := sub_nonneg_of_isGLB_range hoptimal 0
  refine of_step_bound (Real.sqrt_le_one.2 hqf.2) ?_ hstep
  nlinarith

/-- If the optimal value at the fixed parameter `t_k` is nonnegative, the owner exponential gap
bound is at most the same exponential factor times the initial objective value `f(t_k; x_0)`. -/
-- Proof sketch: apply `exp_bound` to the owner statement above, then use
-- `0 ≤ optimalValue` to bound `Δ 0 = f tk (x 0) - optimalValue` by `f tk (x 0)`.
theorem constrainedMinimizationInternalGap_le_exponential_rate_of_optimalValue_nonneg
    (hoptimal_nonneg : 0 ≤ optimalValue) :
    ∀ j : ℕ,
      Δ j ≤ (2 * f tk (x 0)) * Real.exp (-(σ * (j : ℝ))) := by
  intro j
  have hgap0 : 0 ≤ Δ 0 := sub_nonneg_of_isGLB_range hoptimal 0
  have hc : 0 ≤ 2 * Δ 0 := by nlinarith
  have hgap :
      Δ j ≤ (2 * Δ 0) * Real.exp (-(σ * (j : ℝ))) := by
    -- The owner exponential estimate is the exact textbook bound for the gap sequence.
    simpa using
      exp_bound
        (constrainedMinimizationInternalGap_hasGeometricRateOfConvergence
          f tk optimalValue x hqf hoptimal hstep)
        hc
        (Real.sqrt_pos.2 hqf.1)
        (Real.sqrt_le_one.2 hqf.2)
        j
  have hgap0_le : Δ 0 ≤ f tk (x 0) := by
    -- Route correction: the last textbook inequality is valid only after explicitly using the
    -- extra hypothesis `0 ≤ optimalValue`.
    simpa using initial_gap_le_initial_objective (f := f) (tk := tk) (optimalValue := optimalValue)
      (x := x) hoptimal_nonneg
  have hcoeff :
      2 * Δ 0 ≤ 2 * f tk (x 0) := by
    nlinarith [hgap0_le]
  have hexp_nonneg : 0 ≤ Real.exp (-(σ * (j : ℝ))) := (Real.exp_pos _).le
  -- Multiply the initial-gap comparison by the nonnegative exponential factor to finish.
  exact hgap.trans <| mul_le_mul_of_nonneg_right hcoeff hexp_nonneg

end

/-! ### Theorem_2_30 (from Chap02) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace StrongConvexOn

/- Theorem 2.30 lies in the chapter's strong-convexity / quadratic-growth domain on real normed
spaces.

Sampled owner-style declarations:
* `StrongConvexOnWith.quadratic_growth_of_isMinOn_of_mem` in `Definition_2_14`
* `strongConvexOnWith_normSeminorm_iff` in `Definition_2_14`
* mathlib `StrongConvexOn`

Best owner abstraction:
* core/canonical: `StrongConvexOnWith (normSeminorm ℝ E) μ Q f`
* bridge/view public surface: `StrongConvexOn Q μ f`

Primitive data:
* the strong-convexity hypothesis `hf : StrongConvexOn Q μ f`
* a feasible minimizer `hxStar : IsMinOn f Q xStar`

Derived API:
* the ambient-norm quadratic-growth estimate at feasible points
* the whole-space specialization

Source/core/bridge triage:
* source-facing: Theorem 2.30, stated on the ambient owner `StrongConvexOn`
* core/canonical: `StrongConvexOnWith.quadratic_growth_of_isMinOn_of_mem`
* bridge/view: `strongConvexOnWith_normSeminorm_iff`

This file therefore keeps only the ambient bridge theorem and derives it from the owner theorem in
`Definition_2_14`, instead of re-proving the same quadratic-growth argument locally.
-/

variable {μ : ℝ} {Q : Set E} {f : E → ℝ}

/-- A minimizer of a strongly convex function on a feasible set satisfies the standard quadratic
growth bound at every feasible point. -/
theorem quadratic_growth_of_isMinOn_of_mem
    (hf : StrongConvexOn Q μ f) {xStar : E}
    (hxStar_mem : xStar ∈ Q) (hxStar : IsMinOn f Q xStar)
    (x : E) (hx : x ∈ Q) :
    f x ≥ f xStar + (μ / 2) * ‖x - xStar‖ ^ (2 : ℕ) := by
  -- Route correction: reuse the canonical `StrongConvexOnWith` quadratic-growth theorem rather
  -- than rebuilding a separate first-order optimality argument in this item file.
  by_cases hμ : 0 < μ
  · have hf' : StrongConvexOnWith (normSeminorm ℝ E) μ Q f :=
      strongConvexOnWith_normSeminorm_iff.2 ⟨hμ, hf⟩
    -- In the positive-curvature branch, the normed-space statement is exactly the owner theorem.
    simpa using hf'.quadratic_growth_of_isMinOn_of_mem hxStar_mem hxStar x hx
  · have hμ_nonpos : μ ≤ 0 := le_of_not_gt hμ
    have hmin : f xStar ≤ f x := hxStar hx
    -- When `μ ≤ 0`, the quadratic term is nonpositive, so minimality alone gives the bound.
    nlinarith [sq_nonneg ‖x - xStar‖]

/-- Theorem 2.30: if `f : E → ℝ` is `μ`-strongly convex on the normed space `E`, `xStar` is a
global minimizer of `f`, then every point `x` satisfies the quadratic growth bound
`f x ≥ f xStar + (μ / 2) ‖x - xStar‖²`. -/
theorem quadratic_growth_of_isMinOn
    (hf : StrongConvexOn Set.univ μ f) {xStar : E}
    (hxStar : IsMinOn f Set.univ xStar) (x : E) :
    f x ≥ f xStar + (μ / 2) * ‖x - xStar‖ ^ (2 : ℕ) :=
  -- Specialize the feasible-set estimate to the whole space.
  hf.quadratic_growth_of_isMinOn_of_mem (by simp) hxStar x (by simp)

end StrongConvexOn
