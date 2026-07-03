import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Remark_2_20_1 (from Chap02) -/
open scoped Gradient ProjectedGradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Whole-space estimate-sequence lower bounds are best stated as the `Q = Set.univ`
specializations of the strong-convexity owner theorems from `Text_2_1`, rewritten through the
canonical whole-space bridges `gradientMapping_univ_eq_gradient_step` and
`reducedGradient_univ_eq_gradient`.

Primary domain:
* smooth convex optimization on a real Hilbert space, specialized to the unconstrained
  estimate-sequence recursion

Owner declarations sampled for this refinement:
* `simple_set_phi_star_lower_bound_intermediate` in `Text_2_1`;
* `simple_set_phi_star_lower_bound_of_objective_lower_bound` in `Text_2_1`;
* `gradientMapping_univ_eq_gradient_step` and `reducedGradient_univ_eq_gradient` in
  `Remark_2_35_1`.

Best owner abstraction:
* core/canonical: the strong-convexity set-level estimate-sequence lower bounds in `Text_2_1`;
* source-facing: their whole-space `Q = Set.univ` specializations written with `gradientStep`
  and `∇`;
* bridge/view: the canonical simplifications from projected-gradient data to the whole-space
  surface.

Primitive data:
* the objective `f`, initial point `x0`, the scalar parameters `(μ, L, γ₀)`, the iterate data
  `(y, α)`, and the stage data `x_k`;
* the estimating-sequence quantities `φ_k^*`, `φ_{k+1}^*`, `γ_k`, `γ_{k+1}`, and `v_k`.

Derived API:
* the textbook intermediate whole-space lower bound `(2.3.9)`;
* the final whole-space lower bound `(2.3.10)` obtained by first dropping the nonnegative strong
  objective correction from `(2.3.8)` and then specializing the μ-free owner theorem.

This file keeps only the whole-space specializations and does not introduce any parallel local
owner API. -/

section

variable
    (f : E → ℝ) (x0 : E)
    (μ : ℝ) (L : NNRealˣ) (gamma0 : ℝ)
    (y : ℕ → E) (α : ℕ → ℝ)
    (hγ : ∀ k, estimatingSequenceCurvature μ gamma0 α (k + 1) ≠ 0)
    (k : ℕ) (xk : E)

local notation "gammaK" => estimatingSequenceCurvature μ gamma0 α k
local notation "gammaKp1" => estimatingSequenceCurvature μ gamma0 α (k + 1)

local notation "phiK" =>
  simpleSetEstimatingValue
    (Set.univ : Set E) Set.univ_nonempty isClosed_univ convex_univ
    f x0 μ L gamma0 y α k

local notation "phiKp1" =>
  simpleSetEstimatingValue
    (Set.univ : Set E) Set.univ_nonempty isClosed_univ convex_univ
    f x0 μ L gamma0 y α (k + 1)

local notation "vK" =>
  simpleSetEstimatingCenter
    (Set.univ : Set E) Set.univ_nonempty isClosed_univ convex_univ
    f x0 μ L gamma0 y α k

local notation "yK" => y k

local notation "transportCoeff" =>
  α k * (1 - α k) * gammaK / gammaKp1

local notation "intermediateRhs" =>
  (1 - α k) * f xk +
    α k * f (gradientStep f yK L) +
      (α k / (2 * (L : ℝ)) - α k ^ (2 : ℕ) / (2 * gammaKp1)) * ‖∇ f yK‖ ^ (2 : ℕ) +
        transportCoeff * inner ℝ (∇ f yK) (vK - yK)

local notation "strongObjectiveLowerRhs" =>
  f (gradientStep f yK L) +
    inner ℝ (∇ f yK) (xk - yK) +
      (1 / (2 * (L : ℝ))) * ‖∇ f yK‖ ^ (2 : ℕ) +
        (μ / 2) * ‖xk - yK‖ ^ (2 : ℕ)

local notation "finalRhs" =>
  f (gradientStep f yK L) +
    (1 / (2 * (L : ℝ)) - α k ^ (2 : ℕ) / (2 * gammaKp1)) * ‖∇ f yK‖ ^ (2 : ℕ) +
      (1 - α k) * inner ℝ (∇ f yK)
        (((α k * gammaK) / gammaKp1) • (vK - yK) + (xk - yK))

/-- The intermediate whole-space lower bound obtained from the strong-convexity owner recursion by
specializing to `Q = Set.univ` and dropping the nonnegative transport strong-convexity term. -/
-- Proof sketch: specialize `simple_set_phi_star_lower_bound_intermediate` to `Q = Set.univ` and
-- rewrite `x_Q` and `g_Q` as `gradientStep` and `∇`.
theorem whole_space_phi_star_lower_bound_intermediate
    (halpha_k : α k ≤ 1)
    (htransportCoeff : 0 ≤ transportCoeff)
    (hμ : 0 ≤ μ)
    (hphi_k : f xk ≤ phiK) :
    phiKp1 ≥ intermediateRhs := by
  -- Specialize the set-level owner theorem to the unconstrained domain `Set.univ`.
  have howner :=
    simple_set_phi_star_lower_bound_intermediate
      (Q := (Set.univ : Set E))
      (hQ_nonempty := Set.univ_nonempty)
      (hQ_closed := isClosed_univ)
      (hQ_convex := convex_univ)
      (f := f) (x0 := x0) (μ := μ) (L := L) (gamma0 := gamma0) (y := y) (α := α)
      (k := k) (xk := xk)
      halpha_k htransportCoeff hμ hphi_k
  -- The whole-space bridge theorems rewrite the projected-gradient quantities to `gradientStep`
  -- and `∇`, producing exactly the textbook surface form `(2.3.9)`.
  simpa [gradientMapping_univ_eq_gradient_step, reducedGradient_univ_eq_gradient] using howner

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- Helper for Remark 2.20.1: the strong-convexity correction in `(2.3.8)` is nonnegative when
`μ ≥ 0`. -/
lemma strong_objective_correction_nonneg
    (hμ : 0 ≤ μ) :
    0 ≤ (μ / 2) * ‖xk - yK‖ ^ (2 : ℕ) := by
  -- Both the strong-convexity coefficient and the squared norm factor are nonnegative.
  have hμ_half : 0 ≤ μ / 2 := by
    nlinarith
  have hsq : 0 ≤ ‖xk - yK‖ ^ (2 : ℕ) := by
    positivity
  exact mul_nonneg hμ_half hsq

/-- Helper for Remark 2.20.1: the strong lower model `(2.3.8)` implies the μ-free lower model
used by the owner estimate-sequence theorem. -/
lemma strong_objective_lower_implies_objective_lower
    (hμ : 0 ≤ μ)
    (hobjective_lower : f xk ≥ strongObjectiveLowerRhs) :
    f xk ≥
      f (gradientStep f yK L) +
        inner ℝ (∇ f yK) (xk - yK) +
        (1 / (2 * (L : ℝ))) * ‖∇ f yK‖ ^ (2 : ℕ) := by
  -- Drop the nonnegative strong-convexity correction from the right-hand side.
  have hcorrection :
      0 ≤ (μ / 2) * ‖xk - yK‖ ^ (2 : ℕ) :=
    strong_objective_correction_nonneg
      (μ := μ) (y := y) (k := k) (xk := xk) hμ
  nlinarith [hobjective_lower, hcorrection]

/-- Remark 2.20.1: if `φ_k^* ≥ f(x_k)` and the whole-space lower model `(2.3.8)` holds at `y_k`,
then the next estimate-sequence value satisfies the textbook whole-space lower bound `(2.3.10)`. -/
-- Proof sketch: first drop the nonnegative strong-convexity term from `strongObjectiveLowerRhs`
-- using `hμ`; then specialize
-- `simple_set_phi_star_lower_bound_of_objective_lower_bound` to `Q = Set.univ` and rewrite the
-- projected-gradient terms using `gradientMapping_univ_eq_gradient_step` and
-- `reducedGradient_univ_eq_gradient`.
theorem whole_space_phi_star_lower_bound_of_strong_objective_lower_bound
    (halpha_k : α k ≤ 1)
    (htransportCoeff : 0 ≤ transportCoeff)
    (hμ : 0 ≤ μ)
    (hphi_k : f xk ≤ phiK)
    (hobjective_lower : f xk ≥ strongObjectiveLowerRhs) :
    phiKp1 ≥ finalRhs := by
  -- First weaken `(2.3.8)` to the μ-free lower bound consumed by the owner theorem.
  have hobjective_lower' :
      f xk ≥
        f (gradientStep f yK L) +
          inner ℝ (∇ f yK) (xk - yK) +
          (1 / (2 * (L : ℝ))) * ‖∇ f yK‖ ^ (2 : ℕ) :=
    strong_objective_lower_implies_objective_lower
      (f := f) (μ := μ) (L := L) (y := y) (k := k) (xk := xk) hμ hobjective_lower
  -- Rewrite the weakened lower model back to the owner theorem's `x_Q` / `g_Q` notation.
  have hobjective_lower_owner :
      f xk ≥
        f (x_Q[(Set.univ : Set E); Set.univ_nonempty; isClosed_univ; convex_univ | f; L](yK)) +
          inner ℝ
            (g_Q[(Set.univ : Set E); Set.univ_nonempty; isClosed_univ; convex_univ | f; L](yK))
            (xk - yK) +
          (1 / (2 * (L : ℝ))) *
            ‖g_Q[(Set.univ : Set E); Set.univ_nonempty; isClosed_univ; convex_univ | f; L](yK)‖ ^
              (2 : ℕ) := by
    simpa [gradientMapping_univ_eq_gradient_step, reducedGradient_univ_eq_gradient] using
      hobjective_lower'
  -- Then specialize the set-level owner theorem to `Q = Set.univ` and rewrite to the whole-space
  -- `gradientStep` / `∇` surface form `(2.3.10)`.
  have howner :=
    simple_set_phi_star_lower_bound_of_objective_lower_bound
      (Q := (Set.univ : Set E))
      (hQ_nonempty := Set.univ_nonempty)
      (hQ_closed := isClosed_univ)
      (hQ_convex := convex_univ)
      (f := f) (x0 := x0) (μ := μ) (L := L) (gamma0 := gamma0) (y := y) (α := α)
      (k := k) (xk := xk)
      halpha_k htransportCoeff hμ hphi_k hobjective_lower_owner
  simpa [gradientMapping_univ_eq_gradient_step, reducedGradient_univ_eq_gradient] using howner

end

/-! ### Definition_2_20 (from Chap02) -/
noncomputable section

universe u

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Primary domain: smooth unconstrained minimization on `ℝⁿ`.

Sampled owner-style declarations:
* `IsStrongConvexSmoothObjective` in `Definition_2_17`, the positive-`μ` owner predicate;
* `ConvexC1SeminormSmooth (normSeminorm ℝ E) L f` in `Theorem_2_5`, the `μ = 0`
  smooth-convex owner predicate;
* `IsMinOn f Set.univ xStar` together with `isMinOn_univ_iff`, the canonical whole-space
  minimizer owner and its textbook inequality view;
* `SetConstrainedMinimizationProblem.optimalValue` in `Chap01/Definition_1_3_7`, the canonical
  owner for the attained optimal value `f^*`.

Best owner abstraction:
* source-facing: the objective `f : E → ℝ`, together with either `f ∈ 𝓢[μ, L]¹¹` when `0 < μ`
  or `f ∈ 𝓕[L, p]¹¹` when `μ = 0`, and the whole-space minimizer predicate
  `IsMinOn f Set.univ xStar`;
* core/canonical: `SetConstrainedMinimizationProblem.unconstrained f` for the associated
  unconstrained problem, plus `IsMinOn f Set.univ xStar` for an optimal solution;
* bridge/view: the owner-namespace unconstrained specialization
  `SetConstrainedMinimizationProblem.unconstrained_optimalValue_eq_of_isMinOn`.

Primitive data:
* the objective `f : E → ℝ`;
* optionally, an optimizer `xStar : E` with `IsMinOn f Set.univ xStar`.

Derived API:
* the whole-space problem owner `SetConstrainedMinimizationProblem.unconstrained f`;
* the textbook inequality form `∀ x, f xStar ≤ f x` from `isMinOn_univ_iff`;
* the attained optimal value identity from the owner-namespace theorem
  `SetConstrainedMinimizationProblem.unconstrained_optimalValue_eq_of_isMinOn`.

Definition 2.20 therefore reuses the canonical whole-space minimization owner from Chapter 1 and
the canonical whole-space minimizer predicate from mathlib, instead of introducing a parallel
`SmoothMinimizationProblem` wrapper or an alias for “optimal solution”. -/

section ProblemOwner

variable (f : E → ℝ)

/-- Definition 2.20: for a smooth convex objective `f ∈ 𝓕[L, p]¹¹` or a strongly convex smooth
objective `f ∈ 𝓢[μ, L]¹¹`, the associated unconstrained minimization problem
`min_{x ∈ ℝⁿ} f(x)` is the canonical whole-space owner
`SetConstrainedMinimizationProblem.unconstrained f`. If `xStar` satisfies
`IsMinOn f Set.univ xStar`, then `xStar` is an optimal solution and the optimal value is given by
the companion theorem
`SetConstrainedMinimizationProblem.unconstrained_optimalValue_eq_of_isMinOn`. -/
theorem associated_unconstrained_problem_eq_unconstrained :
    ({ feasibleSet := Set.univ, objective := f } : SetConstrainedMinimizationProblem E) =
      SetConstrainedMinimizationProblem.unconstrained f :=
  rfl

end ProblemOwner

namespace SetConstrainedMinimizationProblem

variable {X : Type u} (f : X → ℝ) {xStar : X}

/-- Helper for Definition 2.20: every ambient point is feasible for the unconstrained
minimization problem associated with `f`. -/
theorem mem_unconstrained_feasibleSet (x : X) :
    x ∈ (unconstrained f).feasibleSet := by
  -- The unconstrained feasible region is the whole ambient space.
  simp [unconstrained_feasibleSet]

/-- The unconstrained owner optimal value is the attained value `f xStar` whenever `xStar`
minimizes `f` on all of the ambient space. -/
-- Proof sketch: package `f` as the Chapter 1 whole-space problem on `Set.univ`, apply
-- `SetConstrainedMinimizationProblem.optimalValue_eq_of_isMinOn`, and simplify the trivial
-- feasibility witness `xStar ∈ Set.univ`.
theorem unconstrained_optimalValue_eq_of_isMinOn
    (hmin : IsMinOn f Set.univ xStar) :
    (unconstrained f).optimalValue = (f xStar : EReal) := by
  -- Any ambient point is feasible for the whole-space owner.
  have hxStar : xStar ∈ (unconstrained f).feasibleSet :=
    mem_unconstrained_feasibleSet (f := f) xStar
  -- Apply the Chapter 1 attained-optimal-value theorem to the whole-space owner.
  simpa using
    (unconstrained f).optimalValue_eq_of_isMinOn hxStar hmin

end SetConstrainedMinimizationProblem

/-! ### Lemma_2_20 (from Chap02) -/
open scoped Gradient ProjectedGradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Lemma 2.20 lies in the whole-space specialization of the simple-set estimating-sequence domain
on a complete real inner-product space. The textbook `ℝⁿ` statement is the specialization
`E = EuclideanSpace ℝ (Fin n)`.

Owner declarations sampled for this refinement:
* `simpleSetEstimatingModel` in `Proposition_2_22`, the owner lower model over a closed convex
  feasible set;
* `simpleSetEstimatingFunction`, `simpleSetEstimatingCenter`, and `simpleSetEstimatingValue` in
  `Proposition_2_22`, the owner recursive estimating-sequence objects in canonical quadratic form;
* `simpleSetEstimatingFunction_eq_canonicalQuadratic` and
  `simpleSetEstimatingFunction_eq_canonicalQuadratic_apply` in `Proposition_2_22`, the owner
  centered-quadratic function identity and its pointwise companion;
* `gradientMapping_univ_eq_gradient_step` and `reducedGradient_univ_eq_gradient` in
  `Remark_2_35_1`, the chapter's canonical whole-space bridge from projected-gradient stage data
  to the unconstrained `gradientStep` / `∇ f` formulas.

Best owner abstraction:
* source-facing: the textbook whole-space formulas obtained by specializing the simple-set owners
  to `Q = Set.univ`;
* core/canonical: `simpleSetEstimatingModel`, `simpleSetEstimatingFunction`,
  `simpleSetEstimatingCenter`, `simpleSetEstimatingValue`, and
  `simpleSetEstimatingFunction_eq_canonicalQuadratic_apply`;
* bridge/view: the ordinary specialization `Q = Set.univ`, simplified through
  `gradientMapping_univ_eq_gradient_step` and `reducedGradient_univ_eq_gradient`.

Primitive data:
* the objective `f`, initial point `x0`, parameters `(μ, L, γ₀)`, and stage data `(y, α)`;
* the nonvanishing hypothesis on the owner curvature sequence.

Derived API:
* the whole-space lower-model formula rewritten to `gradientStep` / `∇ f`;
* the whole-space recursive estimating-function and scalar-value families;
* the whole-space centered-quadratic identity.

The previous file duplicated these declarations with separate `smoothEstimating...` names. Those
definitions were exact `Set.univ` specializations of the owner simple-set API, so this file now
keeps only the specialization layer and reuses the canonical owner declarations directly. -/

recall simpleSetEstimatingModel
recall simpleSetEstimatingModel_apply
recall simpleSetEstimatingFunction
recall simpleSetEstimatingCenter
recall simpleSetEstimatingValue
recall simpleSetEstimatingFunction_eq_canonicalQuadratic
recall simpleSetEstimatingFunction_eq_canonicalQuadratic_apply

section

variable
    (f : E → ℝ) (x0 : E)
    (μ : ℝ) (L : NNRealˣ) (gamma0 : ℝ)
    (y : ℕ → E) (alpha : ℕ → ℝ)
    (k : ℕ) (x : E)

local notation "univSet" => (Set.univ : Set E)

local notation "model" =>
  simpleSetEstimatingModel
    univSet Set.univ_nonempty isClosed_univ convex_univ
    f μ L y

local notation "phi" =>
  simpleSetEstimatingFunction
    univSet Set.univ_nonempty isClosed_univ convex_univ
    f x0 μ L gamma0 y alpha

local notation "center" =>
  simpleSetEstimatingCenter
    univSet Set.univ_nonempty isClosed_univ convex_univ
    f x0 μ L gamma0 y alpha

local notation "phiStar" =>
  simpleSetEstimatingValue
    univSet Set.univ_nonempty isClosed_univ convex_univ
    f x0 μ L gamma0 y alpha

#check (model k : E → ℝ)

#check (phi : ℕ → E → ℝ)

#check (center : ℕ → E)

#check (phiStar : ℕ → ℝ)

/-- Lemma 2.20: specializing the simple-set lower model to the whole space rewrites the projected
step data as the exact gradient step `gradientStep f (y k) L` and gradient `∇ f (y k)`. -/
theorem whole_space_simpleSetEstimatingModel_apply :
    model k x =
      let yk := y k
      f (gradientStep f yk L) +
        (1 / (2 * L)) * ‖∇ f yk‖ ^ (2 : ℕ) +
        inner ℝ (∇ f yk) (x - yk) +
        (μ / 2) * ‖x - yk‖ ^ (2 : ℕ) := by
  simp [simpleSetEstimatingModel_apply, gradientMapping_univ_eq_gradient_step,
    reducedGradient_univ_eq_gradient]

/-- Lemma 2.20: the whole-space estimating-sequence function keeps the canonical centered
quadratic form from Proposition 2.22. -/
theorem whole_space_simpleSetEstimatingFunction_eq_canonicalQuadratic_apply
    (hγ : ∀ k, estimatingSequenceCurvature μ gamma0 alpha (k + 1) ≠ 0) :
    phi k x =
      phiStar k +
        (estimatingSequenceCurvature μ gamma0 alpha k / 2) *
          ‖x - center k‖ ^ (2 : ℕ) :=
  simpleSetEstimatingFunction_eq_canonicalQuadratic_apply
    univSet Set.univ_nonempty isClosed_univ convex_univ
    f x0 μ L gamma0 y alpha hγ k x

end

/-! ### Proposition_2_20 (from Chap02) -/
open scoped Gradient
open scoped PrimalEqualityConstrainedProblem.LagrangianMinimizerSelectionNotation

noncomputable section

universe u v

/- Primary domain: equality-constrained Lagrangian duality with a chosen minimizing primal
selection.

Owner declarations sampled before refining this file:
* `LagrangianProblem.lagrangianMinimizers` and `LagrangianProblem.dualFunction` in
  `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_10_2.lean`;
* `PrimalEqualityConstrainedProblem.lagrangian`, `dualFunction`, `constraintResidual`, and
  `mem_equalityFeasibleSet_iff` in `LecturesConvexOptimization_Nesterov_2018/Chap02/Definition_2_30.lean`;
* `PrimalEqualityConstrainedProblem.LagrangianMinimizerSelection`, together with the derived
  equality-problem API `LagrangianMinimizerSelection.isMinOn` and
  `LagrangianMinimizerSelection.dualFunction_eq_lagrangian`, in
  `LecturesConvexOptimization_Nesterov_2018/Chap02/Definition_2_31.lean`;
* mathlib `HasGradientAt.unique` and `IsLocalMax.fderiv_eq_zero`, which give the canonical local
  stationary-point bridge at a dual maximizer.

Best owner abstraction: the primitive selected data are a
`LagrangianMinimizerSelection problem` over the equality problem's own Lagrangian layer, not an
independent function `x : Λ → problem.basicSet` plus separate minimizer proofs.

Primitive data here are `problem`, a minimizing selection `selection`, and the multiplier `uStar`.
The residual, the selected dual profile
`u ↦ problem.lagrangian (selection u) u`, the subproblem optimality
statement, and the dual-value identity are all derived API from the owner selection abstraction.
The pointwise stationarity input at `uStar` is most faithfully expressed by
`HasGradientAt` for that selected dual profile, not by a global equation for mathlib's total
`gradient`.
-/

namespace PrimalEqualityConstrainedProblem
namespace LagrangianMinimizerSelection

variable {E : Type u} {Λ : Type v} [AddCommMonoid E] [Module ℝ E]
variable [NormedAddCommGroup Λ] [InnerProductSpace ℝ Λ]
variable {problem : PrimalEqualityConstrainedProblem E Λ}
variable (selection : LagrangianMinimizerSelection problem)

local notation "Q₌" => problem.equalityFeasibleSet
local notation "φ" => φ[selection]
local notation "g" => g[selection]

/-- The owner-facing core of Proposition 2.20: if the selected dual residual vanishes at `uStar`,
then the selected minimizer is feasible and minimizes the primal objective on the feasible set. -/
-- Proof sketch: `dualResidual selection uStar = 0` is exactly the equality-constraint residual
-- vanishing at `selection uStar`, hence `selection uStar` is feasible. For any feasible `y`, the
-- minimizer property `isMinOn selection uStar` compares the two Lagrangian values at
-- `selection uStar` and `y`; feasibility removes the multiplier term on both sides, leaving the
-- desired objective comparison on the owner feasible set.
theorem isMinOn_feasibleSet_of_dualResidual_eq_zero
    {uStar : Λ}
    (hresidual : g uStar = 0) :
    (selection uStar : E) ∈ Q₌ ∧
      IsMinOn problem Q₌ (selection uStar) := by
  have hselection_mem :
      (selection uStar : E) ∈ problem.feasibleSet :=
    (problem.mem_lagrangianMinimizers_iff.mp (selection uStar).2).1
  have hfeasible : (selection uStar : E) ∈ Q₌ := by
    rw [problem.mem_equalityFeasibleSet_iff_constraintResidual_eq_zero]
    exact ⟨hselection_mem, hresidual⟩
  have hmin := selection.isMinOn uStar
  rw [isMinOn_iff] at hmin ⊢
  constructor
  · exact hfeasible
  · intro y hy
    have hy' := problem.mem_equalityFeasibleSet_iff_constraintResidual_eq_zero.mp hy
    have hselectedResidual :
        problem.constraintResidual (selection uStar) = 0 := hresidual
    simpa [PrimalEqualityConstrainedProblem.lagrangian, hselectedResidual, hy'.2] using
      hmin y hy'.1

/-- At a feasible selected minimizer, the equality-constraint term in the selected dual profile
vanishes, so the selected dual profile equals the primal objective. -/
-- Proof sketch: feasibility of `selection u` is equivalent to vanishing constraint residual, and
-- substituting this into the owner Lagrangian formula removes the multiplier term.
theorem selectedDualProfile_eq_objective_of_mem_feasibleSet
    {u : Λ}
    (hfeasible : (selection u : E) ∈ Q₌) :
    φ u = problem (selection u) := by
  have hg :
      g u = 0 :=
    (problem.mem_equalityFeasibleSet_iff_constraintResidual_eq_zero.mp hfeasible).2
  simpa [hg] using selection.selectedDualProfile_eq_objective_add_inner_dualResidual u

section StationaryPoint

variable [CompleteSpace Λ]

/-- Proposition 2.20 in textbook form: if the canonical selected dual profile
`selection.selectedDualProfile` is maximized at `uStar` and has gradient there equal to the
dual residual, then the selected minimizer at `uStar` solves the primal problem. -/
-- Proof sketch: a global maximizer on `Set.univ` is a local maximizer, so Fermat's theorem and
-- the local differentiability packaged by `hprofile_grad` give a zero gradient witness at `uStar`.
-- Uniqueness of gradients identifies `dualResidual selection uStar = 0`, and the core residual
-- theorem then yields feasibility and primal optimality of `selection uStar`.
theorem isMinOn_feasibleSet_of_dualOptimal
    {uStar : Λ}
    (huStar : IsMaxOn φ Set.univ uStar)
    (hprofile_grad : HasGradientAt φ (g uStar) uStar) :
    (selection uStar : E) ∈ Q₌ ∧
      IsMinOn problem Q₌ (selection uStar) := by
  have hlocalMax : IsLocalMax φ uStar := huStar.isLocalMax (by simp)
  have hfderiv := (hasGradientAt_iff_hasFDerivAt.mp hprofile_grad)
  have hfrechet_zero : (InnerProductSpace.toDual ℝ Λ) (g uStar) = 0 :=
    hlocalMax.hasFDerivAt_eq_zero hfderiv
  have hgradient_zero : HasGradientAt φ (0 : Λ) uStar := by
    have hfderiv_zero : HasFDerivAt φ (0 : StrongDual ℝ Λ) uStar := by
      simpa [hfrechet_zero] using hfderiv
    simpa using hfderiv_zero.hasGradientAt
  have hresidual_zero : g uStar = 0 :=
    HasGradientAt.unique hprofile_grad hgradient_zero
  exact selection.isMinOn_feasibleSet_of_dualResidual_eq_zero hresidual_zero

/-- Companion reformulation of Proposition 2.20 using mathlib's total `gradient` at the single
point `uStar`: differentiability at `uStar` upgrades the pointwise identity
`∇ φ(uStar) = selection.dualResidual uStar` to the `HasGradientAt` hypothesis used by the main
theorem. -/
-- Proof sketch: differentiability identifies the total gradient with the unique pointwise
-- gradient, so the assumed gradient identity converts directly into the `HasGradientAt` input of
-- the main proposition.
theorem isMinOn_feasibleSet_of_dualOptimal_of_gradient_eq_dualResidual
    {uStar : Λ}
    (huStar : IsMaxOn φ Set.univ uStar)
    (hprofile_diff : DifferentiableAt ℝ φ uStar)
    (hprofile_grad : ∇ φ uStar = g uStar) :
    (selection uStar : E) ∈ Q₌ ∧
      IsMinOn problem Q₌ (selection uStar) := by
  exact selection.isMinOn_feasibleSet_of_dualOptimal huStar <|
    by simpa [hprofile_grad] using hprofile_diff.hasGradientAt

end StationaryPoint

/-- Once the selected point is known to minimize the primal problem, strong duality identifies the
primal optimal value with the dual value and the recovered primal objective value. -/
-- Proof sketch: from the primal optimality statement, `selection uStar` lies in the feasible set
-- and attains the infimum defining `primalOptimalValue`. The identity
-- `dualFunction_eq_lagrangian selection uStar` rewrites the dual value as the Lagrangian value at
-- `selection uStar`, and feasibility removes the multiplier term, giving the objective value.
theorem primalOptimalValue_eq_dualFunction_eq_objective_of_isMinOn_feasibleSet
    {uStar : Λ}
    (hoptimal :
      (selection uStar : E) ∈ Q₌ ∧
        IsMinOn problem Q₌ (selection uStar)) :
    problem.primalOptimalValue = problem.dualFunction uStar ∧
      problem.dualFunction uStar =
        (problem (selection uStar) : EReal) := by
  have hprimal :
      problem.primalOptimalValue = (problem (selection uStar) : EReal) :=
    problem.primalProblem.optimalValue_eq_of_isMinOn hoptimal.1 hoptimal.2
  have hdual :
      problem.dualFunction uStar = (problem (selection uStar) : EReal) := by
    calc
      problem.dualFunction uStar = (φ uStar : EReal) :=
        selection.dualFunction_eq_selectedDualProfile uStar
      _ = (problem (selection uStar) : EReal) := by
        exact_mod_cast selection.selectedDualProfile_eq_objective_of_mem_feasibleSet hoptimal.1
  constructor
  · rw [hprimal, hdual]
  · exact hdual

end LagrangianMinimizerSelection
end PrimalEqualityConstrainedProblem

/-! ### Theorem_2_20 (from Chap02) -/
open scoped Gradient StrongConvexSmooth

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain: strongly convex optimal-method objective-gap rates on a real Hilbert space.

Owner declarations sampled before refining this file:
* `GeneralOptimalMethodScheme` in `Algorithm_2_2` owns the optimal-method trajectory together
  with the canonical scalar sequences `αₖ`, `γₖ`, and `λₖ`;
* `OptimalMethodRecurrence.weight_bounds` in `Lemma_2_10` owns the hyperbolic and quadratic
  bounds on the canonical weight `λₖ` for `γ₀ ∈ (μ, 3L + μ]`;
* `OptimalMethodRecurrence.hyperbolic_bound_le_quadratic_bound` in `Lemma_2_10` owns the scalar
  hyperbolic-versus-quadratic factor comparison on the recurrence side;
* `estimating_sequence_suboptimality_le` in `Theorem_2_19` owns the estimating-sequence
  objective-gap estimate;
* the owner-style summary in `Definition_2_20` identifies whole-space strong convexity,
  `C¹` regularity, and gradient Lipschitzness as the primitive objective data in Chapter 2.

Best owner abstraction: the public object here is the owner method
`method : GeneralOptimalMethodScheme ... (3 * L + μ)`. The explicit hyperbolic and quadratic
right-hand sides are derived by combining the owner suboptimality theorem with the owner weight
bound, so this file states those rates directly rather than keeping parallel local bound
definitions.

Primitive data:
* the objective and its whole-space strong-convexity / smoothness hypotheses;
* a minimizer `xStar`;
* the owner method with `γ₀ = 3L + μ`.

Derived API:
* the explicit quadratic objective-gap estimate;
* the explicit hyperbolic objective-gap estimate;
* the comparison of the two displayed right-hand sides. -/

section OptimalMethodRates

variable {μ L gamma0 : ℝ} {f : E → ℝ}
variable {xStar : E}
variable {x0 : E}

/-- For any optimal-method scheme with `μ > 0` and initial curvature `γ₀ ∈ (μ, 3L + μ]`, the
objective gap is bounded above by the corresponding hyperbolic estimate with the canonical initial
energy `f(x₀) - f(x*) + (γ₀ / 2) ‖x₀ - x*‖²`. -/
theorem optimal_method_hyperbolic_suboptimality_le_of_mem_Ioc
    (method : GeneralOptimalMethodScheme f L μ x0 gamma0)
    (hf : f ∈ 𝓢[μ, L]¹¹)
    (hxStar : IsMinOn f Set.univ xStar)
    (hgamma0 : gamma0 ∈ Set.Ioc μ (3 * L + μ))
    (k : ℕ) :
    f (method k) - f xStar ≤
      (4 * μ *
        (f x0 - f xStar + (gamma0 / 2) * ‖x0 - xStar‖ ^ (2 : ℕ))) /
        ((gamma0 - μ) *
          (Real.exp (((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]) -
            Real.exp (-(((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]))) ^
            (2 : ℕ)) := by
  sorry

/-- For any optimal-method scheme with `μ > 0` and initial curvature `γ₀ ∈ (μ, 3L + μ]`, the
hyperbolic estimate yields the quadratic `O((k + 1)⁻²)` objective-gap upper bound with the same
canonical initial energy. -/
theorem optimal_method_quadratic_suboptimality_le_of_mem_Ioc
    (method : GeneralOptimalMethodScheme f L μ x0 gamma0)
    (hf : f ∈ 𝓢[μ, L]¹¹)
    (hxStar : IsMinOn f Set.univ xStar)
    (hgamma0 : gamma0 ∈ Set.Ioc μ (3 * L + μ))
    (k : ℕ) :
    f (method k) - f xStar ≤
      (4 * L / ((gamma0 - μ) * (k + 1 : ℝ) ^ (2 : ℕ))) *
        (f x0 - f xStar + (gamma0 / 2) * ‖x0 - xStar‖ ^ (2 : ℕ)) := by
  sorry

/-- Helper for Theorem 2.20: the hyperbolic factor is bounded above by the quadratic factor after
rewriting the denominator through `sinh`.

This is the scalar comparison underlying
`OptimalMethodRecurrence.hyperbolic_bound_le_quadratic_bound`, but without the recurrence-side
restriction `q_f ∈ (0, 1)`. -/
-- Proof sketch: write `exp t - exp (-t) = 2 sinh t` with
-- `t = ((k + 1) / 2) * sqrt q_f`, use `t ≤ sinh t` for `t ≥ 0`, square both sides, and then
-- rewrite `q_f = μ / L`.
lemma optimal_method_hyperbolic_factor_le_quadratic_factor
    (hμ : 0 < μ) (hL : 0 < L) (k : ℕ) :
    μ /
        (Real.exp (((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]) -
          Real.exp (-(((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]))) ^ (2 : ℕ) ≤
      L / (k + 1 : ℝ) ^ (2 : ℕ) := by
  let qμL : ℝ := μ / L
  let t : ℝ := ((k + 1 : ℝ) / 2) * Real.sqrt qμL
  let d : ℝ := Real.exp t - Real.exp (-t)
  have hq_nonneg : 0 ≤ qμL := div_nonneg hμ.le hL.le
  have ht_nonneg : 0 ≤ t := by
    dsimp [t]
    positivity
  have htsinh : t ≤ Real.sinh t := (Real.self_le_sinh_iff).2 ht_nonneg
  have hsinh_sq :
      t ^ (2 : ℕ) ≤ Real.sinh t ^ (2 : ℕ) := by
    have hsinh_nonneg : 0 ≤ Real.sinh t := (Real.sinh_nonneg_iff).2 ht_nonneg
    nlinarith
  have hqf_sq :
      qμL * (k + 1 : ℝ) ^ (2 : ℕ) = 4 * t ^ (2 : ℕ) := by
    dsimp [t]
    nlinarith [Real.sq_sqrt hq_nonneg]
  have hd_sq :
      d ^ (2 : ℕ) = 4 * Real.sinh t ^ (2 : ℕ) := by
    dsimp [d]
    rw [Real.sinh_eq]
    ring
  have hfactor :
      qμL * (k + 1 : ℝ) ^ (2 : ℕ) ≤ d ^ (2 : ℕ) := by
    calc
      qμL * (k + 1 : ℝ) ^ (2 : ℕ) = 4 * t ^ (2 : ℕ) := hqf_sq
      _ ≤ 4 * Real.sinh t ^ (2 : ℕ) := by
            gcongr
      _ = d ^ (2 : ℕ) := hd_sq.symm
  have hmul :
      μ * (k + 1 : ℝ) ^ (2 : ℕ) ≤ L * d ^ (2 : ℕ) := by
    have hscaled := mul_le_mul_of_nonneg_left hfactor hL.le
    calc
      μ * (k + 1 : ℝ) ^ (2 : ℕ) = L * (qμL * (k + 1 : ℝ) ^ (2 : ℕ)) := by
        dsimp [qμL]
        field_simp [hL.ne']
      _ ≤ L * d ^ (2 : ℕ) := hscaled
  have hd_pos : 0 < d := by
    dsimp [d]
    have ht_pos : 0 < t := by
      dsimp [t]
      positivity
    refine sub_pos.mpr ?_
    exact Real.exp_lt_exp.mpr (by linarith)
  have hk_sq_pos : 0 < (k + 1 : ℝ) ^ (2 : ℕ) := by
    positivity
  refine (div_le_div_iff₀ (by positivity) hk_sq_pos).2 ?_
  simpa [d, t, qμL, mul_assoc, mul_left_comm, mul_comm] using hmul

variable {x0 : E}

/-- Theorem 2.20 (1): for a smooth strongly convex minimization problem with `γ₀ = 3L + μ`, the
iterate sequence of the optimal method satisfies the `O((k + 1)⁻²)` function-value bound. -/
-- Proof sketch: apply `estimating_sequence_suboptimality_le` to the owner estimating sequence
-- attached to `method`. Then use `OptimalMethodRecurrence.weight_bounds` specialized to
-- `γ₀ = 3L + μ` to bound the canonical weight `λₖ`, and bound the initial energy by the smooth
-- upper quadratic estimate at the minimizer `xStar`.
theorem optimal_method_quadratic_suboptimality_le
    (method : GeneralOptimalMethodScheme f L μ x0 (3 * L + μ))
    (hf : f ∈ 𝓢[μ, L]¹¹)
    (hxStar : IsMinOn f Set.univ xStar)
    (k : ℕ) :
    f (method k) - f xStar ≤
      (2 * (4 + q[μ, L]) * L * ‖x0 - xStar‖ ^ (2 : ℕ)) /
        (3 * (k + 1 : ℝ) ^ (2 : ℕ)) := by
  sorry

/-- Theorem 2.20 (2): if `μ > 0`, then the iterate sequence of the optimal method satisfies the
sharper hyperbolic function-value estimate. -/
-- Proof sketch: combine `estimating_sequence_suboptimality_le` with the positive-`μ` upper bound
-- on the owner weight `λₖ` from `OptimalMethodRecurrence.weight_bounds` specialized to
-- `γ₀ = 3L + μ`, and rewrite the resulting factor using `q[μ, L] = μ / L`.
theorem optimal_method_hyperbolic_suboptimality_le
    (method : GeneralOptimalMethodScheme f L μ x0 (3 * L + μ))
    (hf : f ∈ 𝓢[μ, L]¹¹)
    (hxStar : IsMinOn f Set.univ xStar)
    (k : ℕ) :
    f (method k) - f xStar ≤
      (2 * (4 + q[μ, L]) * μ * ‖x0 - xStar‖ ^ (2 : ℕ)) /
        (3 *
          (Real.exp (((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]) -
            Real.exp (-(((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]))) ^ (2 : ℕ)) := by
  sorry

end OptimalMethodRates

section ExplicitBoundComparison

variable {F : Type u} [NormedAddCommGroup F]
variable {μ L : ℝ}

/-- Theorem 2.20 (3): for `μ > 0`, the hyperbolic upper bound from the optimal-method estimate is
itself bounded above by the quadratic `O((k + 1)⁻²)` bound. -/
-- Proof sketch: compare the hyperbolic denominator with its quadratic lower bound from the scalar
-- recurrence analysis for the owner weights, equivalently the second inequality in
-- `OptimalMethodRecurrence.weight_bounds` specialized to `γ₀ = 3L + μ`.
theorem optimal_method_hyperbolic_bound_le_quadratic_bound
    (hμ : 0 < μ) (hL : 0 < L)
    (x0 xStar : F)
    (k : ℕ) :
    (2 * (4 + q[μ, L]) * μ * ‖x0 - xStar‖ ^ (2 : ℕ)) /
        (3 *
          (Real.exp (((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]) -
            Real.exp (-(((k + 1 : ℝ) / 2) * Real.sqrt q[μ, L]))) ^ (2 : ℕ)) ≤
      (2 * (4 + q[μ, L]) * L * ‖x0 - xStar‖ ^ (2 : ℕ)) /
        (3 * (k + 1 : ℝ) ^ (2 : ℕ)) := by
  let c : ℝ := (2 * (4 + q[μ, L]) * ‖x0 - xStar‖ ^ (2 : ℕ)) / 3
  have hbase :=
    optimal_method_hyperbolic_factor_le_quadratic_factor hμ hL k
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hbase hc_nonneg
  simpa [c, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled

end ExplicitBoundComparison

end
