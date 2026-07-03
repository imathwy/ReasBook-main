

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_8 (from Chap02) -/
open scoped Gradient SmoothConvex

noncomputable section

universe u

variable (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]

local notation "p" => normSeminorm ℝ E
local notation "SmoothObjective[" L "]" => { f : E → ℝ // f ∈ 𝓕[L, p]¹¹ }

local instance smoothObjectiveCoeFun {L : NNReal} :
    CoeFun (SmoothObjective[L]) (fun _ ↦ E → ℝ) where
  coe f := f.1

/- Definition 2.8 lies in the chapter's smooth convex first-order black-box domain on a real
finite-dimensional inner-product space.

Sampled owner-style declarations:
* `BlackBoxOptimizationProblemClass` in `Chap01/Definition_1_2_4`, the Chapter 1 owner of the
  model/oracle/stopping-criterion triple;
* `OptimizationOracle.IsLocal` in `Chap01/Definition_1_2_13`, the owner locality predicate for a
  class oracle;
* `SetConstrainedMinimizationProblem.unconstrained` and
  `SetConstrainedMinimizationProblem.IsApproximateMinimizer` in Chapter 1, the canonical owner
  bridge from an unconstrained objective to the `ε`-approximate-solution condition;
* `ConvexC1SeminormSmooth.gradient_lipschitz` in `Theorem_2_5`, the derived gradient-Lipschitz
  view of the objective-side owner `f ∈ 𝓕[L, p]¹¹`.

Best owner abstraction:
* source-facing: the smooth convex first-order black-box problem class at accuracy `ε`;
* core/canonical: `BlackBoxOptimizationProblemClass` with model
  `{f : E → ℝ // f ∈ 𝓕[L, p]¹¹}`;
* bridge/view: the Chapter 1 unconstrained approximate-minimizer predicate and the locality
  theorem for the owner oracle.

Primitive data:
* the ambient real finite-dimensional inner-product space `E`;
* the smoothness constant `L : NNReal`;
* the accuracy threshold `ε : ℝ`.

Derived API:
* the model subtype of objectives in `𝓕[L, p]¹¹`;
* the first-order oracle reply `(f x, ∇ f x)`;
* the stopping criterion expressed through
  `SetConstrainedMinimizationProblem.unconstrained f`;
* the locality bridge for the owner oracle.

Source/core/bridge triage:
* source-facing: `smoothConvexProblemClass L ε`;
* core/canonical: `BlackBoxOptimizationProblemClass` and the smooth-objective subtype
  `{f : E → ℝ // f ∈ 𝓕[L, p]¹¹}`;
* bridge/view:
  `SetConstrainedMinimizationProblem.unconstrained_isApproximateMinimizer_iff_sub_le` and
  `smoothConvexProblemClass_oracle_isLocal`.

Definition 2.8 is therefore refined to the actual Chapter 1 problem-class owner rather than a
list of recalled ingredients. The textbook objective-gap stopping condition is kept as a thin
bridge theorem, not as separate primitive data. -/

section ProblemClass

variable (L : NNReal) (ε : ℝ)

/-- Definition 2.8: the smooth convex first-order black-box class on a real finite-dimensional
inner-product space `E` at smoothness constant `L` and accuracy `ε`. Its model is the subtype of
smooth convex objectives
`f ∈ 𝓕[L, p]¹¹`, its oracle returns the value-gradient reply `(f x, ∇ f x)`, and its stopping
criterion accepts exactly those pairs `(f, x̄)` for which `x̄` is an `ε`-approximate minimizer of
the canonical unconstrained Chapter 1 problem attached to `f`. The textbook `ℝⁿ` statement is the
specialization `E = EuclideanSpace ℝ (Fin n)`. -/
def smoothConvexProblemClass :
    BlackBoxOptimizationProblemClass E (ℝ × E) (SmoothObjective[L] × E) where
  model := SmoothObjective[L]
  oracle := fun f x ↦ (f x, ∇ f x)
  stoppingCriterion := { state | let ⟨f, xBar⟩ := state
    (SetConstrainedMinimizationProblem.unconstrained f).IsApproximateMinimizer ε xBar }

/-- The oracle of `smoothConvexProblemClass L ε` is the canonical first-order reply
`(f, x) ↦ (f x, ∇ f x)`. -/
@[simp] theorem smoothConvexProblemClass_oracle_apply
    (f : SmoothObjective[L]) (x : E) :
    (smoothConvexProblemClass E L ε).oracle f x = (f x, ∇ f x) :=
  rfl

/-- A state belongs to the stopping criterion of `smoothConvexProblemClass L ε` exactly when its
endpoint is an `ε`-approximate minimizer of the unconstrained owner problem attached to the model
objective. -/
@[simp] theorem smoothConvexProblemClass_stops_iff
    (f : SmoothObjective[L]) (xBar : E) :
    (f, xBar) ∈ (smoothConvexProblemClass E L ε).stoppingCriterion ↔
      (SetConstrainedMinimizationProblem.unconstrained f).IsApproximateMinimizer ε xBar :=
  Iff.rfl

end ProblemClass

namespace SetConstrainedMinimizationProblem

variable {X : Type u}

/-- Relative to a chosen global minimizer `x*`, the Chapter 1 unconstrained approximate-minimizer
owner is exactly the textbook objective-gap inequality `f(x̄) - f(x*) ≤ ε`. -/
theorem unconstrained_isApproximateMinimizer_iff_sub_le
    (f : X → ℝ) {xStar xBar : X} (hxStar : IsMinOn f Set.univ xStar) (ε : ℝ) :
    (unconstrained f).IsApproximateMinimizer ε xBar ↔
      f xBar - f xStar ≤ ε := by
  have hoptimalValue :
      (unconstrained f).optimalValue = (f xStar : EReal) := by
    simpa using (unconstrained f).optimalValue_eq_of_isMinOn (by simp) hxStar
  rw [(unconstrained f).isApproximateMinimizer_iff, unconstrained_feasibleSet, hoptimalValue]
  constructor
  · rintro ⟨_, happrox⟩
    refine sub_le_iff_le_add'.mpr ?_
    have happrox' : ((f xBar : ℝ) : EReal) ≤ ((f xStar + ε : ℝ) : EReal) := by
      simpa [EReal.coe_add] using happrox
    exact EReal.coe_le_coe_iff.mp happrox'
  · intro hgap
    have hgap' : f xBar ≤ f xStar + ε :=
      sub_le_iff_le_add'.mp hgap
    refine ⟨by simp, ?_⟩
    have happrox : ((f xBar : ℝ) : EReal) ≤ ((f xStar + ε : ℝ) : EReal) :=
      EReal.coe_le_coe_iff.mpr hgap'
    simpa [EReal.coe_add] using happrox

end SetConstrainedMinimizationProblem

section ProblemClassBridge

variable (L : NNReal) (ε : ℝ)

/-- The stopping rule of `smoothConvexProblemClass L ε` is exactly the textbook objective-gap
criterion once a global minimizer `x*` of the model objective has been fixed. -/
theorem smoothConvexProblemClass_stops_iff_sub_le
    (f : SmoothObjective[L]) {xStar xBar : E} (hxStar : IsMinOn f Set.univ xStar) :
    (f, xBar) ∈ (smoothConvexProblemClass E L ε).stoppingCriterion ↔
      f xBar - f xStar ≤ ε := by
  change (SetConstrainedMinimizationProblem.unconstrained f).IsApproximateMinimizer ε xBar ↔ _
  simpa using
    SetConstrainedMinimizationProblem.unconstrained_isApproximateMinimizer_iff_sub_le f hxStar ε

end ProblemClassBridge

section Locality

variable (L : NNReal) (ε : ℝ)
variable (sameDataNear : (E → ℝ) → (E → ℝ) → E → Prop)

/-- Any locality statement for the raw smooth-objective first-order reply immediately induces the
corresponding locality statement for the owner oracle of `smoothConvexProblemClass L ε`. -/
theorem smoothConvexProblemClass_oracle_isLocal
    (hlocal :
      OptimizationOracle.IsLocal
        (fun (f : SmoothObjective[L]) x ↦ (f x, ∇ f x))
        (fun (f₁ f₂ : SmoothObjective[L]) (x : E) ↦ sameDataNear f₁ f₂ x)) :
    OptimizationOracle.IsLocal
      (smoothConvexProblemClass E L ε).oracle
      (fun (f₁ f₂ : SmoothObjective[L]) (x : E) ↦ sameDataNear f₁ f₂ x) := by
  simpa using hlocal

end Locality

end

/-! ### Lemma_2_8 (from Chap02) -/
open AffineMap
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain: strongly convex estimating sequences on real inner-product spaces.

Sampled owner-style declarations in this domain:
* `IsEstimatingSequence`
* `estimatingWeight`
* `lineMap`
* `firstOrderTaylorModelAt`
* `quadraticallyRegularizedObjective`
* `StrongConvexOn.lower_tangent_quadratic_of_hasGradientAt`

Source/core/bridge triage for this file:
* source-facing: the recursive sequence `strongConvexEstimatingFunction`;
* core/canonical: `IsEstimatingSequence f φ lam`, `estimatingWeight α`, `lineMap`,
  `firstOrderTaylorModelAt`, and `quadraticallyRegularizedObjective`;
* bridge/view: the pointwise successor formula
  `strongConvexEstimatingFunction_succ_apply`.

Primitive data:
* the initial function `φ₀`;
* the recursive function sequence;
* the upstream real-valued weight sequence `estimatingWeight α`.

Derived API:
* the function-valued zero and successor equations for `strongConvexEstimatingFunction`;
* the pointwise successor expansion through the owner affine-quadratic model;
* the `NNReal` weight view `Real.toNNReal ∘ estimatingWeight α` used by
  `IsEstimatingSequence`. -/

section

variable (μ : ℝ) (f φ₀ : E → ℝ) (y : ℕ → E) (α : ℕ → ℝ)

/-- The recursively defined estimating-sequence functions in LecturesConvexOptimization_Nesterov_2018's strong-convex
construction. -/
def strongConvexEstimatingFunction
    (μ : ℝ) (f φ₀ : E → ℝ) (y : ℕ → E) (α : ℕ → ℝ) :
    ℕ → E → ℝ
  | 0 => φ₀
  | k + 1 =>
      lineMap
        (strongConvexEstimatingFunction μ f φ₀ y α k)
        (quadraticallyRegularizedObjective (firstOrderTaylorModelAt f (y k)) μ (y k))
        (α k)

/-- The estimating-sequence functions start from the initial model `φ₀`. -/
@[simp] theorem strongConvexEstimatingFunction_zero :
    strongConvexEstimatingFunction μ f φ₀ y α 0 = φ₀ := rfl

/-- The estimating-sequence functions satisfy their defining affine update with the owner
regularized first-order Taylor model. -/
theorem strongConvexEstimatingFunction_succ
    (k : ℕ) :
    strongConvexEstimatingFunction μ f φ₀ y α (k + 1) =
      lineMap
        (strongConvexEstimatingFunction μ f φ₀ y α k)
        (quadraticallyRegularizedObjective (firstOrderTaylorModelAt f (y k)) μ (y k))
        (α k) := rfl

/-- Evaluating the successor stage recovers the textbook affine-quadratic update formula. -/
@[simp] theorem strongConvexEstimatingFunction_succ_apply
    (k : ℕ) (x : E) :
    strongConvexEstimatingFunction μ f φ₀ y α (k + 1) x =
      (1 - α k) * strongConvexEstimatingFunction μ f φ₀ y α k x +
        α k * (f (y k) + inner ℝ (∇ f (y k)) (x - y k) +
          (μ / 2) * ‖x - y k‖ ^ (2 : ℕ)) := by
  simpa [lineMap_apply_module, quadraticallyRegularizedObjective_apply,
    firstOrderTaylorModelAt_apply] using
    congrFun
      (strongConvexEstimatingFunction_succ μ f φ₀ y α k)
      x

end

/-- Helper for Lemma 2.8: the recursive estimating-sequence weights stay in the interval
`[0, 1]` when each coefficient `αₖ` does. -/
private theorem estimatingWeight_mem_Icc
    {α : ℕ → ℝ}
    (hα : ∀ k, α k ∈ Set.Icc (0 : ℝ) 1) :
    ∀ k, estimatingWeight α k ∈ Set.Icc (0 : ℝ) 1
  | 0 => by
      -- The initial weight is exactly `1`.
      simp [estimatingWeight]
  | k + 1 => by
      -- The successor weight is the product of two factors already known to lie in `[0, 1]`.
      rcases estimatingWeight_mem_Icc hα k with ⟨hk_nonneg, hk_le_one⟩
      rcases hα k with ⟨hα_nonneg, hα_le_one⟩
      constructor
      · simp [estimatingWeight]
        nlinarith
      · simp [estimatingWeight]
        nlinarith

/-- Every stage of the recursive strong-convex estimating function is bounded above by the
canonical affine combination of `f` and `φ₀` with weight `estimatingWeight α k`. -/
theorem strongConvexEstimatingFunction_upper_bound_apply
    {μ : ℝ}
    {f φ₀ : E → ℝ}
    {y : ℕ → E}
    {α : ℕ → ℝ}
    (hf_strong : StrongConvexOn Set.univ μ f)
    (hf_grad : ∀ k, HasGradientAt f (∇ f (y k)) (y k))
    (hα : ∀ k, α k ∈ Set.Icc (0 : ℝ) 1) :
    ∀ k x,
      strongConvexEstimatingFunction μ f φ₀ y α k x ≤
        (1 - estimatingWeight α k) * f x + estimatingWeight α k * φ₀ x := by
  intro k
  induction k with
  | zero =>
      intro x
      -- The base stage is the trivial identity `φ₀(x) = (1 - 1) f(x) + 1 * φ₀(x)`.
      simp [strongConvexEstimatingFunction, estimatingWeight]
  | succ k ih =>
      intro x
      have hk := ih x
      have hmodel :
          quadraticallyRegularizedObjective (firstOrderTaylorModelAt f (y k)) μ (y k) x ≤ f x :=
        by
          simpa [quadraticallyRegularizedObjective_apply, firstOrderTaylorModelAt_apply,
            ge_iff_le, add_assoc, add_left_comm, add_comm] using
            StrongConvexOn.lower_tangent_quadratic_of_hasGradientAt
              hf_strong (by simp) (by simp) (hf_grad k)
      have hα_nonneg : 0 ≤ α k := (hα k).1
      have hα_le_one : α k ≤ 1 := (hα k).2
      have hone_sub_nonneg : 0 ≤ 1 - α k := by
        linarith
      -- Substitute the inductive bound and the tangent-model domination into the successor update.
      calc
        strongConvexEstimatingFunction μ f φ₀ y α (k + 1) x
          = (1 - α k) * strongConvexEstimatingFunction μ f φ₀ y α k x +
              α k * quadraticallyRegularizedObjective
                (firstOrderTaylorModelAt f (y k)) μ (y k) x := by
              simp
        _ ≤ (1 - α k) *
              ((1 - estimatingWeight α k) * f x + estimatingWeight α k * φ₀ x) +
              α k * f x := by
              nlinarith
        _ = (1 - ((1 - α k) * estimatingWeight α k)) * f x +
              ((1 - α k) * estimatingWeight α k) * φ₀ x := by
              ring
        _ = (1 - estimatingWeight α (k + 1)) * f x +
              estimatingWeight α (k + 1) * φ₀ x := by
              simp [estimatingWeight]

/-- The recursive strong-convex estimating function is bounded above by the canonical
function-space affine combination of `f` and `φ₀` with weight `estimatingWeight α k`. -/
theorem strongConvexEstimatingFunction_upper_bound
    {μ : ℝ}
    {f φ₀ : E → ℝ}
    {y : ℕ → E}
    {α : ℕ → ℝ}
    (hf_strong : StrongConvexOn Set.univ μ f)
    (hf_grad : ∀ k, HasGradientAt f (∇ f (y k)) (y k))
    (hα : ∀ k, α k ∈ Set.Icc (0 : ℝ) 1)
    (k : ℕ) :
    strongConvexEstimatingFunction μ f φ₀ y α k ≤ lineMap f φ₀ (estimatingWeight α k) := by
  intro x
  simpa [lineMap_apply_module] using
    strongConvexEstimatingFunction_upper_bound_apply hf_strong hf_grad hα k x

/-- Lemma 2.8: if `f` is differentiable at the sampled points `y_k`, is `μ`-strongly convex on
the ambient real inner-product space `E`, the coefficients satisfy `0 ≤ α_k ≤ 1`, and the
canonical weight sequence
`Real.toNNReal ∘ estimatingWeight α` tends to `0`, then the recursively defined pair
`(φ_k, λ_k)` is an estimating sequence for `f`. The smooth convex case is the specialization
`μ = 0`; the textbook assumptions `0 < α_k < 1` and divergence of the partial sums are one
sufficient way to obtain the stated weight-limit hypothesis. -/
-- Proof sketch: prove the estimating-sequence inequality by induction on `k`. The base case is
-- `λ₀ = 1` and `φ₀ = φ₀`. For the step, use the strong-convexity lower tangent inequality from
-- `hf_strong.lower_tangent_quadratic_of_hasGradientAt` together with `hf_grad k` at the point
-- `y k` to bound the owner regularized
-- Taylor model `quadraticallyRegularizedObjective (firstOrderTaylorModelAt f (y k)) μ (y k)` by
-- `f`, substitute this into `strongConvexEstimatingFunction_succ`, and simplify with the
-- recursion for `λ_{k+1}`. The asymptotic clause is exactly the hypothesis
-- `hweight_tendsto_zero`; in the textbook this is obtained from
-- `0 < α_k < 1` and divergence of the partial sums.
theorem strongConvexEstimatingFunction_isEstimatingSequence
    {μ : ℝ}
    {f : E → ℝ}
    (hf_strong : StrongConvexOn Set.univ μ f)
    (φ₀ : E → ℝ)
    (y : ℕ → E)
    (α : ℕ → ℝ)
    (hf_grad : ∀ k, HasGradientAt f (∇ f (y k)) (y k))
    (hα : ∀ k, α k ∈ Set.Icc (0 : ℝ) 1)
    (hweight_tendsto_zero :
      Filter.Tendsto (Real.toNNReal ∘ estimatingWeight α) Filter.atTop (nhds 0)) :
    IsEstimatingSequence f
      (strongConvexEstimatingFunction μ f φ₀ y α)
      (Real.toNNReal ∘ estimatingWeight α) := by
  refine ⟨hweight_tendsto_zero, ?_⟩
  intro k
  -- The limit clause is assumed, so only the stagewise affine upper bound remains.
  simpa [Real.coe_toNNReal _ (estimatingWeight_mem_Icc hα k).1] using
    strongConvexEstimatingFunction_upper_bound hf_strong hf_grad hα k

/-! ### Proposition_2_8 (from Chap02) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Primary domain: sufficient-decrease and monotonicity for constant-step gradient descent on real
Hilbert spaces.

Owner-style declarations sampled before refining this file:
* `gradientMethod` in `Algorithm_2_1`, the Chapter 2 recall of the recursive trajectory owner;
* `gradient_step_value_decrease_of_contDiffOne_withLipschitzGradient` in `Chap01/Lemma_1_6_6`,
  the arbitrary-point owner theorem from which the chapter iterate theorem is derived;
* `Antitone` and `antitone_nat_of_succ_le`, the canonical decreasing-sequence owner and its
  `ℕ`-successor bridge recalled in `Chap01/Definition_1_4_1`.

Source/core/bridge triage:
* source-facing: Proposition 2.8's monotonicity statement for the constant-step trajectory;
* core/canonical: `Antitone (fun k ↦ f (traj k))`, obtained from the Chapter 1 iterate-wise
  sufficient-decrease theorem plus nonnegativity of the constant-step factor;
* bridge/view: the one-step inequality `f (traj (k + 1)) ≤ f (traj k)` recovered from
  `Nat.le_succ k`.

Primitive data:
* the objective `f`, the constant step `α`, and the initial point `x0`;
* the smoothness hypotheses `ContDiff ℝ 1 f` and `LipschitzWith L (∇ f)`.

Derived API:
* the antitone objective-value sequence and its one-step corollary.

This file derives the textbook iterate-wise decrease directly from the Chapter 1 pointwise owner
`gradient_step_value_decrease_of_contDiffOne_withLipschitzGradient`, then packages the
source-facing monotonicity consequence with `Antitone` as the main public owner statement and the
successor-step inequality as a thin bridge. The textbook `ℝⁿ` formulation is recovered by
specializing `E` to `EuclideanSpace ℝ (Fin n)`.
-/
section GradientMethod

variable (f : E → ℝ) {L : NNReal} {α : ℝ} (x0 : E)
variable
  (hf_C1 : ContDiff ℝ 1 f)
  (hgrad : LipschitzWith L (∇ f))
  (hα_nonneg : 0 ≤ α)
  (hα_le : α ≤ 2 / (L : ℝ))

local notation "traj" => gradientMethod (fun _ ↦ α) f x0

section

include hf_C1 hgrad

/-- Helper for Proposition 2.8: along the constant-step trajectory, the pointwise descent lemma
specializes to the textbook one-step value decrease. -/
private lemma gradientMethod_step_value_decrease_of_constant_stepsize
    (k : ℕ) :
    f (traj (k + 1)) ≤
      f (traj k) - (α * (1 - ((L : ℝ) * α) / 2)) * ‖∇ f (traj k)‖ ^ (2 : ℕ) := by
  -- Route correction: use the Chapter 1 pointwise descent owner directly, since the iterate-wise
  -- wrapper module is not available in the current workspace import state.
  -- Rewriting `traj (k + 1)` by the recursion turns the textbook iterate step into the pointwise
  -- antigradient update from Lemma 1.6.6.
  simpa [gradientMethod_succ] using
    gradient_step_value_decrease_of_contDiffOne_withLipschitzGradient
      hf_C1 hgrad (traj k) α

end

section

include hα_nonneg hα_le

/-- Helper for Proposition 2.8: the admissible constant-step range makes the descent coefficient
nonnegative. -/
private lemma stepFactor_nonneg
    : 0 ≤ α * (1 - ((L : ℝ) * α) / 2) := by
  -- Separate the degenerate `L = 0` case from the positive-L case.
  by_cases hL0 : (L : ℝ) = 0
  · have hα_nonpos : α ≤ 0 := by
      simpa [hL0] using hα_le
    have hα_eq : α = 0 := by
      linarith
    simp [hα_eq]
  · have hL_pos : 0 < (L : ℝ) :=
      lt_of_le_of_ne L.2 <| by simpa [eq_comm] using hL0
    have hmul : (L : ℝ) * α ≤ 2 := by
      simpa [mul_comm] using (le_div_iff₀ hL_pos).mp hα_le
    have hscale_nonneg : 0 ≤ 1 - ((L : ℝ) * α) / 2 := by
      nlinarith
    exact mul_nonneg hα_nonneg hscale_nonneg

end

include hf_C1 hgrad hα_nonneg hα_le

/-- Proposition 2.8: on the monotonicity range `0 ≤ α ≤ 2 / L`, the objective values along the
constant-step gradient-method trajectory form an antitone sequence. The source range
`0 < α ≤ 2 / L` is a special case, and the textbook `ℝⁿ` statement is recovered by specializing
`E` to `EuclideanSpace ℝ (Fin n)`. -/
-- Proof sketch: obtain the one-step decrease from the Chapter 1 constant-step owner theorem, then
-- promote the successor-step inequality to an antitone sequence on `ℕ`.
theorem gradientMethod_value_antitone_of_constant_stepsize
    : Antitone (fun k ↦ f (traj k)) := by
  refine antitone_nat_of_succ_le ?_
  intro k
  have hstep := gradientMethod_step_value_decrease_of_constant_stepsize
    (f := f) (L := L) (α := α) (x0 := x0) (hf_C1 := hf_C1) (hgrad := hgrad) k
  have hterm_nonneg :
      0 ≤ (α * (1 - ((L : ℝ) * α) / 2)) * ‖∇ f (traj k)‖ ^ (2 : ℕ) := by
    -- The decrease term is nonnegative because both the scalar coefficient and the squared norm
    -- are nonnegative on the admissible step-size range.
    exact mul_nonneg
      (stepFactor_nonneg (L := L) (α := α) (hα_nonneg := hα_nonneg) (hα_le := hα_le))
      (by positivity)
  -- Dropping the nonnegative decrease term gives the monotonicity inequality.
  linarith

/-- Companion one-step formulation of Proposition 2.8. -/
theorem gradientMethod_value_nonincreasing_step
    (k : ℕ) :
    f (traj (k + 1)) ≤ f (traj k) := by
  -- The one-step statement is the successor instance of the antitone trajectory-value sequence.
  simpa using
    gradientMethod_value_antitone_of_constant_stepsize
      f x0 hf_C1 hgrad hα_nonneg hα_le (Nat.le_succ k)

end GradientMethod
