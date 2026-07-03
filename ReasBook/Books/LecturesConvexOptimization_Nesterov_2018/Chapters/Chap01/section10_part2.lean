import Mathlib
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_1_10_7 (from Chap01) -/
noncomputable section

universe u

namespace LagrangianProblem

variable {Q : Type u} {m : ℕ} (problem : LagrangianProblem Q m)

local notation "Λ" => EuclideanSpace ℝ (Fin m)
local notation "ψ" => problem.dualFunction
local notation "X⋆" => problem.lagrangianMinimizers

/-
Primary domain: Lagrangian duality for inequality-constrained problems.

Owner declarations sampled before refining this file:
* `LagrangianProblem.dualFunction`, `dualDomain`, `lagrangianMinimizers`, and
  `dualFunction_eq_lagrangian` in
  `Definition_1_10_2`;
* mathlib's owner predicate `ConcaveOn` in `Mathlib/Analysis/Convex/Function`, the canonical
  Jensen-style abstraction when the codomain is an `ℝ`-module;
* the Chapter 3 finite-part API `extendedRealEffectiveDomain`, `extendedRealRealPart`, and the
  resulting `ConcaveOn`-based owner style for `EReal`-valued functions once such a bridge is
  available;
* `PrimalEqualityConstrainedProblem.LagrangianMinimizerSelection.dualFunction_eq_lagrangian` in
  `Definition_2_31`, a downstream bridge that should delegate to the owner-level single-minimizer
  identity rather than reprove it.

Best owner abstraction: `problem : LagrangianProblem Q m`. The primitive data remain only the
owner fields `objective` and `constraints`; `constraintVector`, `dualFunction`, `dualDomain`, and
`lagrangianMinimizers` are derived API.

Source/core/bridge triage in this file:
* source-facing: Proposition 1.10.7's affine upper-support inequality for `dualFunction`;
* core/canonical: the owner identity `ψ(λ) = 𝓛(x, λ)` at a point `x ∈ X*(λ)`, now attached
  directly to `LagrangianProblem`;
* bridge/view: the Jensen-style concavity inequality on `dualDomain`.

Because `dualFunction` is `EReal`-valued, the direct mathlib owner `ConcaveOn ℝ _ ψ` is not
available here: `EReal` does not carry the required `SMul ℝ EReal` instance. The Chapter 3
finite-part bridge `ConcaveOn ℝ (dom ψ) (extendedRealRealPart ψ)` is therefore a later
bridge/view layer, not the Chapter 1 owner. This file correspondingly keeps the source-facing
Jensen inequality rather than forcing an ad hoc real-valued wrapper.
-/

-- The source proof first identifies the affine dependence of `𝓛(x, ·)` on the multiplier and
-- then transfers that pointwise structure to the infimum defining `ψ`.
/-- Helper for Proposition 1.10.7: changing the multiplier changes the Lagrangian by the
corresponding constraint inner product. -/
lemma lagrangian_eq_add_inner_sub
    {x : Q} {lam₁ lam₂ : Λ} :
    (problem.lagrangian x lam₂ : EReal) =
      (problem.lagrangian x lam₁ : EReal) +
        inner ℝ (problem.constraintVector x) (lam₂ - lam₁) := by
  -- Normalize the affine change in the multiplier on the real side before casting to `EReal`.
  have hreal :
      problem.lagrangian x lam₂ =
        problem.lagrangian x lam₁ + inner ℝ (problem.constraintVector x) (lam₂ - lam₁) := by
    rw [LagrangianProblem.lagrangian, LagrangianProblem.lagrangian]
    have hcomm :
        inner ℝ (problem.constraintVector x) (lam₂ - lam₁) =
          inner ℝ (lam₂ - lam₁) (problem.constraintVector x) := by
      simpa using (real_inner_comm (problem.constraintVector x) (lam₂ - lam₁)).symm
    rw [hcomm, inner_sub_left]
    ring_nf
  exact_mod_cast hreal

/-- Helper for Proposition 1.10.7: for each fixed `x`, the Lagrangian is affine in the
multiplier. -/
lemma lagrangian_convexCombination_eq
    {x : Q} {lam₁ lam₂ : Λ} {a b : ℝ} (hab : a + b = 1) :
    problem.lagrangian x (a • lam₁ + b • lam₂) =
      a * problem.lagrangian x lam₁ + b * problem.lagrangian x lam₂ := by
  -- Expand the Lagrangian and collect the objective and inner-product terms by the weights.
  rw [LagrangianProblem.lagrangian, LagrangianProblem.lagrangian, LagrangianProblem.lagrangian]
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  calc
    problem x + (a * inner ℝ lam₁ (problem.constraintVector x) +
        b * inner ℝ lam₂ (problem.constraintVector x)) =
      (a + b) * problem x +
        (a * inner ℝ lam₁ (problem.constraintVector x) +
          b * inner ℝ lam₂ (problem.constraintVector x)) := by
        rw [hab, one_mul]
    _ = a * (problem x + inner ℝ lam₁ (problem.constraintVector x)) +
        b * (problem x + inner ℝ lam₂ (problem.constraintVector x)) := by
      ring

/-- Helper for Proposition 1.10.7: every weighted average of two dual values is bounded above by
the corresponding weighted Lagrangian evaluation at any fixed point `x`. -/
lemma weighted_dualFunction_le_lagrangian_convexCombination
    {x : Q} {lam₁ lam₂ : Λ} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a : EReal) * ψ lam₁ + (b : EReal) * ψ lam₂ ≤
      (problem.lagrangian x (a • lam₁ + b • lam₂) : EReal) := by
  -- Bound each dual value by evaluating the defining infimum at the chosen point `x`.
  have h₁ : ψ lam₁ ≤ (problem.lagrangian x lam₁ : EReal) := by
    simpa [LagrangianProblem.dualFunction] using
      (SetConstrainedMinimizationProblem.optimalValue_le_of_mem_feasibleSet
        (problem := SetConstrainedMinimizationProblem.unconstrained
          (fun y ↦ problem.lagrangian y lam₁))
        (x := x)
        (by simp))
  have h₂ : ψ lam₂ ≤ (problem.lagrangian x lam₂ : EReal) := by
    simpa [LagrangianProblem.dualFunction] using
      (SetConstrainedMinimizationProblem.optimalValue_le_of_mem_feasibleSet
        (problem := SetConstrainedMinimizationProblem.unconstrained
          (fun y ↦ problem.lagrangian y lam₂))
        (x := x)
        (by simp))
  -- Preserve those bounds under the nonnegative weights and collapse the right-hand side.
  have hmul₁ :
      (a : EReal) * ψ lam₁ ≤ (a : EReal) * (problem.lagrangian x lam₁ : EReal) := by
    exact mul_le_mul_of_nonneg_left h₁ (by exact_mod_cast ha)
  have hmul₂ :
      (b : EReal) * ψ lam₂ ≤ (b : EReal) * (problem.lagrangian x lam₂ : EReal) := by
    exact mul_le_mul_of_nonneg_left h₂ (by exact_mod_cast hb)
  calc
    (a : EReal) * ψ lam₁ + (b : EReal) * ψ lam₂ ≤
        (a : EReal) * (problem.lagrangian x lam₁ : EReal) +
          (b : EReal) * (problem.lagrangian x lam₂ : EReal) := by
      exact add_le_add hmul₁ hmul₂
    _ = (problem.lagrangian x (a • lam₁ + b • lam₂) : EReal) := by
      exact_mod_cast (problem.lagrangian_convexCombination_eq (x := x) (hab := hab)).symm

/-- Proposition 1.10.7: if `x₁ ∈ X*(λ₁)`, then the dual function is bounded above by the affine
support determined by `x₁` at `λ₁`. -/
-- Proof sketch: bound `ψ(λ₂)` by evaluating the infimum defining `ψ(λ₂)` at `x₁`, use
-- `problem.dualFunction_eq_lagrangian hx₁` to replace `𝓛(x₁, λ₁)` with `ψ(λ₁)`, and simplify the
-- difference of the two
-- Lagrangian values into the inner product with `λ₂ - λ₁`.
theorem dualFunction_le_affine_support_of_mem_lagrangianMinimizers
    {lam₁ lam₂ : Λ} {x₁ : Q}
    (hx₁ : x₁ ∈ X⋆ lam₁) :
    ψ lam₂ ≤ ψ lam₁ + (inner ℝ (problem.constraintVector x₁) (lam₂ - lam₁) : EReal) := by
  -- Evaluate the infimum defining `ψ(λ₂)` at the chosen minimizer `x₁`.
  have hdualLe : ψ lam₂ ≤ (problem.lagrangian x₁ lam₂ : EReal) := by
    simpa [LagrangianProblem.dualFunction] using
      (SetConstrainedMinimizationProblem.optimalValue_le_of_mem_feasibleSet
        (problem := SetConstrainedMinimizationProblem.unconstrained
          (fun y ↦ problem.lagrangian y lam₂))
        (x := x₁)
        (by simp))
  -- Replace the value at `λ₁` by `ψ(λ₁)` and rewrite the multiplier shift affinely.
  calc
    ψ lam₂ ≤ (problem.lagrangian x₁ lam₂ : EReal) := hdualLe
    _ = (problem.lagrangian x₁ lam₁ : EReal) +
          inner ℝ (problem.constraintVector x₁) (lam₂ - lam₁) :=
      problem.lagrangian_eq_add_inner_sub
    _ = ψ lam₁ + (inner ℝ (problem.constraintVector x₁) (lam₂ - lam₁) : EReal) := by
      rw [problem.dualFunction_eq_lagrangian hx₁]

/-- On `dom ψ = {λ | ψ(λ) > -∞}`, the dual function satisfies the Jensen inequality for
concavity. -/
-- Proof sketch: write `ψ` as the pointwise infimum of the affine maps
-- `λ ↦ 𝓛(x, λ)` indexed by `x ∈ Q`, evaluate those affine maps at the convex combination
-- `a • λ₁ + b • λ₂`, and then pass to the infimum over `x`.
theorem dualFunction_concave_on_dualDomain
    {lam₁ lam₂ : Λ}
    (h_lam₁ : lam₁ ∈ problem.dualDomain) (h_lam₂ : lam₂ ∈ problem.dualDomain)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a : EReal) * ψ lam₁ + (b : EReal) * ψ lam₂ ≤ ψ (a • lam₁ + b • lam₂) := by
  -- The domain hypotheses record the stated domain restriction; the Jensen argument is pointwise.
  let _ := h_lam₁
  let _ := h_lam₂
  -- Rewrite the dual value at the convex combination as an infimum over all Lagrangian values.
  rw [LagrangianProblem.dualFunction,
    SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image]
  refine le_sInf ?_
  rintro _ ⟨x, -, rfl⟩
  -- Each pointwise affine upper bound survives to the infimum over all `x`.
  exact problem.weighted_dualFunction_le_lagrangian_convexCombination
    (x := x) ha hb hab

end LagrangianProblem

/-! ### Proposition_1_10_8 (from Chap01) -/
noncomputable section

universe u

open scoped EuclideanOrthant

namespace LagrangianProblem

variable {Q : Type u} {m : ℕ}

local notation "Λ" => EuclideanSpace ℝ (Fin m)

/-
Source/core/bridge triage for Proposition 1.10.8:
- source-facing: weak duality `f_* ≤ f*` for the owner `LagrangianProblem`;
- core/canonical owner: `problem : LagrangianProblem Q m` with its derived notions
  `feasibleSet`, `primalOptimalValue`, `dualFunction`, and
  `dualOptimalValue`;
- bridge/view: the pointwise weak-duality estimate
  `problem.dualFunction l ≤ problem.primalOptimalValue` for `l ∈ nonnegativeOrthant m`.

Primitive data:
- `problem.objective`
- `problem.constraints`

Derived API:
- `SetConstrainedMinimizationProblem.optimalValue`
- `problem.feasibleSet`
- `problem.primalOptimalValue`
- `problem.lagrangian`
- `problem.dualFunction`
- `ℝ₊^m`
- `problem.dualFeasibleSet`
- `problem.dualOptimalValue`

The pointwise weak-duality estimate is mathematically atomic owner API, and its hypothesis is
only nonnegativity of the multiplier. The stronger dual-domain membership built into
`problem.dualFeasibleSet` is not needed for that inequality and therefore stays out of the
companion theorem statement.
-/

/-- Helper for Proposition 1.10.8: a nonnegative multiplier makes the Lagrangian no larger than
the objective at every primal-feasible point. -/
lemma lagrangian_le_objective_of_mem_feasibleSet
    (problem : LagrangianProblem Q m) {x : Q} {l : Λ}
    (hx : x ∈ problem.feasibleSet) (hl : l ∈ ℝ₊^m) :
    problem.lagrangian x l ≤ problem x := by
  -- Rewrite primal feasibility and multiplier nonnegativity coordinatewise.
  have hx_le : ∀ j : Fin m, problem.constraints j x ≤ 0 := by
    simpa using problem.mem_feasibleSet_iff.mp hx
  have hl_nonneg : ∀ j : Fin m, 0 ≤ l j := by
    simpa [EuclideanSpace.mem_nonnegativeOrthant_iff] using hl
  -- Show that every summand in the inner product term is nonpositive.
  rw [LagrangianProblem.lagrangian, PiLp.inner_apply]
  have hsum_nonpos :
      ∑ j, inner ℝ (l j) (problem.constraintVector x j) ≤ 0 := by
    refine Finset.sum_nonpos ?_
    intro j _
    have hscalar :
        inner ℝ (l j) (problem.constraintVector x j) =
          l j * problem.constraintVector x j := by
      have hinner :
          inner ℝ (l j) (problem.constraintVector x j) =
            problem.constraintVector x j * (starRingEnd ℝ) (l j) :=
        RCLike.inner_apply (l j) (problem.constraintVector x j)
      simpa [mul_comm] using hinner
    rw [hscalar, problem.constraintVector_apply]
    exact mul_nonpos_of_nonneg_of_nonpos (hl_nonneg j) (hx_le j)
  linarith

/-- Helper for Proposition 1.10.8: the dual function is bounded above by the Lagrangian at every
point. -/
lemma dualFunction_le_lagrangian
    (problem : LagrangianProblem Q m) (l : Λ) (x : Q) :
    problem.dualFunction l ≤ (problem.lagrangian x l : EReal) := by
  -- Evaluate the unconstrained Lagrangian subproblem at the ambient point `x`.
  simpa [LagrangianProblem.dualFunction] using
    (SetConstrainedMinimizationProblem.optimalValue_le_of_mem_feasibleSet
      (problem := SetConstrainedMinimizationProblem.unconstrained
        (fun y ↦ problem.lagrangian y l))
      (x := x)
      (by simp))

/-- Weak duality at a fixed nonnegative multiplier: the dual value at `l` is bounded above by the
primal optimal value. -/
-- Proof sketch: for each feasible point `x`, the constraint terms satisfy
-- `lᵢ * problem.constraints i x ≤ 0`, so `problem.lagrangian x l ≤ problem x`. View
-- `problem.dualFunction l` as the owner optimal value of the unconstrained Lagrangian subproblem
-- and `problem.primalOptimalValue` as the owner optimal value of the primal constrained problem;
-- then compare both owner values at each feasible `x`.
theorem dualFunction_le_primalOptimalValue
    (problem : LagrangianProblem Q m) (l : Λ)
    (hl : l ∈ ℝ₊^m) :
    problem.dualFunction l ≤ problem.primalOptimalValue := by
  -- Rewrite the primal value as the infimum of the feasible objective values.
  rw [problem.primalOptimalValue_eq_sInf_image]
  refine le_sInf ?_
  rintro _ ⟨x, hx, rfl⟩
  -- Compare `ψ(l)` to the feasible objective through the Lagrangian at `x`.
  calc
    problem.dualFunction l ≤ (problem.lagrangian x l : EReal) :=
      problem.dualFunction_le_lagrangian l x
    _ ≤ (problem x : EReal) := by
      exact_mod_cast problem.lagrangian_le_objective_of_mem_feasibleSet hx hl

/-- Proposition 1.10.8: weak duality bounds the dual optimal value of a Lagrangian problem by
its primal optimal value. -/
-- Proof sketch: apply
-- `dualFunction_le_primalOptimalValue` to each
-- `l ∈ problem.dualFeasibleSet`, using `problem.mem_dualFeasibleSet_iff` to extract the
-- nonnegativity hypothesis, and then pass to the supremum over the dual-feasible set.
theorem dualOptimalValue_le_primalOptimalValue
    (problem : LagrangianProblem Q m) :
    problem.dualOptimalValue ≤ problem.primalOptimalValue := by
  -- Bound every dual-feasible image point by the fixed-multiplier weak-duality estimate.
  rw [LagrangianProblem.dualOptimalValue]
  refine sSup_le ?_
  rintro _ ⟨l, hl, rfl⟩
  have hl_nonneg : l ∈ ℝ₊^m := by
    simpa [EuclideanSpace.mem_nonnegativeOrthant_iff] using
      (problem.mem_dualFeasibleSet_iff.mp hl).2
  exact problem.dualFunction_le_primalOptimalValue l hl_nonneg

end LagrangianProblem

/-! ### Definition_1_10_9 (from Chap01) -/
universe u

namespace LagrangianProblem

variable {Q : Type u} {m : ℕ}

/-
Definition 1.10.9 lies in the Chapter 1 strict-feasibility domain.

Sampled owner-style declarations in this domain:
* `FunctionalConstraintsMinimizationProblem.StrictlyFeasible` in `Chap01/Definition_1_1_2`
* `LagrangianProblem.toFunctionalConstraintsMinimizationProblem` in `Chap01/Definition_1_10_2`
* `FunctionalConstraintsMinimizationProblem.StrictlyFeasible.feasibleSet_nonempty` in
  `Chap01/Definition_1_1_2`

Best owner abstraction:
* the Chapter 1 strict-feasibility owner
  `problem.toFunctionalConstraintsMinimizationProblem.StrictlyFeasible`

Primitive data:
* `problem.objective`
* `problem.constraints`

Derived API:
* `problem.feasibleSet`
* the textbook expansion `∃ x : Q, ∀ j : Fin m, problem.constraints j x < 0`
* the induced feasible-set nonemptiness theorem on `problem.feasibleSet`

Source/core/bridge triage:
* source-facing: the textbook strict-inequality formulation of Slater's condition
* core/canonical: `FunctionalConstraintsMinimizationProblem.StrictlyFeasible`
* bridge/view: `problem.toFunctionalConstraintsMinimizationProblem`

This file does not introduce a second owner. Definition 1.10.9 is the specialization of the
existing strict-feasibility owner along `toFunctionalConstraintsMinimizationProblem`, and the
source-facing API here should stay at that bridge layer.
-/

/- Definition 1.10.9 reuses the Chapter 1 strict-feasibility owner specialized to a
`LagrangianProblem`. -/
variable (problem : LagrangianProblem Q m) in
#check problem.toFunctionalConstraintsMinimizationProblem.StrictlyFeasible

/-- Definition 1.10.9: the Slater condition for a Lagrangian problem is strict feasibility of the
associated functional-constraint problem obtained by viewing every scalar constraint as an
inequality `fⱼ(x) ≤ 0`. -/
def SlaterCondition (problem : LagrangianProblem Q m) : Prop :=
  problem.toFunctionalConstraintsMinimizationProblem.StrictlyFeasible

/-- Helper for Definition 1.10.9: expanding `problem.SlaterCondition` recovers the textbook
coordinatewise strict-inequality formulation. -/
@[simp] theorem slaterCondition_iff (problem : LagrangianProblem Q m) :
    problem.SlaterCondition ↔
      ∃ x : Q, ∀ j : Fin m, problem.constraints j x < 0 := by
  let P := problem.toFunctionalConstraintsMinimizationProblem
  -- Re-express the bridge definition in terms of the owner strict-feasibility predicate.
  change P.StrictlyFeasible ↔
      ∃ x : Q, ∀ j : Fin m, problem.constraints j x < 0
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    intro j
    -- Unpack membership in the owner strict feasible set and simplify the `≤`-constraint view.
    simpa [LagrangianProblem.toFunctionalConstraintsMinimizationProblem,
      ConstraintSense.StrictHolds] using
      (P.mem_strictFeasibleSet.mp hx) j
  · rintro ⟨x, hx⟩
    -- Repackage a textbook Slater point as a strict-feasible point of the owner problem.
    refine ⟨⟨x, Set.mem_univ x⟩, ?_⟩
    exact P.mem_strictFeasibleSet.mpr <| fun j ↦ by
      simpa [LagrangianProblem.toFunctionalConstraintsMinimizationProblem,
        ConstraintSense.StrictHolds] using hx j

/-- Helper for Definition 1.10.9: a Slater point is in particular feasible for the associated
inequality-constrained problem. -/
theorem feasibleSet_nonempty_of_slaterCondition {problem : LagrangianProblem Q m}
    (h : problem.SlaterCondition) :
    problem.feasibleSet.Nonempty := by
  -- The owner strict-feasibility theorem already provides a feasible point after unfolding.
  simpa [LagrangianProblem.feasibleSet] using h.feasibleSet_nonempty

end LagrangianProblem

/-! ### Example_1_10_10 (from Chap01) -/
variable {X : Type*} [TopologicalSpace X] {ι : Type*} [Fintype ι]

section

variable (constraints : ι → C(X, ℝ))

/- Primary domain: penalty functions for finite families of continuous inequality constraints.

Relevant owner declarations sampled before refining:
* `IsPenaltyFunction` in `Definition_1_10_14`
* `quadraticPenalty` in `Definition_1_10_15`
* `nonsmoothPenalty` in `Definition_1_10_15`
* the owner certification theorems
  `quadraticPenalty_isPenaltyFunction` and
  `nonsmoothPenalty_isPenaltyFunction` in `Definition_1_10_15`

Best owner abstraction:
* core/canonical: `IsPenaltyFunction`

Primitive data:
* the finite family `constraints : ι → C(X, ℝ)` with `[Fintype ι]`

Derived API:
* the concrete penalties `quadratic_penalty_function constraints` and
  `nonsmoothPenalty constraints`
* their pointwise textbook formulas
  `quadraticPenalty_apply` and `nonsmoothPenalty_apply`
* their certification as penalty functions for the chapter owner
  `constraintSet constraints`

Source/core/bridge triage:
* source-facing: Example 1.10.10, asserting that these two explicit positive-part sums are
  penalty functions for the same feasible set
* core/canonical: `IsPenaltyFunction`
* bridge/view: direct recall of the two owner certification theorems from `Definition_1_10_15`

This file adds no new owner-level API: the concrete penalties, their textbook evaluation formulas,
and their certification theorems already live in the owner file, so keeping local duplicate
example theorems here would only duplicate that API. The source's Euclidean model is not used by
the owner declarations, so the example is stated at the same canonical ambient level as
`Definition_1_10_15`. -/

/- Example 1.10.10: the quadratic positive-part sum is the concrete owner
`quadraticPenalty constraints`. -/
recall quadraticPenalty

/- Example 1.10.10: pointwise, the quadratic penalty is the textbook sum
`x ↦ ∑ j, ((constraints j x)⁺)^2`. -/
recall quadraticPenalty_apply

/- Example 1.10.10: the quadratic positive-part sum is a penalty for the feasible set cut out by
the constraints. -/
recall quadraticPenalty_isPenaltyFunction

/- Example 1.10.10: the nonsmooth positive-part sum is the concrete owner
`nonsmoothPenalty constraints`. -/
recall nonsmoothPenalty

/- Example 1.10.10: pointwise, the nonsmooth penalty is the textbook sum
`x ↦ ∑ j, (constraints j x)⁺`. -/
recall nonsmoothPenalty_apply

/- Example 1.10.10: the nonsmooth positive-part sum is a penalty for the same feasible set. -/
recall nonsmoothPenalty_isPenaltyFunction

end

/-! ### Proposition_1_10_12 (from Chap01) -/
noncomputable section

open Set EuclideanSpace

/-
Source/core/bridge triage for Proposition 1.10.12:
- source-facing: the textbook scalar maximizer `λ_*` and the trajectory value `x(λ_*)`;
- core/canonical owner: `lagrangianRelaxationExample.dualFunction`;
- bridge/view: `lagrangianRelaxationExampleMultiplier_mem_dualDomain_iff` and
  `lagrangianRelaxationExample_dualFunction_eq_closedForm`, together with the owner-side
  maximality and dual-feasibility bridges for `single 0 λ_*`.

Primitive data already live upstream:
- the owner `lagrangianRelaxationExample : LagrangianProblem _ 1`,
- the scalar-domain and closed-form bridge theorems listed above,
- the explicit minimizer trajectory `lagrangianRelaxationExampleMinimizerTrajectory`.

This file only names the textbook scalar maximizer `λ_*` and records the derived maximizer and
trajectory statements attached to that owner data.
-/

local notation "D" => Iio (1 : ℝ)
local notation "ψ" => lagrangianRelaxationExample.dualFunction ∘ single 0

/-- The unique maximizer of the example dual function on `(-∞, 1)`. -/
def lagrangianRelaxationExampleLambdaStar : ℝ :=
  1 - Real.rpow (1 / 2 : ℝ) (1 / 3 : ℝ)

/-- Helper for Proposition 1.10.12: the real closed form of the example dual function on
`(-∞, 1)`. -/
def lagrangianRelaxationExampleClosedForm (lam : ℝ) : ℝ :=
  lam - (1 / 2 : ℝ) * lam ^ (2 : ℕ) - (1 - lam)⁻¹ * (1 / 2 : ℝ) + (1 / 2 : ℝ)

/-- Helper for Proposition 1.10.12: the first derivative of the real closed form. -/
def lagrangianRelaxationExampleClosedFormDeriv (lam : ℝ) : ℝ :=
  1 - lam - ((1 - lam) ^ (2 : ℕ))⁻¹ * (1 / 2 : ℝ)

/-- Helper for Proposition 1.10.12: on `(-∞, 1)`, the owner-side dual function agrees with the
real closed form. -/
lemma lagrangianRelaxationExample_dualFunction_eq_closedForm_on_Iio_one
    {lam : ℝ} (h_lam : lam ∈ D) :
    ψ lam = (lagrangianRelaxationExampleClosedForm lam : EReal) := by
  -- The scalar interval `D` is exactly the domain where Proposition 1.10.5 gives the closed form.
  have hreal :
      lam - (1 / 2 : ℝ) * lam ^ (2 : ℕ) - 1 / (2 * (1 - lam)) + (1 / 2 : ℝ) =
        lagrangianRelaxationExampleClosedForm lam := by
    have hlamlt : lam < 1 := h_lam
    have hne : 1 - lam ≠ 0 := by
      linarith
    unfold lagrangianRelaxationExampleClosedForm
    field_simp [hne]
  rw [← hreal]
  exact lagrangianRelaxationExample_dualFunction_eq_closedForm lam h_lam

/-- Helper for Proposition 1.10.12: the owner-side `IsMaxOn` statement is equivalent to the real
closed-form `IsMaxOn` statement on `(-∞, 1)`. -/
lemma lagrangianRelaxationExample_closedForm_isMaxOn_iff
    {lam : ℝ} (h_lam : lam ∈ D) :
    IsMaxOn ψ D lam ↔ IsMaxOn lagrangianRelaxationExampleClosedForm D lam := by
  rw [isMaxOn_iff, isMaxOn_iff]
  constructor
  · intro hmax y hy
    -- Rewrite both dual values into finite real numbers before comparing them.
    have hy_eq := lagrangianRelaxationExample_dualFunction_eq_closedForm_on_Iio_one hy
    have hlam_eq := lagrangianRelaxationExample_dualFunction_eq_closedForm_on_Iio_one h_lam
    have hle := hmax y hy
    rw [hy_eq, hlam_eq] at hle
    exact EReal.coe_le_coe_iff.mp hle
  · intro hmax y hy
    -- Transport the real comparison back into `EReal` using the same closed-form identities.
    have hy_eq := lagrangianRelaxationExample_dualFunction_eq_closedForm_on_Iio_one hy
    have hlam_eq := lagrangianRelaxationExample_dualFunction_eq_closedForm_on_Iio_one h_lam
    rw [hy_eq, hlam_eq]
    exact EReal.coe_le_coe_iff.mpr (hmax y hy)

/-- Helper for Proposition 1.10.12: the closed form is continuous on `(-∞, 1)`. -/
lemma lagrangianRelaxationExampleClosedForm_continuousOn :
    ContinuousOn lagrangianRelaxationExampleClosedForm D := by
  intro x hx
  -- The only singularity comes from `1 - x = 0`, excluded by `x < 1`.
  have hxlt : x < 1 := hx
  have hne : 1 - x ≠ 0 := by
    linarith
  have hcont :
      ContinuousAt
        (fun t : ℝ ↦ t - (1 / 2 : ℝ) * t ^ (2 : ℕ) - (1 - t)⁻¹ * (1 / 2 : ℝ) + (1 / 2 : ℝ))
        x := by
    fun_prop (disch := assumption)
  change ContinuousWithinAt
    (fun t : ℝ ↦ t - (1 / 2 : ℝ) * t ^ (2 : ℕ) - (1 - t)⁻¹ * (1 / 2 : ℝ) + (1 / 2 : ℝ))
    D x
  exact hcont.continuousWithinAt

/-- Helper for Proposition 1.10.12: the closed form is differentiable at every point of
`(-∞, 1)`. -/
lemma lagrangianRelaxationExampleClosedForm_differentiableAt
    {x : ℝ} (hx : x ∈ D) :
    DifferentiableAt ℝ lagrangianRelaxationExampleClosedForm x := by
  -- Again, the denominator does not vanish because `x < 1`.
  have hxlt : x < 1 := hx
  have hne : 1 - x ≠ 0 := by
    linarith
  change DifferentiableAt ℝ
    (fun t : ℝ ↦ t - (1 / 2 : ℝ) * t ^ (2 : ℕ) - (1 - t)⁻¹ * (1 / 2 : ℝ) + (1 / 2 : ℝ))
    x
  fun_prop (disch := assumption)

/-- Helper for Proposition 1.10.12: the closed form has the expected first derivative on
`(-∞, 1)`. -/
lemma lagrangianRelaxationExampleClosedForm_hasDerivAt
    {x : ℝ} (hx : x ∈ D) :
    HasDerivAt lagrangianRelaxationExampleClosedForm
      (lagrangianRelaxationExampleClosedFormDeriv x) x := by
  -- Differentiate the affine, quadratic, and reciprocal pieces separately.
  have hxlt : x < 1 := hx
  have hne : 1 - x ≠ 0 := by
    linarith
  have hid : HasDerivAt (fun y : ℝ ↦ y) 1 x := hasDerivAt_id x
  have hsq : HasDerivAt (fun y : ℝ ↦ (1 / 2 : ℝ) * y ^ (2 : ℕ)) x x := by
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using
      ((hasDerivAt_id x).pow 2).const_mul (1 / 2 : ℝ)
  have hu : HasDerivAt (fun y : ℝ ↦ 1 - y) (-1) x := by
    simpa using (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
  have hinv : HasDerivAt (fun y : ℝ ↦ (1 - y)⁻¹) (((1 - x) ^ (2 : ℕ))⁻¹) x := by
    simpa [div_eq_mul_inv, pow_two, mul_comm, mul_left_comm, mul_assoc] using hu.inv hne
  have hhalf :
      HasDerivAt
        (fun y : ℝ ↦ (1 - y)⁻¹ * (1 / 2 : ℝ))
        (((1 - x) ^ (2 : ℕ))⁻¹ * (1 / 2 : ℝ)) x := by
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using
      hinv.mul_const (1 / 2 : ℝ)
  change HasDerivAt
    (fun y : ℝ ↦ y - (1 / 2 : ℝ) * y ^ (2 : ℕ) - (1 - y)⁻¹ * (1 / 2 : ℝ) + (1 / 2 : ℝ))
    (lagrangianRelaxationExampleClosedFormDeriv x) x
  simpa [lagrangianRelaxationExampleClosedFormDeriv, sub_eq_add_neg,
    add_comm, add_left_comm, add_assoc] using
    ((hid.sub hsq).sub hhalf).add_const (1 / 2 : ℝ)

/-- Helper for Proposition 1.10.12: the derivative of the closed form has the expected textbook
formula. -/
lemma lagrangianRelaxationExampleClosedForm_deriv
    {x : ℝ} (hx : x ∈ D) :
    deriv lagrangianRelaxationExampleClosedForm x =
      lagrangianRelaxationExampleClosedFormDeriv x := by
  -- The derivative is already packaged by the explicit `HasDerivAt` computation above.
  exact (lagrangianRelaxationExampleClosedForm_hasDerivAt hx).deriv

/-- Helper for Proposition 1.10.12: the explicit derivative is continuous on `(-∞, 1)`. -/
lemma lagrangianRelaxationExampleClosedFormDeriv_continuousOn :
    ContinuousOn lagrangianRelaxationExampleClosedFormDeriv D := by
  intro x hx
  -- The derivative only has the same pole at `x = 1`, which is still outside the domain.
  have hxlt : x < 1 := hx
  have hx0 : 0 < 1 - x := by
    linarith
  have hne : ((1 - x) ^ (2 : ℕ) : ℝ) ≠ 0 := by
    positivity
  have hcont :
      ContinuousAt
        (fun t : ℝ ↦ 1 - t - ((1 - t) ^ (2 : ℕ))⁻¹ * (1 / 2 : ℝ))
        x := by
    fun_prop (disch := assumption)
  change ContinuousWithinAt
    (fun t : ℝ ↦ 1 - t - ((1 - t) ^ (2 : ℕ))⁻¹ * (1 / 2 : ℝ))
    D x
  exact hcont.continuousWithinAt

/-- Helper for Proposition 1.10.12: the explicit first derivative itself has derivative
`-1 - (1 - x)⁻³`. -/
lemma lagrangianRelaxationExampleClosedFormDeriv_hasDerivAt
    {x : ℝ} (hx : x ∈ D) :
    HasDerivAt lagrangianRelaxationExampleClosedFormDeriv
      (-1 - ((1 - x) ^ (3 : ℕ))⁻¹) x := by
  -- Differentiate the inverse-square term explicitly and simplify the resulting algebra.
  have hxlt : x < 1 := hx
  have hx0 : 0 < 1 - x := by
    linarith
  have hne : ((1 - x) ^ (2 : ℕ) : ℝ) ≠ 0 := by
    positivity
  have hu : HasDerivAt (fun t : ℝ ↦ 1 - t) (-1) x := by
    simpa using (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
  have hsq : HasDerivAt (fun t : ℝ ↦ (1 - t) ^ (2 : ℕ)) (-2 * (1 - x)) x := by
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hu.pow 2
  have hinv :
      HasDerivAt (fun t : ℝ ↦ ((1 - t) ^ (2 : ℕ) : ℝ)⁻¹)
        (2 * (1 - x) / (((1 - x) ^ (2 : ℕ) : ℝ) ^ (2 : ℕ))) x := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hsq.inv hne
  have hhalf :
      HasDerivAt
        (fun t : ℝ ↦ ((1 - t) ^ (2 : ℕ) : ℝ)⁻¹ * (1 / 2 : ℝ))
        ((1 - x) / (((1 - x) ^ (2 : ℕ) : ℝ) ^ (2 : ℕ))) x := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hinv.mul_const (1 / 2 : ℝ)
  convert hu.sub hhalf using 1
  have hne1 : 1 - x ≠ 0 := by
    linarith
  field_simp [hne1]

/-- Helper for Proposition 1.10.12: the explicit derivative is strictly decreasing on
`(-∞, 1)`. -/
lemma lagrangianRelaxationExampleClosedFormDeriv_strictAntiOn :
    StrictAntiOn lagrangianRelaxationExampleClosedFormDeriv D := by
  -- The second derivative is strictly negative everywhere on the interval.
  have hconv : Convex ℝ (Iio (1 : ℝ)) := convex_Iio (1 : ℝ)
  refine strictAntiOn_of_deriv_neg hconv
    lagrangianRelaxationExampleClosedFormDeriv_continuousOn ?_
  intro x hx
  have hxD : x ∈ D := interior_subset hx
  rw [show deriv lagrangianRelaxationExampleClosedFormDeriv x =
      -1 - ((1 - x) ^ (3 : ℕ))⁻¹ by
      exact (lagrangianRelaxationExampleClosedFormDeriv_hasDerivAt hxD).deriv]
  have hx0 : 0 < 1 - x := by
    have hxlt : x < 1 := by
      simpa using hx
    linarith
  have hcubeInv : 0 < (((1 - x) ^ (3 : ℕ) : ℝ)⁻¹) := by
    positivity
  linarith

/-- Helper for Proposition 1.10.12: the real closed form is strictly concave on `(-∞, 1)`. -/
lemma lagrangianRelaxationExample_closedForm_strictConcaveOn :
    StrictConcaveOn ℝ D lagrangianRelaxationExampleClosedForm := by
  -- Transfer the strict antitonicity of the explicit derivative to `deriv closedForm`.
  have hantiDeriv :
      StrictAntiOn (deriv lagrangianRelaxationExampleClosedForm) (interior D) := by
    simpa using
      (lagrangianRelaxationExampleClosedFormDeriv_strictAntiOn.congr
        (fun x hx ↦ (lagrangianRelaxationExampleClosedForm_deriv hx).symm))
  have hconv : Convex ℝ (Iio (1 : ℝ)) := convex_Iio (1 : ℝ)
  exact hantiDeriv.strictConcaveOn_of_deriv hconv
    lagrangianRelaxationExampleClosedForm_continuousOn

/-- Helper for Proposition 1.10.12: the derivative of the closed form vanishes at the textbook
critical point `λ_*`. -/
lemma lagrangianRelaxationExampleClosedForm_deriv_eq_zero_at_lambdaStar :
    deriv lagrangianRelaxationExampleClosedForm lagrangianRelaxationExampleLambdaStar = 0 := by
  -- Substitute `1 - λ_* = (1 / 2)^(1 / 3)` and use the cubic identity `((1 / 2)^(1 / 3))^3 = 1/2`.
  have hstar :
      lagrangianRelaxationExampleLambdaStar ∈ D := by
    unfold lagrangianRelaxationExampleLambdaStar
    have hpos : 0 < Real.rpow (1 / 2 : ℝ) (1 / 3 : ℝ) := by
      exact Real.rpow_pos_of_pos (by norm_num) _
    simpa using sub_lt_self (1 : ℝ) hpos
  rw [lagrangianRelaxationExampleClosedForm_deriv hstar]
  have hr_pos : 0 < Real.rpow (1 / 2 : ℝ) (1 / 3 : ℝ) := by
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hr_ne : Real.rpow (1 / 2 : ℝ) (1 / 3 : ℝ) ≠ 0 := ne_of_gt hr_pos
  have hcube :
      (Real.rpow (1 / 2 : ℝ) (1 / 3 : ℝ)) ^ (3 : ℕ) = (1 / 2 : ℝ) := by
    have h := Real.rpow_inv_rpow
      (show 0 ≤ (1 / 2 : ℝ) by norm_num)
      (show (3 : ℝ) ≠ 0 by norm_num)
    simpa [one_div, Real.rpow_natCast] using h
  unfold lagrangianRelaxationExampleClosedFormDeriv lagrangianRelaxationExampleLambdaStar
  field_simp [hr_ne]
  nlinarith [hcube]

/-- Helper for Proposition 1.10.12: the textbook critical point `λ_*` is a global maximizer of the
real closed form on `(-∞, 1)`. -/
lemma lagrangianRelaxationExample_closedForm_isMaxOn_lambdaStar :
    IsMaxOn lagrangianRelaxationExampleClosedForm D
      lagrangianRelaxationExampleLambdaStar := by
  -- Use the strict concavity route to make the derivative sign test stable on both sides of `λ_*`.
  have hstar :
      lagrangianRelaxationExampleLambdaStar ∈ D := by
    unfold lagrangianRelaxationExampleLambdaStar
    have hpos : 0 < Real.rpow (1 / 2 : ℝ) (1 / 3 : ℝ) := by
      exact Real.rpow_pos_of_pos (by norm_num) _
    simpa using sub_lt_self (1 : ℝ) hpos
  have hstarlt : lagrangianRelaxationExampleLambdaStar < 1 := hstar
  have hcontAt :
      ContinuousAt lagrangianRelaxationExampleClosedForm
        lagrangianRelaxationExampleLambdaStar := by
    have hne : 1 - lagrangianRelaxationExampleLambdaStar ≠ 0 := by
      linarith
    change ContinuousAt
      (fun t : ℝ ↦ t - (1 / 2 : ℝ) * t ^ (2 : ℕ) - (1 - t)⁻¹ * (1 / 2 : ℝ) + (1 / 2 : ℝ))
      lagrangianRelaxationExampleLambdaStar
    exact
      (show ContinuousAt
        (fun t : ℝ ↦ t - (1 / 2 : ℝ) * t ^ (2 : ℕ) - (1 - t)⁻¹ * (1 / 2 : ℝ) + (1 / 2 : ℝ))
        lagrangianRelaxationExampleLambdaStar by
        fun_prop (disch := assumption))
  have hdiffLeft :
      DifferentiableOn ℝ lagrangianRelaxationExampleClosedForm
        (Iio lagrangianRelaxationExampleLambdaStar) := by
    intro x hx
    exact
      (lagrangianRelaxationExampleClosedForm_differentiableAt
        (show x ∈ D from lt_trans hx hstarlt)).differentiableWithinAt
  have hdiffRight :
      DifferentiableOn ℝ lagrangianRelaxationExampleClosedForm
        (Ioo lagrangianRelaxationExampleLambdaStar 1) := by
    intro x hx
    exact (lagrangianRelaxationExampleClosedForm_differentiableAt hx.2).differentiableWithinAt
  have hanti :
      AntitoneOn (deriv lagrangianRelaxationExampleClosedForm) D := by
    exact lagrangianRelaxationExample_closedForm_strictConcaveOn.concaveOn.antitoneOn_deriv
      (fun x hx ↦ lagrangianRelaxationExampleClosedForm_differentiableAt hx)
  refine isMaxOn_Iio_of_deriv hcontAt hdiffLeft hdiffRight ?_ ?_
  · intro x hx
    -- To the left of `λ_*`, antitonicity forces `φ'(x) ≥ φ'(λ_*) = 0`.
    have hxD : x ∈ D := by
      exact lt_trans hx hstarlt
    have hle :=
      hanti hxD hstar hx.le
    simpa [lagrangianRelaxationExampleClosedForm_deriv_eq_zero_at_lambdaStar,
      lagrangianRelaxationExampleClosedForm_deriv hxD] using hle
  · intro x hx
    -- To the right of `λ_*`, the same antitonicity gives `φ'(x) ≤ φ'(λ_*) = 0`.
    have hle := hanti hstar hx.2 hx.1.le
    simpa [lagrangianRelaxationExampleClosedForm_deriv_eq_zero_at_lambdaStar,
      lagrangianRelaxationExampleClosedForm_deriv hx.2] using hle

-- Proof sketch: compute the first and second derivatives of `ψ` on `(-∞, 1)`, deduce strict
-- concavity from `ψ''(λ) < 0`, and solve the critical-point equation to identify the unique
-- maximizer.
/-- Proposition 1.10.12: a scalar `λ` lies in `(-∞, 1)` and is a global maximizer of the example
dual function on that interval exactly when `λ = 1 - (1 / 2)^(1 / 3)`. -/
theorem lagrangianRelaxationExample_dualFunction_isMaxOn_iff
    (lam : ℝ) :
    lam ∈ D ∧ IsMaxOn ψ D lam ↔
      lam = lagrangianRelaxationExampleLambdaStar := by
  constructor
  · rintro ⟨h_lam, hmax⟩
    -- Transport the maximizer statement to the real closed form and use strict concavity.
    have hmaxClosed :
        IsMaxOn lagrangianRelaxationExampleClosedForm D lam :=
      (lagrangianRelaxationExample_closedForm_isMaxOn_iff h_lam).1 hmax
    have hstar :
        lagrangianRelaxationExampleLambdaStar ∈ D := by
      unfold lagrangianRelaxationExampleLambdaStar
      have hpos : 0 < Real.rpow (1 / 2 : ℝ) (1 / 3 : ℝ) := by
        exact Real.rpow_pos_of_pos (by norm_num) _
      simpa using sub_lt_self (1 : ℝ) hpos
    have hstarlt : lagrangianRelaxationExampleLambdaStar < 1 := hstar
    exact lagrangianRelaxationExample_closedForm_strictConcaveOn.eq_of_isMaxOn
      hmaxClosed
      lagrangianRelaxationExample_closedForm_isMaxOn_lambdaStar
      h_lam
      hstar
  · intro hlam
    constructor
    · -- The explicit formula for `λ_*` visibly lies in `(-∞, 1)`.
      subst hlam
      unfold lagrangianRelaxationExampleLambdaStar
      have hpos : 0 < Real.rpow (1 / 2 : ℝ) (1 / 3 : ℝ) := by
        exact Real.rpow_pos_of_pos (by norm_num) _
      simpa using sub_lt_self (1 : ℝ) hpos
    · -- Push the real closed-form maximizer back to the owner-side `EReal` dual function.
      subst hlam
      exact (lagrangianRelaxationExample_closedForm_isMaxOn_iff (by
        unfold lagrangianRelaxationExampleLambdaStar
        have hpos : 0 < Real.rpow (1 / 2 : ℝ) (1 / 3 : ℝ) := by
          exact Real.rpow_pos_of_pos (by norm_num) _
        simpa using sub_lt_self (1 : ℝ) hpos)).2
          lagrangianRelaxationExample_closedForm_isMaxOn_lambdaStar

/-- The scalar maximizer `λ_*` lies in the effective dual domain `(-∞, 1)`. -/
theorem lagrangianRelaxationExampleLambdaStar_lt_one :
    lagrangianRelaxationExampleLambdaStar < 1 := by
  change lagrangianRelaxationExampleLambdaStar ∈ Iio (1 : ℝ)
  exact
    ((lagrangianRelaxationExample_dualFunction_isMaxOn_iff
      lagrangianRelaxationExampleLambdaStar).2 rfl).1

/-- The owner multiplier `single 0 λ_*` lies in the dual-feasible set. -/
theorem lagrangianRelaxationExampleLambdaStar_mem_dualFeasibleSet :
    single 0 lagrangianRelaxationExampleLambdaStar ∈
      lagrangianRelaxationExample.dualFeasibleSet := by
  rw [lagrangianRelaxationExample.mem_dualFeasibleSet_iff]
  constructor
  · -- Dual-domain membership is the scalar inequality `λ_* < 1`.
    exact (lagrangianRelaxationExampleMultiplier_mem_dualDomain_iff
      lagrangianRelaxationExampleLambdaStar).2 lagrangianRelaxationExampleLambdaStar_lt_one
  · intro j
    fin_cases j
    -- The nonnegativity condition follows from `(1 / 2)^(1 / 3) ≤ 1`.
    have hrpow_le_one :
        Real.rpow (1 / 2 : ℝ) (1 / 3 : ℝ) ≤ 1 := by
      have hmono :=
        Real.monotoneOn_rpow_Ici_of_exponent_nonneg (show 0 ≤ (1 / 3 : ℝ) by norm_num)
      simpa using hmono
        (by norm_num : (1 / 2 : ℝ) ∈ Set.Ici 0)
        (by norm_num : (1 : ℝ) ∈ Set.Ici 0)
        (by norm_num : (1 / 2 : ℝ) ≤ 1)
    unfold lagrangianRelaxationExampleLambdaStar
    simpa using sub_nonneg.mpr hrpow_le_one

/-- The owner multiplier `single 0 λ_*` maximizes the example dual function on the dual-feasible
set. -/
theorem lagrangianRelaxationExampleLambdaStar_isMaxOn_dualFeasibleSet :
    IsMaxOn lagrangianRelaxationExample.dualFunction
      lagrangianRelaxationExample.dualFeasibleSet
      (single 0 lagrangianRelaxationExampleLambdaStar) := by
  rw [isMaxOn_iff]
  intro μ hμ
  -- Every one-dimensional multiplier is determined by its unique coordinate.
  have hμ_eq : μ = single 0 (μ 0) := by
    ext i
    fin_cases i
    simp
  have hμ_dom :
      μ ∈ lagrangianRelaxationExample.dualDomain :=
    (lagrangianRelaxationExample.mem_dualFeasibleSet_iff.mp hμ).1
  have hscalar : μ 0 < 1 := by
    have hscalarDom : single 0 (μ 0) ∈ lagrangianRelaxationExample.dualDomain := by
      rwa [hμ_eq]
    exact (lagrangianRelaxationExampleMultiplier_mem_dualDomain_iff (μ 0)).1 hscalarDom
  have hscalarMax :
      IsMaxOn ψ D lagrangianRelaxationExampleLambdaStar :=
    ((lagrangianRelaxationExample_dualFunction_isMaxOn_iff
      lagrangianRelaxationExampleLambdaStar).2 rfl).2
  -- Reduce the owner comparison to the scalar comparison supplied by the maximizer theorem.
  have hleScalar :
      ψ (μ 0) ≤ ψ lagrangianRelaxationExampleLambdaStar :=
    (isMaxOn_iff.mp hscalarMax) (μ 0) hscalar
  rw [hμ_eq]
  simpa [Function.comp_apply] using hleScalar

-- Proof sketch: substitute `λ_* = 1 - (1 / 2)^(1 / 3)` into the explicit trajectory formula
-- `x(λ) = (1 - λ, (1 - λ)⁻¹)` and simplify both coordinates.
/-- The textbook trajectory evaluated at `λ_*` has coordinates `(2^(-1 / 3), 2^(1 / 3))`. -/
theorem lagrangianRelaxationExampleTrajectory_atLambdaStar :
    lagrangianRelaxationExampleMinimizerTrajectory lagrangianRelaxationExampleLambdaStar =
      WithLp.toLp 2
        ![Real.rpow (2 : ℝ) (-(1 / 3 : ℝ)),
          Real.rpow (2 : ℝ) (1 / 3 : ℝ)] := by
  -- Evaluate the explicit trajectory coordinatewise at `λ_*`.
  ext i
  fin_cases i
  · have hcoord :
        1 - lagrangianRelaxationExampleLambdaStar =
          Real.rpow (2 : ℝ) (-(1 / 3 : ℝ)) := by
      unfold lagrangianRelaxationExampleLambdaStar
      ring_nf
      convert (Real.rpow_neg_eq_inv_rpow (2 : ℝ) ((3 : ℝ)⁻¹)).symm using 1 <;> norm_num
    simpa [lagrangianRelaxationExampleMinimizerTrajectory] using hcoord
  · have hcoord :
        1 / (1 - lagrangianRelaxationExampleLambdaStar) =
          Real.rpow (2 : ℝ) (1 / 3 : ℝ) := by
      unfold lagrangianRelaxationExampleLambdaStar
      ring_nf
      simpa [one_div] using congrArg Inv.inv
        (Real.inv_rpow (show 0 ≤ (2 : ℝ) by positivity) (1 / 3 : ℝ))
    simpa [lagrangianRelaxationExampleMinimizerTrajectory] using hcoord

/-! ### Definition_1_10_13 (from Chap01) -/
noncomputable section

universe u

/- Definition 1.10.13 lies in the Chapter 1 constrained/unconstrained minimization domain.

Sampled owner-style declarations:
* `IsMinOn f Set.univ x` in mathlib, the canonical whole-space minimizer predicate;
* `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the Chapter 1 owner for a
  feasible set together with its real-valued objective;
* `SetConstrainedMinimizationProblem.optimalValue` and
  `SetConstrainedMinimizationProblem.optimalValue_eq_of_isMinOn` in `Chap01/Definition_1_3_7`,
  the derived optimal-value API for that owner object;
* `PenaltyFunctionMethod.toSequentialUnconstrainedMinimizationScheme` in
  `Chap01/Algorithm_1_10_11`, the nearby source-facing algorithm that bridges to this scheme
  owner.

Best owner abstraction:
* source-facing: `SequentialUnconstrainedMinimizationScheme Q`;
* core/canonical: for each index `k`, the Chapter 1 owner
  `SetConstrainedMinimizationProblem Q` specialized to feasible set `Set.univ`;
* bridge/view: the canonical owner problem `scheme.auxiliaryProblem k`.

Primitive data:
* the auxiliary objective family `Φₖ : Q → ℝ`;
* the iterate family `xₖ : Q`;
* the minimizing certificates `IsMinOn (Φₖ) Set.univ xₖ`.

Derived API:
* the associated Chapter 1 owner problem on the subtype `Q`;
* its optimal value and attained-value identities.

Source/core/bridge triage:
* source-facing: the sequential unconstrained minimization scheme itself;
* core/canonical: `SetConstrainedMinimizationProblem Q`;
* bridge/view: packaging each `Φₖ` as the owner problem with feasible set `Set.univ`.

The file therefore keeps the source-facing scheme structure and reuses the Chapter 1 owner object
directly for optimal-value language, instead of introducing a parallel public auxiliary-problem
wrapper. -/

/-- Definition 1.10.13: A sequential unconstrained minimization scheme for a nonlinear
optimization problem with functional constraints consists of auxiliary unconstrained objective
functions `Φₖ : Q → ℝ` and iterates `xₖ ∈ Q` such that each `xₖ` minimizes `Φₖ` on `Q`. The
owner abstraction is the intrinsic feasible type `Q`; any surrounding constrained-problem package
or ambient-set presentation is auxiliary context used only when specializing this generic scheme.
The auxiliary objectives are intended to approximate a solution of the original constrained
problem.
-/
structure SequentialUnconstrainedMinimizationScheme (Q : Type u) where
  auxiliaryObjectives : ℕ+ → Q → ℝ
  iterates : ℕ+ → Q
  isMinOn_auxiliaryObjective (k : ℕ+) :
    IsMinOn (auxiliaryObjectives k) Set.univ (iterates k)

namespace SequentialUnconstrainedMinimizationScheme

variable {Q : Type u}

/-- A sequential unconstrained minimization scheme can be used as its underlying sequence of
iterates in the feasible-set subtype. -/
instance :
    CoeFun (SequentialUnconstrainedMinimizationScheme Q) (fun _ ↦ ℕ+ → Q) where
  coe scheme := scheme.iterates

/-- The `k`-th auxiliary minimization problem attached to a sequential unconstrained
minimization scheme. This is the canonical Chapter 1 owner problem on the feasible-set subtype
`Q`, with feasible set `Set.univ`. -/
abbrev auxiliaryProblem (scheme : SequentialUnconstrainedMinimizationScheme Q) (k : ℕ+) :
    SetConstrainedMinimizationProblem Q :=
  .unconstrained (scheme.auxiliaryObjectives k)

/-- The optimal value of the `k`-th auxiliary problem is attained at the selected iterate. -/
theorem auxiliaryProblem_optimalValue_eq_iterateValue
    (scheme : SequentialUnconstrainedMinimizationScheme Q) (k : ℕ+) :
    (scheme.auxiliaryProblem k).optimalValue =
      (scheme.auxiliaryObjectives k (scheme k) : EReal) :=
  by
    simpa [auxiliaryProblem] using
      (scheme.auxiliaryProblem k).optimalValue_eq_of_isMinOn
        (by simp)
        (scheme.isMinOn_auxiliaryObjective k)

end SequentialUnconstrainedMinimizationScheme

/-! ### Definition_1_10_14 (from Chap01) -/
variable {E : Type u} [TopologicalSpace E]

/- Primary domain: continuous real-valued maps that detect a subset through their zero set.

Sampled owner-style declarations:
* `C(E, ℝ)`, the canonical owner for continuous real-valued maps;
* `Set.EqOn`, the canonical localized equality predicate for functions on a set;
* `IsBarrierFunctionOn` in `Chap01/Definition_1_10_18`, the nearby chapter owner predicate on a
  bundled continuous map;
* `ContDiffMapSupportedIn.zero_on_compl` in mathlib, a nearby owner property organized around a
  vanishing condition rather than extra wrapper data.

Best owner abstraction:
* source-facing: `IsPenaltyFunction F Phi`;
* core/canonical: the bundled continuous map `Phi : C(E, ℝ)`;
* bridge/view: the exact zero-locus identity `F = Phi ⁻¹' {0}` and its pointwise reformulations.

Primitive data:
* `Phi` is globally nonnegative;
* the exact zero-locus identity `F = Phi ⁻¹' {0}`.

Derived API:
* the pointwise characterizations `x ∈ F ↔ Phi x = 0` and `Phi x = 0 ↔ x ∈ F`;
* `EqOn Phi 0 F`;
* strict positivity on `Fᶜ`;
* closedness of `F`.

The source phrase "closed set" is therefore redundant here: once the zero set is part of the owner
data, closedness follows immediately from continuity. -/

/-- Definition 1.10.14: for a set `F` in the ambient space, a continuous real-valued map is a
penalty function for `F` if it is nonnegative and vanishes exactly on `F`. The customary
strict-positivity statement on the complement is derived API. -/
class IsPenaltyFunction (F : Set E) (Phi : C(E, ℝ)) : Prop where
  nonneg (x : E) : 0 ≤ Phi x
  zeroSet_eq : F = Phi ⁻¹' ({0} : Set ℝ)

namespace IsPenaltyFunction

variable {F : Set E} {Phi : C(E, ℝ)}

/-- A penalty function vanishes exactly on the underlying set. -/
theorem mem_iff_eq_zero (hPhi : IsPenaltyFunction F Phi) {x : E} :
    x ∈ F ↔ Phi x = 0 := by
  rw [hPhi.zeroSet_eq]
  simp

/-- The defining zero-locus condition can also be read in the codomain-to-domain direction. -/
theorem eq_zero_iff_mem (hPhi : IsPenaltyFunction F Phi) {x : E} :
    Phi x = 0 ↔ x ∈ F := by
  simpa using hPhi.mem_iff_eq_zero.symm

/-- A penalty function vanishes on the underlying set. -/
theorem eqOn_zero (hPhi : IsPenaltyFunction F Phi) : EqOn Phi 0 F := by
  intro x hx
  simpa using hPhi.mem_iff_eq_zero.mp hx

/-- A penalty function is strictly positive on the complement of its zero set. -/
theorem pos_of_notMem (hPhi : IsPenaltyFunction F Phi) {x : E} (hx : x ∉ F) :
    0 < Phi x := by
  have hne : Phi x ≠ 0 := by
    intro hx0
    exact hx (hPhi.mem_iff_eq_zero.mpr hx0)
  exact lt_of_le_of_ne (hPhi.nonneg x) (by simpa [eq_comm] using hne)

/-- The zero set of a penalty function is closed, so the underlying set is automatically closed. -/
theorem isClosed (hPhi : IsPenaltyFunction F Phi) : IsClosed F := by
  rw [hPhi.zeroSet_eq]
  exact isClosed_singleton.preimage Phi.continuous

end IsPenaltyFunction

/-- A penalty-function hypothesis canonically supplies the owner-level vanishing condition on its
underlying set. -/
instance {F : Set E} {Phi : C(E, ℝ)} [hPhi : IsPenaltyFunction F Phi] : Fact (EqOn Phi 0 F) :=
  ⟨hPhi.eqOn_zero⟩

/-! ### Definition_1_10_15 (from Chap01) -/
open scoped BigOperators

variable {X : Type*} [TopologicalSpace X]
variable {ι : Type*}

/- Definition 1.10.15 lies in the chapter's penalty-function domain for finitely many continuous
inequality constraints.

Relevant owner-style declarations sampled before refinement:
* `IsPenaltyFunction` in `Definition_1_10_14`
* `constraintSet` in `Proposition_1_10_17`, the chapter's finite-family feasible-set owner
* `PosPart.posPart` together with `posPart_def`
* the canonical ring structure on `C(X, ℝ)`, including pointwise sums and powers
* the pointwise order/lattice structure on `C(X, ℝ)`

Best owner abstraction:
* source-facing: the two explicit penalty maps attached to a finite constraint family
* core/canonical: the bundled continuous maps `C(X, ℝ)` together with `IsPenaltyFunction`
* bridge/view: the pointwise evaluation formulas recovering the textbook sums of positive parts

Primitive data:
* a finite family `constraints : ι → C(X, ℝ)` with `[Fintype ι]`

Derived API:
* the feasible-set owner `constraintSet constraints`
* the quadratic and nonsmooth penalty maps
* their pointwise formulas and their certification as penalty functions

The Euclidean model `ℝⁿ` is not used by the constructions themselves, so the owner declarations are
kept at the weaker canonical level of an arbitrary topological space with real-valued continuous
constraints. -/

section

variable [Fintype ι] (constraints : ι → C(X, ℝ))

/-- Definition 1.10.15: for continuous constraint functions `f₁, …, f_m : ℝⁿ → ℝ`, the feasible
set `constraintSet constraints` is cut out by the inequalities `constraints j x ≤ 0`, and one
quadratic penalty for it is
`x ↦ ∑ j, ((fⱼ x)⁺)^2`, where `a⁺ = max a 0` is mathlib's positive-part notation. The nonsmooth
penalty is introduced below as a companion definition. -/
def quadraticPenalty : C(X, ℝ) :=
  ∑ j : ι, ((constraints j)⁺) ^ (2 : ℕ)

@[simp] theorem quadraticPenalty_apply (x : X) :
    quadraticPenalty constraints x = ∑ j : ι, ((constraints j x)⁺) ^ (2 : ℕ) := by
  simp [quadraticPenalty, posPart_def]

/-- The nonsmooth penalty associated to finitely many continuous inequality constraints is the sum
of the positive parts of the constraint violations. -/
def nonsmoothPenalty : C(X, ℝ) :=
  ∑ j : ι, (constraints j)⁺

@[simp] theorem nonsmoothPenalty_apply (x : X) :
    nonsmoothPenalty constraints x = ∑ j : ι, (constraints j x)⁺ := by
  simp [nonsmoothPenalty, posPart_def]

/-- The quadratic penalty is a penalty function for the feasible set cut out by the given
continuous inequality constraints. -/
-- Proof sketch: continuity follows from continuity of each constraint, the positive-part map, the
-- squaring map, and finite sums. On the feasible set every positive part vanishes; outside the
-- feasible set some constraint is positive, so the corresponding summand is strictly positive.
theorem quadraticPenalty_isPenaltyFunction :
    IsPenaltyFunction (constraintSet constraints)
      (quadraticPenalty constraints) := by
  refine ⟨?_, ?_⟩
  · intro x
    rw [quadraticPenalty_apply]
    exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  · ext x
    rw [Set.mem_preimage, Set.mem_singleton_iff, mem_constraintSet_iff, quadraticPenalty_apply]
    constructor
    · intro hx
      refine (Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ sq_nonneg _).2 ?_
      intro j _
      rw [posPart_eq_zero.mpr (hx j)]
      simp
    · intro hx j
      have hzero :
          ∀ j ∈ (Finset.univ : Finset ι), ((constraints j x)⁺) ^ (2 : ℕ) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ sq_nonneg _).mp hx
      exact posPart_eq_zero.mp <| sq_eq_zero_iff.mp <| hzero j (Finset.mem_univ j)

/-- The nonsmooth penalty is a penalty function for the feasible set cut out by the given
continuous inequality constraints. -/
-- Proof sketch: use continuity of the positive-part map and finite sums. Feasible points make
-- every positive part vanish, while an infeasible point has at least one violated constraint whose
-- positive part contributes a strictly positive summand.
theorem nonsmoothPenalty_isPenaltyFunction :
    IsPenaltyFunction (constraintSet constraints)
      (nonsmoothPenalty constraints) := by
  refine ⟨?_, ?_⟩
  · intro x
    rw [nonsmoothPenalty_apply]
    exact Finset.sum_nonneg fun _ _ ↦ posPart_nonneg _
  · ext x
    rw [Set.mem_preimage, Set.mem_singleton_iff, mem_constraintSet_iff, nonsmoothPenalty_apply]
    constructor
    · intro hx
      refine (Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ posPart_nonneg _).2 ?_
      intro j _
      exact posPart_eq_zero.mpr (hx j)
    · intro hx j
      have hzero : ∀ j ∈ (Finset.univ : Finset ι), (constraints j x)⁺ = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ posPart_nonneg _).mp hx
      exact posPart_eq_zero.mp (hzero j (Finset.mem_univ j))

end

/-! ### Proposition_1_10_16 (from Chap01) -/
open Filter Set Topology

universe u

variable {α : Type u} [TopologicalSpace α]

namespace IsBarrierFunctionOn

/-
Source/core/bridge triage for Proposition 1.10.16:
- source-facing: the sum of two barrier functions is again a barrier on the common interior;
- core/canonical owner: the continuous maps `C(interior 𝓕, ℝ)`;
- bridge/view: restrict each owner map along `ContinuousMap.inclusion (interior_mono ...)` and add
  the resulting continuous maps on `interior (𝓕₁ ∩ 𝓕₂)`.

The restricted sum is derived entirely from the owner `ContinuousMap` API, so this file keeps the
source-facing proposition and instance at the intrinsic topological level and does not introduce a
parallel public wrapper definition specialized to Euclidean coordinates.
-/
variable {𝓕₁ 𝓕₂ : Set α}
variable (F₁ : C(interior 𝓕₁, ℝ)) (F₂ : C(interior 𝓕₂, ℝ))

/-- Restrict both summands to `interior (𝓕₁ ∩ 𝓕₂)` and add them there. -/
private abbrev interAdd : C(interior (𝓕₁ ∩ 𝓕₂), ℝ) :=
  F₁.comp (ContinuousMap.inclusion (interior_mono inter_subset_left)) +
    F₂.comp (ContinuousMap.inclusion (interior_mono inter_subset_right))

/-- Helper for Proposition 1.10.16: a point in the closure of a closed set lies either in its
interior or on its frontier. -/
private lemma mem_interior_or_frontier_of_mem_closure_of_closed
    {s : Set α} (hs : IsClosed s) {x : α} (hx : x ∈ closure s) :
    x ∈ interior s ∨ x ∈ frontier s := by
  have hx' : x ∈ s := by
    simpa [hs.closure_eq] using hx
  -- Closedness lets us turn the closure statement into the standard interior/frontier dichotomy.
  by_cases hfront : x ∈ frontier s
  · exact Or.inr hfront
  · exact Or.inl ((mem_interior_iff_notMem_frontier hx').2 hfront)

/-- Helper for Proposition 1.10.16: if a sequence in a smaller interior converges to a point that
is still interior to the larger set, continuity gives a finite limit for the restricted summand. -/
private lemma tendsto_restricted_summand_of_mem_interior
    {s 𝓕 : Set α} (F : C(interior 𝓕, ℝ)) (hsub : interior s ⊆ interior 𝓕)
    (x : ℕ → interior s) {xBar : α}
    (hx : Tendsto (fun k ↦ (x k : α)) atTop (nhds xBar))
    (hxBar : xBar ∈ interior 𝓕) :
    Tendsto (fun k ↦ F ⟨x k, hsub (x k).property⟩)
      atTop (nhds (F ⟨xBar, hxBar⟩)) := by
  let xF : ℕ → interior 𝓕 := fun k ↦ ⟨x k, hsub (x k).property⟩
  have hxF : Tendsto xF atTop (nhds ⟨xBar, hxBar⟩) := by
    -- Passing to the subtype keeps exactly the same ambient convergence.
    apply tendsto_subtype_rng.mpr
    simpa [xF] using hx
  -- Continuity of the owner map transports the convergence to a finite real limit.
  exact F.continuous.continuousAt.tendsto.comp hxF

/-- The pointwise sum of two barrier functions, restricted to `interior (𝓕₁ ∩ 𝓕₂)`, diverges to
`+∞` along sequences in that interior converging to a boundary point of `𝓕₁ ∩ 𝓕₂`. -/
-- Proof sketch: use `frontier_inter_subset` to reduce a boundary point of `𝓕₁ ∩ 𝓕₂` to the
-- boundary of one factor or the other, apply the corresponding barrier property there, and combine
-- it with continuity of the remaining summand using the standard `atTop` addition lemmas.
private theorem add_inter_tendsTo_atTop_of_tendsto_frontier
    (h₁ : IsBarrierFunctionOn 𝓕₁ F₁)
    (h₂ : IsBarrierFunctionOn 𝓕₂ F₂)
    (x : ℕ → interior (𝓕₁ ∩ 𝓕₂)) {xBar : α}
    (hx : Tendsto (fun k ↦ (x k : α)) atTop (nhds xBar))
    (hxBar : xBar ∈ frontier (𝓕₁ ∩ 𝓕₂)) :
    Tendsto
      (fun k : ℕ ↦ interAdd F₁ F₂ (x k))
      atTop (atTop : Filter ℝ) := by
  let x₁ : ℕ → interior 𝓕₁ := fun k ↦ ⟨x k, interior_mono inter_subset_left (x k).property⟩
  let x₂ : ℕ → interior 𝓕₂ := fun k ↦ ⟨x k, interior_mono inter_subset_right (x k).property⟩
  have hx₁ : Tendsto (fun k ↦ (x₁ k : α)) atTop (nhds xBar) := by
    simpa [x₁] using hx
  have hx₂ : Tendsto (fun k ↦ (x₂ k : α)) atTop (nhds xBar) := by
    simpa [x₂] using hx
  have hxCases :
      xBar ∈ frontier 𝓕₁ ∩ closure 𝓕₂ ∪ closure 𝓕₁ ∩ frontier 𝓕₂ :=
    (frontier_inter_subset 𝓕₁ 𝓕₂) hxBar
  -- Restrict the common-interior sequence to each factor so the two barrier hypotheses apply.
  rcases hxCases with hxLeft | hxRight
  · rcases hxLeft with ⟨hxBar₁, hxBar₂Closure⟩
    have hF₁ :
        Tendsto (fun k ↦ F₁ (x₁ k)) atTop (atTop : Filter ℝ) :=
      h₁.tendsTo_atTop_of_tendsto_frontier x₁ hx₁ hxBar₁
    -- In the first textbook branch, the left summand blows up and the right summand is either
    -- still finite by continuity or also blows up on its own frontier.
    rcases mem_interior_or_frontier_of_mem_closure_of_closed h₂.isClosed hxBar₂Closure with
      hxBar₂ | hxBar₂
    · have hF₂ :
          Tendsto (fun k ↦ F₂ (x₂ k)) atTop (nhds (F₂ ⟨xBar, hxBar₂⟩)) := by
        simpa [x₂] using
          tendsto_restricted_summand_of_mem_interior F₂
            (interior_mono inter_subset_right) x hx hxBar₂
      have hsum :
          Tendsto (fun k ↦ F₁ (x₁ k) + F₂ (x₂ k)) atTop (atTop : Filter ℝ) :=
        hF₁.atTop_add hF₂
      simpa [interAdd, x₁, x₂] using hsum
    · have hF₂ :
          Tendsto (fun k ↦ F₂ (x₂ k)) atTop (atTop : Filter ℝ) :=
        h₂.tendsTo_atTop_of_tendsto_frontier x₂ hx₂ hxBar₂
      have hle : (fun k ↦ F₁ (x₁ k)) ≤ᶠ[atTop] fun k ↦ F₁ (x₁ k) + F₂ (x₂ k) := by
        filter_upwards [hF₂.eventually (eventually_ge_atTop 0)] with k hk
        exact le_add_of_nonneg_right hk
      have hsum :
          Tendsto (fun k ↦ F₁ (x₁ k) + F₂ (x₂ k)) atTop (atTop : Filter ℝ) :=
        tendsto_atTop_mono' atTop hle hF₁
      simpa [interAdd, x₁, x₂] using hsum
  · rcases hxRight with ⟨hxBar₁Closure, hxBar₂⟩
    have hF₂ :
        Tendsto (fun k ↦ F₂ (x₂ k)) atTop (atTop : Filter ℝ) :=
      h₂.tendsTo_atTop_of_tendsto_frontier x₂ hx₂ hxBar₂
    -- The symmetric branch interchanges the roles of the two factors.
    rcases mem_interior_or_frontier_of_mem_closure_of_closed h₁.isClosed hxBar₁Closure with
      hxBar₁ | hxBar₁
    · have hF₁ :
          Tendsto (fun k ↦ F₁ (x₁ k)) atTop (nhds (F₁ ⟨xBar, hxBar₁⟩)) := by
        simpa [x₁] using
          tendsto_restricted_summand_of_mem_interior F₁
            (interior_mono inter_subset_left) x hx hxBar₁
      have hsum :
          Tendsto (fun k ↦ F₁ (x₁ k) + F₂ (x₂ k)) atTop (atTop : Filter ℝ) :=
        hF₁.add_atTop hF₂
      simpa [interAdd, x₁, x₂] using hsum
    · have hF₁ :
          Tendsto (fun k ↦ F₁ (x₁ k)) atTop (atTop : Filter ℝ) :=
        h₁.tendsTo_atTop_of_tendsto_frontier x₁ hx₁ hxBar₁
      have hle : (fun k ↦ F₂ (x₂ k)) ≤ᶠ[atTop] fun k ↦ F₁ (x₁ k) + F₂ (x₂ k) := by
        filter_upwards [hF₁.eventually (eventually_ge_atTop 0)] with k hk
        exact le_add_of_nonneg_left hk
      have hsum :
          Tendsto (fun k ↦ F₁ (x₁ k) + F₂ (x₂ k)) atTop (atTop : Filter ℝ) :=
        tendsto_atTop_mono' atTop hle hF₂
      simpa [interAdd, x₁, x₂] using hsum

/-- Proposition 1.10.16: if `F₁` and `F₂` are barrier functions for `𝓕₁` and `𝓕₂` and
`interior (𝓕₁ ∩ 𝓕₂)` is nonempty, then their pointwise sum, restricted to the common interior,
is a barrier function for `𝓕₁ ∩ 𝓕₂`. -/
theorem add_inter
    (h₁ : IsBarrierFunctionOn 𝓕₁ F₁)
    (h₂ : IsBarrierFunctionOn 𝓕₂ F₂)
    (hinter : (interior (𝓕₁ ∩ 𝓕₂)).Nonempty) :
    IsBarrierFunctionOn (𝓕₁ ∩ 𝓕₂)
      (F₁.comp (ContinuousMap.inclusion (interior_mono inter_subset_left)) +
        F₂.comp (ContinuousMap.inclusion (interior_mono inter_subset_right))) := by
  change IsBarrierFunctionOn (𝓕₁ ∩ 𝓕₂) (interAdd F₁ F₂)
  let _ : Fact (IsClosed (𝓕₁ ∩ 𝓕₂)) := ⟨h₁.isClosed.inter h₂.isClosed⟩
  -- The wrapper only packages the repaired frontier-growth proof for the restricted sum.
  refine
    { interior_nonempty := hinter
      tendsTo_atTop_of_tendsto_frontier := ?_ }
  intro x xBar hx hxBar
  exact add_inter_tendsTo_atTop_of_tendsto_frontier F₁ F₂ h₁ h₂ x hx hxBar

instance
    [h₁ : IsBarrierFunctionOn 𝓕₁ F₁]
    [h₂ : IsBarrierFunctionOn 𝓕₂ F₂]
    [Fact ((interior (𝓕₁ ∩ 𝓕₂)).Nonempty)] :
    IsBarrierFunctionOn (𝓕₁ ∩ 𝓕₂)
      (F₁.comp (ContinuousMap.inclusion (interior_mono inter_subset_left)) +
        F₂.comp (ContinuousMap.inclusion (interior_mono inter_subset_right))) :=
  add_inter F₁ F₂ h₁ h₂ Fact.out

end IsBarrierFunctionOn
