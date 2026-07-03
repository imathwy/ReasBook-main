import Mathlib
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_1_10_1 (from Chap01) -/
universe u v w

/- Theorem 1.10.1 lies in the order-theoretic weak-duality domain.

Relevant owner declarations sampled before refining:
* `iSup_iInf_le_iInf_iSup`, the complete-lattice maximin `≤` minimax owner theorem
* `ciSup_le`, the conditionally complete introduction rule for indexed suprema
* `le_ciInf`, the conditionally complete introduction rule for indexed infima
* `ciInf_le` and `le_ciSup`, the slice-evaluation rules supplying the pointwise comparison

Best owner abstraction:
* the indexed `⨅`/`⨆` API of `ConditionallyCompleteLattice`

Primitive data:
* the payoff `F : Q₁ → Q₂ → α`
* nonempty index types `Q₁`, `Q₂`
* lower bounded `x`-slices and upper bounded `u`-slices

Derived API:
* the source-facing weak-duality inequality
  `⨆ u, ⨅ x, F x u ≤ ⨅ x, ⨆ u, F x u`

Source/core/bridge triage:
* source-facing: the textbook weak-duality inequality
* core/canonical: the indexed `⨅`/`⨆` operators in a `ConditionallyCompleteLattice`
* bridge/view: `iSup_iInf_le_iInf_iSup`, the complete-lattice analogue that identifies the same
  owner pattern at a stronger ambient level

Accordingly this file keeps only the source-facing theorem and reuses the canonical indexed
`iInf`/`iSup` API directly, rather than introducing any local maximin/minimax wrapper layer.
-/

/-- Theorem 1.10.1: for a payoff on nonempty index sets valued in a conditionally complete
lattice, if each lower slice `{F(x, u) | x ∈ Q₁}` is bounded below and each upper slice
`{F(x, u) | u ∈ Q₂}` is bounded above, then the maximin value is bounded above by the minimax
value. Specializing to `α = ℝ` recovers the textbook real-valued weak-duality inequality. -/
theorem maximin_le_minimax
    {Q₁ : Type u} {Q₂ : Type v} {α : Type w} [ConditionallyCompleteLattice α]
    [Nonempty Q₁] [Nonempty Q₂] (F : Q₁ → Q₂ → α)
    (hbelow : ∀ u, BddBelow (Set.range fun x ↦ F x u))
    (habove : ∀ x, BddAbove (Set.range (F x))) :
    (⨆ u, ⨅ x, F x u) ≤ ⨅ x, ⨆ u, F x u := by
  -- Fix a column index and reduce the target to the corresponding inequality for that slice.
  refine ciSup_le fun u ↦ ?_
  -- For this fixed column, prove it is below every row supremum and then introduce the infimum.
  refine le_ciInf fun x ↦ ?_
  -- Compare the column infimum to the entry `F x u`, then compare that entry to the row supremum.
  exact (ciInf_le (hbelow u) x).trans (le_ciSup (habove x) u)

/-! ### Definition_1_10_2 (from Chap01) -/
noncomputable section

universe u

open scoped ConstrainedArgmin

/- Definition 1.10.2 lies in the finite-constraint Lagrangian-duality domain.

Sampled owner declarations in this domain:
* `FunctionalConstraintsMinimizationProblem X m` together with
  `FunctionalConstraintsMinimizationProblem.constraintVector` and
  `FunctionalConstraintsMinimizationProblem.mem_feasibleSet_iff` in `Chap01/Definition_1_1_1`,
  the chapter owner for finitely many scalar constraints on an ambient feasible subtype;
* `SetConstrainedMinimizationProblem`, `argmin[Q] f`, and
  `SetConstrainedMinimizationProblem.optimalValue` in `Chap01/Definition_1_3_3` and
  `Chap01/Definition_1_3_7`, the chapter owners for minimizer sets and optimal values of ambient
  constrained problems;
* `problem.constrainedAuxiliaryOptimalValue` in `Chap02/Lemma_2_21`, which already routes a
  Lagrangian-derived value function through `SetConstrainedMinimizationProblem.optimalValue`.

Best owner abstraction:
* source-facing: `LagrangianProblem Q m`, whose primitive data are exactly an ambient objective
  and finitely many inequality constraints on `Q`;
* core/canonical: the chapter owners `FunctionalConstraintsMinimizationProblem Q m` for the
  feasible-set / constraint-vector layer and `SetConstrainedMinimizationProblem Q` together with
  `argmin[Q]` / `optimalValue` for ambient minimization;
* bridge/view: `toFunctionalConstraintsMinimizationProblem`,
  `toSetConstrainedMinimizationProblem`, and the fixed-multiplier minimizer set
  `lagrangianMinimizers`.

Primitive data:
* `objective : Q → ℝ`
* `constraints : Fin m → Q → ℝ`

Derived API:
* the objective coercion
* `constraintVector`
* `feasibleSet`
* `toSetConstrainedMinimizationProblem`
* `primalOptimalValue`
* `lagrangian`
* `dualFunction`
* `lagrangianMinimizers`
* `dualOptimalValue`

This refinement keeps the textbook owner `LagrangianProblem`, but deletes the duplicate ambient
optimal-value and minimizer-set wheels by routing them through the existing Chapter 1 owners
`SetConstrainedMinimizationProblem.optimalValue` and `argmin[Q]`. -/

/-- Definition 1.10.2: A Lagrangian problem is specified by a domain `Q`, an objective function
`f₀ : Q → ℝ`, and finitely many inequality constraint functions `fⱼ : Q → ℝ` for
`j = 1, ..., m`; the feasible set, primal optimal value, Lagrangian, dual function and its
domain, the Lagrangian minimizers, and the dual optimal value are the derived notions defined
below. -/
structure LagrangianProblem (Q : Type u) (m : ℕ) where
  objective : Q → ℝ
  constraints : Fin m → Q → ℝ

/-- A Lagrangian problem coerces to its objective function. -/
instance : CoeFun (LagrangianProblem Q m) (fun _ ↦ Q → ℝ) where
  coe problem := problem.objective

namespace LagrangianProblem

variable {Q : Type u} {m : ℕ}

/-- Evaluating a Lagrangian problem at a point returns its objective value. -/
@[simp] theorem coe_apply (problem : LagrangianProblem Q m) (x : Q) :
    problem x = problem.objective x :=
  rfl

/-- The Chapter 1 functional-constraint owner attached to a Lagrangian problem by taking the
ambient domain `Q` as the basic feasible set and recording that all constraint senses are `≤`.
-/
def toFunctionalConstraintsMinimizationProblem (problem : LagrangianProblem Q m) :
    FunctionalConstraintsMinimizationProblem Q m where
  basicFeasibleSet := Set.univ
  objective := fun x ↦ problem x
  constraints := fun j x ↦ problem.constraints j x
  senses := fun _ ↦ .le

end LagrangianProblem

/-- The nonnegative orthant `ℝ₊^m = {λ ∈ ℝ^m | λⱼ ≥ 0 for all `j`}`. -/
def EuclideanSpace.nonnegativeOrthant (m : ℕ) : Set (EuclideanSpace ℝ (Fin m)) :=
  {l | ∀ j : Fin m, 0 ≤ l j}

/-- The positive orthant `ℝ₊₊^m = {x ∈ ℝ^m | 0 < xⱼ for all `j`}`. -/
def EuclideanSpace.positiveOrthant (m : ℕ) : Set (EuclideanSpace ℝ (Fin m)) :=
  {x | ∀ j : Fin m, 0 < x j}

namespace EuclideanOrthant

/- Source-facing Lean notation for the textbook Euclidean orthants `ℝ₊^m` and `ℝ₊₊^m`. -/
scoped notation:max "ℝ₊^" n:arg => EuclideanSpace.nonnegativeOrthant n
scoped notation:max "ℝ₊₊^" n:arg => EuclideanSpace.positiveOrthant n

end EuclideanOrthant

open scoped EuclideanOrthant

namespace EuclideanSpace

variable {m : ℕ} {l : EuclideanSpace ℝ (Fin m)}

/-- Membership in the nonnegative orthant is coordinatewise nonnegativity. -/
@[simp] theorem mem_nonnegativeOrthant_iff :
    l ∈ ℝ₊^m ↔ ∀ j : Fin m, 0 ≤ l j :=
  Iff.rfl

/-- Membership in the positive orthant is coordinatewise strict positivity. -/
@[simp] theorem mem_positiveOrthant_iff {x : EuclideanSpace ℝ (Fin m)} :
    x ∈ ℝ₊₊^m ↔ ∀ j : Fin m, 0 < x j :=
  Iff.rfl

end EuclideanSpace

namespace LagrangianProblem

variable {Q : Type u} {m : ℕ}

local notation "Λ" => EuclideanSpace ℝ (Fin m)

/-- The vector-valued constraint map `x ↦ (f₁(x), ..., fₘ(x))ᵀ`. -/
def constraintVector (problem : LagrangianProblem Q m) : Q → Λ :=
  fun x ↦ problem.toFunctionalConstraintsMinimizationProblem.constraintVector ⟨x, Set.mem_univ x⟩

/-- The coordinates of the constraint vector are the scalar constraint values. -/
@[simp] theorem constraintVector_apply (problem : LagrangianProblem Q m) (x : Q) (j : Fin m) :
    problem.constraintVector x j = problem.constraints j x :=
  rfl

/-- The feasible set cut out by the inequality constraints `fⱼ(x) ≤ 0`. -/
def feasibleSet (problem : LagrangianProblem Q m) : Set Q :=
  problem.toFunctionalConstraintsMinimizationProblem.feasibleSet

/-- Membership in the feasible set is exactly coordinatewise constraint feasibility. -/
@[simp] theorem mem_feasibleSet_iff (problem : LagrangianProblem Q m) {x : Q} :
    x ∈ problem.feasibleSet ↔ ∀ j : Fin m, problem.constraints j x ≤ 0 := by
  let x' : problem.toFunctionalConstraintsMinimizationProblem.basicFeasibleSet :=
    ⟨x, Set.mem_univ x⟩
  have hx' :
      x' ∈ problem.toFunctionalConstraintsMinimizationProblem.feasibleSet ↔
        ∀ j : Fin m,
          problem.toFunctionalConstraintsMinimizationProblem.constraints j x' ≤ 0 :=
    problem.toFunctionalConstraintsMinimizationProblem.mem_feasibleSet_iff (fun _ ↦ rfl)
  simpa [x', feasibleSet, toFunctionalConstraintsMinimizationProblem] using hx'

/-- The ambient constrained minimization problem obtained by minimizing the objective on the
feasible set cut out by the inequality constraints. -/
def toSetConstrainedMinimizationProblem (problem : LagrangianProblem Q m) :
    SetConstrainedMinimizationProblem Q where
  feasibleSet := problem.feasibleSet
  objective := problem

/-- The owner bridge preserves the feasible set. -/
@[simp] theorem toSetConstrainedMinimizationProblem_feasibleSet
    (problem : LagrangianProblem Q m) :
    problem.toSetConstrainedMinimizationProblem.feasibleSet = problem.feasibleSet :=
  rfl

/-- The owner bridge evaluates to the original objective. -/
@[simp] theorem toSetConstrainedMinimizationProblem_apply
    (problem : LagrangianProblem Q m) (x : Q) :
    problem.toSetConstrainedMinimizationProblem x = problem x :=
  rfl

/-- The primal optimal value `f*`, interpreted as the extended-real infimum over the feasible
set. -/
def primalOptimalValue (problem : LagrangianProblem Q m) : EReal :=
  problem.toSetConstrainedMinimizationProblem.optimalValue

/-- Expanding `problem.primalOptimalValue` recovers the infimum of the objective over the feasible
set. -/
theorem primalOptimalValue_eq_sInf_image (problem : LagrangianProblem Q m) :
    problem.primalOptimalValue =
      sInf ((fun x : Q ↦ (problem x : EReal)) '' problem.feasibleSet) := by
  simpa [primalOptimalValue] using
    problem.toSetConstrainedMinimizationProblem.optimalValue_eq_sInf_image

/-- The Lagrangian `𝓛(x, λ) = f₀(x) + ⟨λ, f(x)⟩`. -/
def lagrangian (problem : LagrangianProblem Q m) (x : Q) (l : Λ) : ℝ :=
  problem x + inner ℝ l (problem.constraintVector x)

/-- For a single inequality constraint, the Lagrangian at the scalar multiplier `λ` is
`f₀(x) + λ f₁(x)`. -/
@[simp] theorem lagrangian_single_eq (problem : LagrangianProblem Q 1) (x : Q) (lam : ℝ) :
    problem.lagrangian x (EuclideanSpace.single 0 lam) =
      problem x + lam * problem.constraints 0 x := by
  rw [lagrangian]
  simpa [constraintVector_apply] using
    (EuclideanSpace.inner_single_left (i := 0) (a := lam) (v := problem.constraintVector x))

/-- The dual function `ψ(λ) = inf_{x ∈ Q} 𝓛(x, λ)`, routed through the Chapter 1 owner
`SetConstrainedMinimizationProblem.optimalValue` for the unconstrained Lagrangian subproblem on
`Q`. The codomain is `EReal` so that `-∞` is available. -/
def dualFunction (problem : LagrangianProblem Q m) (l : Λ) : EReal :=
  (SetConstrainedMinimizationProblem.unconstrained fun x ↦ problem.lagrangian x l).optimalValue

/-- The effective domain of the dual function, consisting of multipliers for which `ψ(λ) > -∞`. -/
def dualDomain (problem : LagrangianProblem Q m) : Set Λ :=
  {l | ⊥ < problem.dualFunction l}

/-- Membership in the dual domain means the dual function is finite from below. -/
@[simp] theorem mem_dualDomain_iff (problem : LagrangianProblem Q m) {l : Λ} :
    l ∈ problem.dualDomain ↔ ⊥ < problem.dualFunction l :=
  Iff.rfl

/-- The feasible set of the Lagrange dual problem is `dom ψ ∩ ℝ₊^m`. -/
def dualFeasibleSet (problem : LagrangianProblem Q m) : Set Λ :=
  problem.dualDomain ∩ ℝ₊^m

/-- Dual feasibility means lying in the dual domain and in the nonnegative orthant. -/
@[simp] theorem mem_dualFeasibleSet_iff (problem : LagrangianProblem Q m) {l : Λ} :
    l ∈ problem.dualFeasibleSet ↔ l ∈ problem.dualDomain ∧ ∀ j : Fin m, 0 ≤ l j := by
  simp [dualFeasibleSet]

/-- The set `X*(λ)` of global minimizers of the Lagrangian subproblem at a fixed multiplier
`λ`. -/
def lagrangianMinimizers (problem : LagrangianProblem Q m) (l : Λ) : Set Q :=
  argmin[Set.univ] fun y ↦ problem.lagrangian y l

/-- Membership in `X*(λ)` means being a global minimizer of `x ↦ 𝓛(x, λ)`. -/
@[simp] theorem mem_lagrangianMinimizers_iff (problem : LagrangianProblem Q m) {l : Λ} {x : Q} :
    x ∈ problem.lagrangianMinimizers l ↔
      IsMinOn (fun y ↦ problem.lagrangian y l) Set.univ x := by
  rw [lagrangianMinimizers, mem_constrainedArgmin_iff]
  simp

/-- A point of `X*(λ)` realizes the dual value `ψ(λ)` by evaluating the Lagrangian at that
point. -/
-- Proof sketch: `problem.dualFunction l` is the owner optimal value of the unconstrained
-- Lagrangian subproblem on `Q`, so apply
-- `SetConstrainedMinimizationProblem.optimalValue_eq_of_isMinOn` to the minimizer witness
-- encoded by `x ∈ X*(λ)`.
theorem dualFunction_eq_lagrangian
    (problem : LagrangianProblem Q m) {l : Λ} {x : Q}
    (hx : x ∈ problem.lagrangianMinimizers l) :
    problem.dualFunction l = (problem.lagrangian x l : EReal) := by
  -- Rewrite `x ∈ X*(λ)` into the owner-level global minimizer statement on `Set.univ`.
  rw [mem_lagrangianMinimizers_iff] at hx
  -- Realize `ψ(λ)` as the optimal value of the unconstrained Lagrangian subproblem.
  simpa [dualFunction] using
    (SetConstrainedMinimizationProblem.optimalValue_eq_of_isMinOn
      (problem := SetConstrainedMinimizationProblem.unconstrained
        (fun y ↦ problem.lagrangian y l))
      (x := x)
      (by simp)
      hx)

/-- The Lagrange dual optimal value `f_*`, interpreted as the extended-real supremum of `ψ` over
`dom ψ ∩ ℝ₊ᵐ`. -/
def dualOptimalValue (problem : LagrangianProblem Q m) : EReal :=
  sSup (problem.dualFunction '' problem.dualFeasibleSet)

end LagrangianProblem

/-! ### Definition_1_10_3 (from Chap01) -/
noncomputable section

open EuclideanSpace

local notation "X" => EuclideanSpace ℝ (Fin 2)

/- Primary domain: finite-dimensional Lagrangian duality for a single inequality-constrained
example on `ℝ²`.

Sampled owner declarations before refining this file:
* `LagrangianProblem` together with its primitive fields `objective` and `constraints` in
  `Definition_1_10_2`;
* the derived owner API `LagrangianProblem.constraintVector`, `LagrangianProblem.lagrangian`,
  `LagrangianProblem.lagrangian_single_eq`, and `LagrangianProblem.feasibleSet` in
  `Definition_1_10_2`;
* the direct downstream owner usage in `Proposition_1_10_5`, which treats
  `lagrangianRelaxationExample : LagrangianProblem (EuclideanSpace ℝ (Fin 2)) 1` as the primary
  object.

Best owner abstraction:
`lagrangianRelaxationExample : LagrangianProblem X 1`.

Primitive data in this file:
* the objective function;
* the single scalar constraint.

No additional public bridge/view API is kept here: the textbook scalar-multiplier Lagrangian
formula already follows from the owner theorem `LagrangianProblem.lagrangian_single_eq` by
specializing to `lagrangianRelaxationExample` and unfolding the structure literal. The pointwise
objective and constraint formulas are likewise available directly from the owner declaration. -/

/-- Definition 1.10.3: The example constrained optimization problem on `ℝ²` has objective
`f₀(x) = (1 / 2) ‖x - (1,1)‖²` and the single inequality constraint
`f₁(x) = x₁ - (1 / 2) x₂² ≤ 0`. -/
def lagrangianRelaxationExample : LagrangianProblem X 1 where
  objective x := (1 / 2 : ℝ) * ‖x - WithLp.toLp 2 ![(1 : ℝ), 1]‖ ^ 2
  constraints _ x := x 0 - (1 / 2 : ℝ) * x 1 ^ 2

/-- Evaluating the example problem recovers its quadratic objective formula. -/
@[simp] theorem lagrangianRelaxationExample_apply (x : X) :
    lagrangianRelaxationExample x =
      (1 / 2 : ℝ) * ‖x - WithLp.toLp 2 ![(1 : ℝ), 1]‖ ^ 2 :=
  rfl

/-- The unique scalar constraint of the example is `x₁ - (1 / 2) x₂²`. -/
@[simp] theorem lagrangianRelaxationExample_constraint_apply (x : X) :
    lagrangianRelaxationExample.constraints 0 x =
      x 0 - (1 / 2 : ℝ) * x 1 ^ 2 :=
  rfl

/-! ### Theorem_1_10_4 (from Chap01) -/
noncomputable section

open Filter
open scoped ConstrainedArgmin EuclideanOrthant

universe u

variable {Q : Type u} [TopologicalSpace Q] {m : ℕ}

namespace LagrangianProblem

local notation "Λ" => EuclideanSpace ℝ (Fin m)

section

variable (problem : LagrangianProblem Q m) {lamStar : Λ} {ε : ℝ}

local notation "N" => Metric.closedBall lamStar ε ∩ ℝ₊^m

/- Theorem 1.10.4 lies in topological Lagrangian duality for inequality-constrained problems.

Sampled owner-style declarations:
* `LagrangianProblem.dualDomain`, `dualFeasibleSet`, `constraintVector`, and
  `lagrangianMinimizers` in `Definition_1_10_2`;
* `LagrangianProblem.dualFunction_le_affine_support_of_mem_lagrangianMinimizers` in
  `Proposition_1_10_7`;
* `LagrangianProblem.dualOptimalValue_le_primalOptimalValue` in `Proposition_1_10_8`;
* `objective_gap_ge_weighted_constraint_violation_of_lagrangian_minimizer` in `Chap03/Lemma_3_21`.

Best owner abstraction:
* the existing owner `problem : LagrangianProblem Q m` together with its derived dual-feasibility,
  constraint-vector, and Lagrangian-minimizer API.

Primitive data:
* `problem`
* the dual certificate point `lamStar`
* the radius `ε`
* the punctured orthant-neighborhood minimizer path `xPath`
* the limit point `xStar`

Derived API:
* `problem.dualDomain`
* `problem.dualFeasibleSet`
* `problem.constraintVector`
* `problem.lagrangianMinimizers`
* `problem.feasibleSet`
* `argmin[problem.feasibleSet] problem`

Source/core/bridge triage:
* source-facing: the textbook primal-optimality certificate extracted from nearby dual-feasible
  Lagrangian minimizers
* core/canonical: the owner `LagrangianProblem` and its derived APIs above
* bridge/view: the owner theorem `problem.dualFunction_eq_lagrangian`, used to recover
  neighborhood dual-domain membership from punctured-neighborhood Lagrangian minimizers

The previous statement fixed the primal ambient type to `EuclideanSpace ℝ (Fin n)` and carried
two local neighborhood aliases. The refined statement keeps the same mathematics, lowers the
primal ambient assumptions to the topological structure actually used, and phrases the
certificate directly on the orthant neighborhood because dual-domain membership there is already
derived from `hlamStar` at `lamStar` and from `hxPath` together with
`problem.dualFunction_eq_lagrangian` away from `lamStar`. -/

/-- Helper for Theorem 1.10.4: changing the multiplier changes the Lagrangian by the corresponding
constraint inner product. -/
lemma lagrangian_add_inner_sub_eq
    (x : Q) (lam₁ lam₂ : Λ) :
    problem.lagrangian x lam₁ + inner ℝ (problem.constraintVector x) (lam₂ - lam₁) =
      problem.lagrangian x lam₂ := by
  -- Rewrite the increment term against the second Lagrangian variable and simplify the affine
  -- difference in the multiplier.
  rw [LagrangianProblem.lagrangian, LagrangianProblem.lagrangian]
  have hcomm :
      inner ℝ (problem.constraintVector x) (lam₂ - lam₁) =
        inner ℝ (lam₂ - lam₁) (problem.constraintVector x) := by
    simpa using (real_inner_comm (problem.constraintVector x) (lam₂ - lam₁)).symm
  rw [hcomm, inner_sub_left]
  ring_nf

/-- Helper for Theorem 1.10.4: a forward variation in one multiplier coordinate adds the
corresponding weighted constraint value to the Lagrangian. -/
lemma lagrangian_forward_variation
    (x : Q) (lam : Λ) (j : Fin m) (t : ℝ) :
    problem.lagrangian x (lam + EuclideanSpace.single j t) =
      problem.lagrangian x lam + t * problem.constraints j x := by
  -- Expand the Lagrangian and isolate the contribution of the perturbed coordinate.
  rw [LagrangianProblem.lagrangian, LagrangianProblem.lagrangian, inner_add_left]
  simpa [problem.constraintVector_apply, mul_comm, add_assoc, add_left_comm, add_comm] using
    (congrArg
      (fun r : ℝ ↦ problem x + inner ℝ lam (problem.constraintVector x) + r)
      (EuclideanSpace.inner_single_left
        (i := j) (a := t) (v := problem.constraintVector x)))

/-- Helper for Theorem 1.10.4: a backward variation in one multiplier coordinate subtracts the
corresponding weighted constraint value from the Lagrangian. -/
lemma lagrangian_backward_variation
    (x : Q) (lam : Λ) (j : Fin m) (t : ℝ) :
    problem.lagrangian x (lam - EuclideanSpace.single j t) =
      problem.lagrangian x lam - t * problem.constraints j x := by
  -- Expand the Lagrangian and isolate the contribution of the perturbed coordinate.
  rw [LagrangianProblem.lagrangian, LagrangianProblem.lagrangian, inner_sub_left]
  simpa [problem.constraintVector_apply, mul_comm, add_assoc, add_left_comm, add_comm,
    sub_eq_add_neg] using
    (congrArg
      (fun r : ℝ ↦ problem x + inner ℝ lam (problem.constraintVector x) - r)
      (EuclideanSpace.inner_single_left
        (i := j) (a := t) (v := problem.constraintVector x)))

/-- Helper for Theorem 1.10.4: every punctured point of the orthant neighborhood lies in the dual
feasible set because the path hypothesis supplies a finite Lagrangian minimizer there. -/
lemma punctured_neighborhood_mem_dualFeasibleSet
    {lamStar : Λ} {ε : ℝ}
    (xPath : Λ → Q)
    (hxPath :
      ∀ ⦃lam : Λ⦄,
        lam ∈ Metric.closedBall lamStar ε ∩ ℝ₊^m →
          lam ≠ lamStar →
          xPath lam ∈ problem.lagrangianMinimizers lam)
    {lam : Λ} (hN : lam ∈ Metric.closedBall lamStar ε ∩ ℝ₊^m) (hneq : lam ≠ lamStar) :
    lam ∈ problem.dualFeasibleSet := by
  -- The punctured-path minimizer realizes the dual value as a finite real number.
  have hx : xPath lam ∈ problem.lagrangianMinimizers lam :=
    hxPath hN hneq
  have hdualDomain : lam ∈ problem.dualDomain := by
    rw [problem.mem_dualDomain_iff, bot_lt_iff_ne_bot, problem.dualFunction_eq_lagrangian hx]
    exact EReal.coe_ne_bot _
  -- The orthant membership is already built into the neighborhood definition.
  rw [problem.mem_dualFeasibleSet_iff]
  exact ⟨hdualDomain, by
    simpa [EuclideanSpace.mem_nonnegativeOrthant_iff] using hN.2⟩

/-- Helper for Theorem 1.10.4: forward perturbations of a single multiplier coordinate force the
limiting constraint value at `xStar` to be nonpositive. -/
lemma constraint_nonpos_at_limit_of_forward_variation
    {lamStar : Λ} {ε : ℝ}
    (xPath : Λ → Q) (xStar : Q)
    (hlamStar : lamStar ∈ problem.dualFeasibleSet)
    (hmax : IsMaxOn problem.dualFunction problem.dualFeasibleSet lamStar)
    (hε : 0 < ε)
    (hxPath :
      ∀ ⦃lam : Λ⦄,
        lam ∈ Metric.closedBall lamStar ε ∩ ℝ₊^m →
          lam ≠ lamStar →
          xPath lam ∈ problem.lagrangianMinimizers lam)
    (hlim :
      Tendsto xPath
        (nhdsWithin lamStar ((Metric.closedBall lamStar ε ∩ ℝ₊^m) \ {lamStar}))
        (nhds xStar))
    (hcont : ContinuousAt problem.constraintVector xStar)
    (j : Fin m) :
    problem.constraints j xStar ≤ 0 := by
  let Nset : Set Λ := Metric.closedBall lamStar ε ∩ ℝ₊^m
  let forwardRay : ℝ → Λ := fun t ↦ lamStar + EuclideanSpace.single j t
  have hlamStar_nonneg : ∀ k : Fin m, 0 ≤ lamStar k :=
    (problem.mem_dualFeasibleSet_iff.mp hlamStar).2
  have hforwardMaps :
      ∀ ⦃t : ℝ⦄, t ∈ Set.Ioo 0 ε → forwardRay t ∈ Nset \ {lamStar} := by
    intro t ht
    constructor
    · constructor
      · rw [Metric.mem_closedBall, dist_eq_norm]
        simpa [forwardRay, Real.norm_eq_abs, abs_of_nonneg ht.1.le] using ht.2.le
      · rw [EuclideanSpace.mem_nonnegativeOrthant_iff]
        intro k
        by_cases hk : k = j
        · subst k
          simpa [forwardRay, EuclideanSpace.single] using add_nonneg (hlamStar_nonneg j) ht.1.le
        · simp [forwardRay, EuclideanSpace.single, hk, hlamStar_nonneg k]
    · intro hEq
      have hEq' : forwardRay t = lamStar := by simpa using hEq
      have hCoord := congrArg (fun lam : Λ ↦ lam j) hEq'
      simp [forwardRay, EuclideanSpace.single] at hCoord
      have : (0 : ℝ) < 0 := by simpa [hCoord] using ht.1
      exact this.false
  have hsingleBasis :
      ∀ t : ℝ, (EuclideanSpace.single j t : Λ) = t • (EuclideanSpace.single j (1 : ℝ) : Λ) := by
    intro t
    ext k
    by_cases hk : k = j
    · subst k
      simp [EuclideanSpace.single]
    · simp [EuclideanSpace.single, hk]
  have hforwardEq :
      forwardRay =
        fun t : ℝ ↦ lamStar + (t : ℝ) • (EuclideanSpace.single j (1 : ℝ) : Λ) := by
    funext t
    dsimp [forwardRay]
    rw [hsingleBasis]
  have hforwardContinuous : ContinuousAt forwardRay 0 := by
    rw [hforwardEq]
    have hsingle :
        Continuous fun t : ℝ ↦ (t : ℝ) • (EuclideanSpace.single j (1 : ℝ) : Λ) :=
      continuous_id.smul continuous_const
    exact (continuous_const.add hsingle).continuousAt
  have hforwardToNhds :
      Tendsto forwardRay
        (nhdsWithin (0 : ℝ) (Set.Ioo 0 ε))
        (nhds lamStar) := by
    have hToZero :=
      hforwardContinuous.tendsto.mono_left
        (show nhdsWithin (0 : ℝ) (Set.Ioo 0 ε) ≤ nhds (0 : ℝ) from nhdsWithin_le_nhds)
    have hzero : forwardRay 0 = lamStar := by
      simp [forwardRay, EuclideanSpace.single]
    simpa [hzero] using hToZero
  have hforwardToPrincipal :
      Tendsto forwardRay
        (nhdsWithin (0 : ℝ) (Set.Ioo 0 ε))
        (Filter.principal (Nset \ {lamStar})) := by
    rw [Filter.tendsto_def]
    intro s hs
    rw [Filter.mem_principal] at hs
    exact Filter.mem_of_superset self_mem_nhdsWithin fun t ht ↦ hs (hforwardMaps ht)
  have hforwardToNhdsWithin :
      Tendsto forwardRay
        (nhdsWithin (0 : ℝ) (Set.Ioo 0 ε))
        (nhdsWithin lamStar (Nset \ {lamStar})) := by
    -- Package the ordinary convergence together with eventual membership in the punctured
    -- neighborhood.
    change Tendsto forwardRay
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 ε))
      (nhds lamStar ⊓ Filter.principal (Nset \ {lamStar}))
    simpa using hforwardToNhds.inf hforwardToPrincipal
  have hpathAlongForward :
      Tendsto (fun t : ℝ ↦ xPath (forwardRay t))
        (nhdsWithin (0 : ℝ) (Set.Ioo 0 ε))
        (nhds xStar) :=
    hlim.comp hforwardToNhdsWithin
  have hcoordCont :
      ContinuousAt (fun x : Q ↦ problem.constraintVector x j) xStar := by
    have hofLp :
        ContinuousAt (fun x : Q ↦ WithLp.ofLp (problem.constraintVector x)) xStar := by
      simpa [Function.comp] using
        ((PiLp.continuous_ofLp 2 (fun _ : Fin m ↦ ℝ)).continuousAt.comp hcont)
    simpa [Function.comp] using ((continuous_apply j).continuousAt.comp hofLp)
  have hcoordTendsto :
      Tendsto (fun t : ℝ ↦ problem.constraints j (xPath (forwardRay t)))
        (nhdsWithin (0 : ℝ) (Set.Ioo 0 ε))
        (nhds (problem.constraints j xStar)) := by
    simpa [problem.constraintVector_apply] using hcoordCont.tendsto.comp hpathAlongForward
  have hEventuallyNonpos :
      ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Ioo 0 ε),
        problem.constraints j (xPath (forwardRay t)) ≤ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hmem : forwardRay t ∈ Nset \ {lamStar} := hforwardMaps ht
    have hxray : xPath (forwardRay t) ∈ problem.lagrangianMinimizers (forwardRay t) :=
      hxPath hmem.1 hmem.2
    have hmaxRay :
        problem.dualFunction (forwardRay t) ≤ problem.dualFunction lamStar :=
      (isMaxOn_iff.mp hmax) (forwardRay t)
        (problem.punctured_neighborhood_mem_dualFeasibleSet xPath hxPath hmem.1 hmem.2)
    have hsupport :
        problem.dualFunction lamStar ≤
          problem.dualFunction (forwardRay t) +
            (inner ℝ (problem.constraintVector (xPath (forwardRay t)))
              (lamStar - forwardRay t) : EReal) := by
      simpa [forwardRay] using
        (problem.dualFunction_le_affine_support_of_mem_lagrangianMinimizers
          (lam₁ := forwardRay t) (lam₂ := lamStar) (x₁ := xPath (forwardRay t)) hxray)
    have hsupport' :
        problem.dualFunction lamStar ≤
          ((problem.lagrangian (xPath (forwardRay t)) lamStar : ℝ) : EReal) := by
      calc
        problem.dualFunction lamStar ≤
            problem.dualFunction (forwardRay t) +
              (inner ℝ (problem.constraintVector (xPath (forwardRay t)))
                (lamStar - forwardRay t) : EReal) := hsupport
        _ =
            ((problem.lagrangian (xPath (forwardRay t)) lamStar : ℝ) : EReal) := by
          rw [problem.dualFunction_eq_lagrangian hxray]
          exact_mod_cast
            (problem.lagrangian_add_inner_sub_eq
              (x := xPath (forwardRay t))
              (lam₁ := forwardRay t) (lam₂ := lamStar))
    have hlagLe :
        problem.lagrangian (xPath (forwardRay t)) (forwardRay t) ≤
          problem.lagrangian (xPath (forwardRay t)) lamStar := by
      have hlagLeEReal :
          ((problem.lagrangian (xPath (forwardRay t)) (forwardRay t) : ℝ) : EReal) ≤
            ((problem.lagrangian (xPath (forwardRay t)) lamStar : ℝ) : EReal) := by
        calc
          ((problem.lagrangian (xPath (forwardRay t)) (forwardRay t) : ℝ) : EReal) =
              problem.dualFunction (forwardRay t) := by
            symm
            exact problem.dualFunction_eq_lagrangian hxray
          _ ≤ problem.dualFunction lamStar := hmaxRay
          _ ≤ ((problem.lagrangian (xPath (forwardRay t)) lamStar : ℝ) : EReal) := hsupport'
      exact_mod_cast hlagLeEReal
    have hstep :
        problem.lagrangian (xPath (forwardRay t)) (forwardRay t) =
          problem.lagrangian (xPath (forwardRay t)) lamStar +
            t * problem.constraints j (xPath (forwardRay t)) := by
      simpa [forwardRay] using
        (problem.lagrangian_forward_variation
          (x := xPath (forwardRay t)) (lam := lamStar) (j := j) (t := t))
    rw [hstep] at hlagLe
    have hmul : t * problem.constraints j (xPath (forwardRay t)) ≤ 0 := by
      linarith
    by_contra hpos
    have hpos' : 0 < problem.constraints j (xPath (forwardRay t)) := lt_of_not_ge hpos
    have : 0 < t * problem.constraints j (xPath (forwardRay t)) := mul_pos ht.1 hpos'
    linarith
  have hneBot : (nhdsWithin (0 : ℝ) (Set.Ioo 0 ε)).NeBot := by
    apply (mem_closure_iff_nhdsWithin_neBot).mp
    rw [closure_Ioo (show (0 : ℝ) ≠ ε by linarith)]
    exact ⟨le_rfl, hε.le⟩
  exact le_of_tendsto hcoordTendsto hEventuallyNonpos

/-- Helper for Theorem 1.10.4: if a multiplier coordinate stays strictly positive at `lamStar`,
then the backward coordinate variation forces the limiting constraint value to vanish. -/
lemma constraint_eq_zero_at_limit_of_positive_multiplier
    {lamStar : Λ} {ε : ℝ}
    (xPath : Λ → Q) (xStar : Q)
    (hlamStar : lamStar ∈ problem.dualFeasibleSet)
    (hmax : IsMaxOn problem.dualFunction problem.dualFeasibleSet lamStar)
    (hε : 0 < ε)
    (hxPath :
      ∀ ⦃lam : Λ⦄,
        lam ∈ Metric.closedBall lamStar ε ∩ ℝ₊^m →
          lam ≠ lamStar →
          xPath lam ∈ problem.lagrangianMinimizers lam)
    (hlim :
      Tendsto xPath
        (nhdsWithin lamStar ((Metric.closedBall lamStar ε ∩ ℝ₊^m) \ {lamStar}))
        (nhds xStar))
    (hcont : ContinuousAt problem.constraintVector xStar)
    (j : Fin m) (hj : 0 < lamStar j) :
    problem.constraints j xStar = 0 := by
  let Nset : Set Λ := Metric.closedBall lamStar ε ∩ ℝ₊^m
  let δ : ℝ := min ε (lamStar j)
  let backwardRay : ℝ → Λ := fun t ↦ lamStar - EuclideanSpace.single j t
  have hlamStar_nonneg : ∀ k : Fin m, 0 ≤ lamStar k :=
    (problem.mem_dualFeasibleSet_iff.mp hlamStar).2
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact lt_min hε hj
  have hbackwardMaps :
      ∀ ⦃t : ℝ⦄, t ∈ Set.Ioo 0 δ → backwardRay t ∈ Nset \ {lamStar} := by
    intro t ht
    constructor
    · constructor
      · rw [Metric.mem_closedBall, dist_eq_norm]
        have htε : t ≤ ε := by
          exact le_trans ht.2.le (min_le_left _ _)
        simpa [backwardRay, Real.norm_eq_abs, abs_of_nonneg ht.1.le] using htε
      · rw [EuclideanSpace.mem_nonnegativeOrthant_iff]
        intro k
        by_cases hk : k = j
        · subst k
          have htj : t < lamStar j := lt_of_lt_of_le ht.2 (min_le_right _ _)
          simpa [backwardRay, EuclideanSpace.single] using sub_nonneg.mpr htj.le
        · simp [backwardRay, EuclideanSpace.single, hk, hlamStar_nonneg k]
    · intro hEq
      have hEq' : backwardRay t = lamStar := by simpa using hEq
      have hCoord := congrArg (fun lam : Λ ↦ lam j) hEq'
      simp [backwardRay, EuclideanSpace.single] at hCoord
      have : (0 : ℝ) < 0 := by simpa [hCoord] using ht.1
      exact this.false
  have hsingleBasis :
      ∀ t : ℝ, (EuclideanSpace.single j t : Λ) = t • (EuclideanSpace.single j (1 : ℝ) : Λ) := by
    intro t
    ext k
    by_cases hk : k = j
    · subst k
      simp [EuclideanSpace.single]
    · simp [EuclideanSpace.single, hk]
  have hbackwardEq :
      backwardRay =
        fun t : ℝ ↦ lamStar - (t : ℝ) • (EuclideanSpace.single j (1 : ℝ) : Λ) := by
    funext t
    dsimp [backwardRay]
    rw [hsingleBasis]
  have hbackwardContinuous : ContinuousAt backwardRay 0 := by
    rw [hbackwardEq]
    have hsingle :
        Continuous fun t : ℝ ↦ (t : ℝ) • (EuclideanSpace.single j (1 : ℝ) : Λ) :=
      continuous_id.smul continuous_const
    exact (continuous_const.sub hsingle).continuousAt
  have hbackwardToNhds :
      Tendsto backwardRay
        (nhdsWithin (0 : ℝ) (Set.Ioo 0 δ))
        (nhds lamStar) := by
    have hToZero :=
      hbackwardContinuous.tendsto.mono_left
        (show nhdsWithin (0 : ℝ) (Set.Ioo 0 δ) ≤ nhds (0 : ℝ) from nhdsWithin_le_nhds)
    have hzero : backwardRay 0 = lamStar := by
      simp [backwardRay, EuclideanSpace.single]
    simpa [hzero] using hToZero
  have hbackwardToPrincipal :
      Tendsto backwardRay
        (nhdsWithin (0 : ℝ) (Set.Ioo 0 δ))
        (Filter.principal (Nset \ {lamStar})) := by
    rw [Filter.tendsto_def]
    intro s hs
    rw [Filter.mem_principal] at hs
    exact Filter.mem_of_superset self_mem_nhdsWithin fun t ht ↦ hs (hbackwardMaps ht)
  have hbackwardToNhdsWithin :
      Tendsto backwardRay
        (nhdsWithin (0 : ℝ) (Set.Ioo 0 δ))
        (nhdsWithin lamStar (Nset \ {lamStar})) := by
    -- Package the ordinary convergence together with eventual membership in the punctured
    -- neighborhood.
    change Tendsto backwardRay
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 δ))
      (nhds lamStar ⊓ Filter.principal (Nset \ {lamStar}))
    simpa using hbackwardToNhds.inf hbackwardToPrincipal
  have hpathAlongBackward :
      Tendsto (fun t : ℝ ↦ xPath (backwardRay t))
        (nhdsWithin (0 : ℝ) (Set.Ioo 0 δ))
        (nhds xStar) :=
    hlim.comp hbackwardToNhdsWithin
  have hcoordCont :
      ContinuousAt (fun x : Q ↦ problem.constraintVector x j) xStar := by
    have hofLp :
        ContinuousAt (fun x : Q ↦ WithLp.ofLp (problem.constraintVector x)) xStar := by
      simpa [Function.comp] using
        ((PiLp.continuous_ofLp 2 (fun _ : Fin m ↦ ℝ)).continuousAt.comp hcont)
    simpa [Function.comp] using ((continuous_apply j).continuousAt.comp hofLp)
  have hcoordTendsto :
      Tendsto (fun t : ℝ ↦ problem.constraints j (xPath (backwardRay t)))
        (nhdsWithin (0 : ℝ) (Set.Ioo 0 δ))
        (nhds (problem.constraints j xStar)) := by
    simpa [problem.constraintVector_apply] using hcoordCont.tendsto.comp hpathAlongBackward
  have hEventuallyNonneg :
      ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Ioo 0 δ),
        0 ≤ problem.constraints j (xPath (backwardRay t)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hmem : backwardRay t ∈ Nset \ {lamStar} := hbackwardMaps ht
    have hxray : xPath (backwardRay t) ∈ problem.lagrangianMinimizers (backwardRay t) :=
      hxPath hmem.1 hmem.2
    have hmaxRay :
        problem.dualFunction (backwardRay t) ≤ problem.dualFunction lamStar :=
      (isMaxOn_iff.mp hmax) (backwardRay t)
        (problem.punctured_neighborhood_mem_dualFeasibleSet xPath hxPath hmem.1 hmem.2)
    have hsupport :
        problem.dualFunction lamStar ≤
          problem.dualFunction (backwardRay t) +
            (inner ℝ (problem.constraintVector (xPath (backwardRay t)))
              (lamStar - backwardRay t) : EReal) := by
      simpa [backwardRay] using
        (problem.dualFunction_le_affine_support_of_mem_lagrangianMinimizers
          (lam₁ := backwardRay t) (lam₂ := lamStar) (x₁ := xPath (backwardRay t)) hxray)
    have hsupport' :
        problem.dualFunction lamStar ≤
          ((problem.lagrangian (xPath (backwardRay t)) lamStar : ℝ) : EReal) := by
      calc
        problem.dualFunction lamStar ≤
            problem.dualFunction (backwardRay t) +
              (inner ℝ (problem.constraintVector (xPath (backwardRay t)))
                (lamStar - backwardRay t) : EReal) := hsupport
        _ =
            ((problem.lagrangian (xPath (backwardRay t)) lamStar : ℝ) : EReal) := by
          rw [problem.dualFunction_eq_lagrangian hxray]
          exact_mod_cast
            (problem.lagrangian_add_inner_sub_eq
              (x := xPath (backwardRay t))
              (lam₁ := backwardRay t) (lam₂ := lamStar))
    have hlagLe :
        problem.lagrangian (xPath (backwardRay t)) (backwardRay t) ≤
          problem.lagrangian (xPath (backwardRay t)) lamStar := by
      have hlagLeEReal :
          ((problem.lagrangian (xPath (backwardRay t)) (backwardRay t) : ℝ) : EReal) ≤
            ((problem.lagrangian (xPath (backwardRay t)) lamStar : ℝ) : EReal) := by
        calc
          ((problem.lagrangian (xPath (backwardRay t)) (backwardRay t) : ℝ) : EReal) =
              problem.dualFunction (backwardRay t) := by
            symm
            exact problem.dualFunction_eq_lagrangian hxray
          _ ≤ problem.dualFunction lamStar := hmaxRay
          _ ≤ ((problem.lagrangian (xPath (backwardRay t)) lamStar : ℝ) : EReal) := hsupport'
      exact_mod_cast hlagLeEReal
    have hstep :
        problem.lagrangian (xPath (backwardRay t)) (backwardRay t) =
          problem.lagrangian (xPath (backwardRay t)) lamStar -
            t * problem.constraints j (xPath (backwardRay t)) := by
      simpa [backwardRay] using
        (problem.lagrangian_backward_variation
          (x := xPath (backwardRay t)) (lam := lamStar) (j := j) (t := t))
    rw [hstep] at hlagLe
    have hmul : (-t) * problem.constraints j (xPath (backwardRay t)) ≤ 0 := by
      linarith
    by_contra hneg
    have hneg' : problem.constraints j (xPath (backwardRay t)) < 0 := lt_of_not_ge hneg
    have htneg : -t < 0 := by
      nlinarith [ht.1]
    have : 0 < (-t) * problem.constraints j (xPath (backwardRay t)) :=
      mul_pos_of_neg_of_neg htneg hneg'
    linarith
  have hneBot : (nhdsWithin (0 : ℝ) (Set.Ioo 0 δ)).NeBot := by
    apply (mem_closure_iff_nhdsWithin_neBot).mp
    rw [closure_Ioo (show (0 : ℝ) ≠ δ by linarith [hδpos])]
    exact ⟨le_rfl, hδpos.le⟩
  have hnonneg : 0 ≤ problem.constraints j xStar :=
    ge_of_tendsto hcoordTendsto hEventuallyNonneg
  have hnonpos :
      problem.constraints j xStar ≤ 0 :=
    problem.constraint_nonpos_at_limit_of_forward_variation
      xPath xStar hlamStar hmax hε hxPath hlim hcont j
  exact le_antisymm hnonpos hnonneg

/-- Helper for Theorem 1.10.4: the coordinatewise limiting equalities and inequalities combine
into the complementary-slackness identity at `xStar`. -/
lemma complementary_slackness_at_limit
    {lamStar : Λ} {ε : ℝ}
    (xPath : Λ → Q) (xStar : Q)
    (hlamStar : lamStar ∈ problem.dualFeasibleSet)
    (hmax : IsMaxOn problem.dualFunction problem.dualFeasibleSet lamStar)
    (hε : 0 < ε)
    (hxPath :
      ∀ ⦃lam : Λ⦄,
        lam ∈ Metric.closedBall lamStar ε ∩ ℝ₊^m →
          lam ≠ lamStar →
          xPath lam ∈ problem.lagrangianMinimizers lam)
    (hlim :
      Tendsto xPath
        (nhdsWithin lamStar ((Metric.closedBall lamStar ε ∩ ℝ₊^m) \ {lamStar}))
        (nhds xStar))
    (hcont : ContinuousAt problem.constraintVector xStar)
    (j : Fin m) :
    lamStar j * problem.constraints j xStar = 0 := by
  -- Split by whether the multiplier coordinate is strictly positive or already zero.
  by_cases hj : 0 < lamStar j
  · have hzero :
        problem.constraints j xStar = 0 :=
      problem.constraint_eq_zero_at_limit_of_positive_multiplier
        xPath xStar hlamStar hmax hε hxPath hlim hcont j hj
    rw [hzero, mul_zero]
  · have hjZero : lamStar j = 0 := by
      have hjNonneg : 0 ≤ lamStar j :=
        (problem.mem_dualFeasibleSet_iff.mp hlamStar).2 j
      linarith
    rw [hjZero, zero_mul]

/-- Theorem 1.10.4: a dual-feasible maximizer of the dual function together with a convergent
family of Lagrangian minimizers on a punctured `ℝ₊^m`-neighborhood certifies that the limit
point is a globally optimal primal solution. -/
-- Proof sketch: use the affine upper-support inequality for the dual function at nearby
-- dual-feasible multipliers, vary one coordinate at a time around `λStar`, and pass to the limit
-- using continuity of the constraint map at `xStar` to deduce feasibility and complementary
-- slackness for `xStar`; the needed dual-domain membership comes from `hlamStar` at `λStar` and
-- from `problem.dualFunction_eq_lagrangian` along the punctured neighborhood. Then combine
-- `xStar ∈ X*(λStar)` with weak duality to conclude that `xStar` belongs to the canonical
-- constrained argmin set of the primal problem.
theorem globalOptimality_of_dualCertificate
    {lamStar : Λ} {ε : ℝ}
    (xPath : Λ → Q) (xStar : Q)
    (hlamStar : lamStar ∈ problem.dualFeasibleSet)
    (hmax : IsMaxOn problem.dualFunction problem.dualFeasibleSet lamStar)
    (hε : 0 < ε)
    (hxPath :
      ∀ ⦃lam : Λ⦄,
        lam ∈ Metric.closedBall lamStar ε ∩ ℝ₊^m →
          lam ≠ lamStar →
          xPath lam ∈ problem.lagrangianMinimizers lam)
    (hlim :
      Tendsto xPath
        (nhdsWithin lamStar ((Metric.closedBall lamStar ε ∩ ℝ₊^m) \ {lamStar}))
        (nhds xStar))
    (hcont : ContinuousAt problem.constraintVector xStar)
    (hxStar : xStar ∈ problem.lagrangianMinimizers lamStar) :
    xStar ∈ argmin[problem.feasibleSet] problem := by
  -- First extract feasibility and complementary slackness by the coordinate-variation argument.
  have hfeasible : xStar ∈ problem.feasibleSet := by
    rw [problem.mem_feasibleSet_iff]
    intro j
    exact problem.constraint_nonpos_at_limit_of_forward_variation
      xPath xStar hlamStar hmax hε hxPath hlim hcont j
  have hcomp :
      ∀ j : Fin m, lamStar j * problem.constraints j xStar = 0 := by
    intro j
    exact problem.complementary_slackness_at_limit
      xPath xStar hlamStar hmax hε hxPath hlim hcont j
  -- Next collapse the Lagrangian at `(xStar, lamStar)` to the primal objective value.
  have hinnerZero : inner ℝ lamStar (problem.constraintVector xStar) = 0 := by
    rw [PiLp.inner_apply]
    refine Finset.sum_eq_zero ?_
    intro j _
    have hscalar :
        inner ℝ (lamStar j) (problem.constraintVector xStar j) =
          lamStar j * problem.constraintVector xStar j := by
      have hinner :
          inner ℝ (lamStar j) (problem.constraintVector xStar j) =
            problem.constraintVector xStar j * (starRingEnd ℝ) (lamStar j) :=
        RCLike.inner_apply (lamStar j) (problem.constraintVector xStar j)
      simpa [mul_comm] using hinner
    rw [hscalar, problem.constraintVector_apply, hcomp j]
  have hlagrangianEq :
      problem.lagrangian xStar lamStar = problem xStar := by
    -- Complementary slackness kills the inner-product term in the Lagrangian.
    rw [LagrangianProblem.lagrangian, hinnerZero, add_zero]
  have hdualEq :
      problem.dualFunction lamStar = (problem xStar : EReal) := by
    calc
      problem.dualFunction lamStar = (problem.lagrangian xStar lamStar : EReal) :=
        problem.dualFunction_eq_lagrangian hxStar
      _ = (problem xStar : EReal) := by
        exact_mod_cast hlagrangianEq
  -- Finally combine the dual-value identity with pointwise weak duality and the primal owner API.
  rw [mem_constrainedArgmin_iff]
  refine ⟨hfeasible, ?_⟩
  rw [isMinOn_iff]
  intro y hy
  have hlamStar_nonneg : lamStar ∈ ℝ₊^m := by
    simpa [EuclideanSpace.mem_nonnegativeOrthant_iff] using
      (problem.mem_dualFeasibleSet_iff.mp hlamStar).2
  have hdualLe :
      problem.dualFunction lamStar ≤ problem.primalOptimalValue :=
    problem.dualFunction_le_primalOptimalValue lamStar hlamStar_nonneg
  have hprimalLe :
      problem.primalOptimalValue ≤ (problem y : EReal) := by
    simpa [LagrangianProblem.primalOptimalValue] using
      problem.toSetConstrainedMinimizationProblem.optimalValue_le_of_mem_feasibleSet hy
  have hoptimalEReal : (problem xStar : EReal) ≤ (problem y : EReal) := by
    calc
      (problem xStar : EReal) = problem.dualFunction lamStar := by
        simpa using hdualEq.symm
      _ ≤ problem.primalOptimalValue := hdualLe
      _ ≤ (problem y : EReal) := hprimalLe
  exact_mod_cast hoptimalEReal

end

end LagrangianProblem

/-! ### Proposition_1_10_5 (from Chap01) -/
noncomputable section

open EuclideanSpace

local notation "X" => EuclideanSpace ℝ (Fin 2)
local notation "ψ" => lagrangianRelaxationExample.dualFunction ∘ single 0
local notation "X⋆" => lagrangianRelaxationExample.lagrangianMinimizers ∘ single 0

/- Primary domain: explicit Lagrangian-duality computations for the single-constraint example from
Definition 1.10.3.

Owner declarations sampled before refining this file:
* `LagrangianProblem.dualDomain`, `LagrangianProblem.lagrangianMinimizers`, and
  `LagrangianProblem.dualFunction` in `Definition_1_10_2`;
* `lagrangianRelaxationExample` in `Definition_1_10_3`, together with the owner theorem
  `LagrangianProblem.lagrangian_single_eq` specialized to that example by unfolding the structure
  literal;
* `LagrangianProblem.dualFunction_le_affine_support_of_mem_lagrangianMinimizers` in
  `Proposition_1_10_7`;
* `PrimalEqualityConstrainedProblem.LagrangianMinimizerSelection` and
  `LagrangianMinimizerSelection.dualFunction_eq_lagrangian` in `Definition_2_31`.

Best owner abstraction: the primitive owner is `lagrangianRelaxationExample : LagrangianProblem X
1`.

Layering in this file:
* source-facing primitive data: the explicit minimizer path `λ ↦ x(λ)`;
* bridge/view API: its coordinate formulas and the scalar specializations of the owner dual-domain,
  minimizer-set, and dual-function declarations.

No extra public wrapper is introduced here: Proposition 1.10.5 is an explicit example
computation attached to the owner `LagrangianProblem`, not a second owner abstraction. -/

/-- The explicit minimizer trajectory for the Lagrangian relaxation example. -/
def lagrangianRelaxationExampleMinimizerTrajectory (lam : ℝ) : X :=
  WithLp.toLp 2 ![(1 : ℝ) - lam, 1 / (1 - lam)]

/- Proposition 1.10.5 splits naturally into the effective-domain statement, the explicit
singleton description of the minimizer set, and the closed formula for the dual function. -/

/-- Helper for Proposition 1.10.5: the example Lagrangian matches the scalar quadratic formula
from the source proof. -/
lemma lagrangianRelaxationExample_lagrangian_eq_explicit (x : X) (lam : ℝ) :
    lagrangianRelaxationExample.lagrangian x (single 0 lam) =
      (1 / 2 : ℝ) * ((x 0 - 1) ^ (2 : ℕ) + (x 1 - 1) ^ (2 : ℕ)) +
        lam * (x 0 - (1 / 2 : ℝ) * x 1 ^ (2 : ℕ)) := by
  -- Rewrite the owner Lagrangian into the textbook objective-plus-constraint form.
  rw [LagrangianProblem.lagrangian_single_eq]
  rw [lagrangianRelaxationExample_apply, lagrangianRelaxationExample_constraint_apply]
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp

/-- Helper for Proposition 1.10.5: completing the squares isolates the unique minimizer when
`λ < 1`. -/
lemma lagrangianRelaxationExample_lagrangian_eq_completed_square
    (x : X) (lam : ℝ) (h_lam : lam ≠ 1) :
    lagrangianRelaxationExample.lagrangian x (single 0 lam) =
      (1 / 2 : ℝ) * (x 0 - (1 - lam)) ^ (2 : ℕ) +
        ((1 - lam) / 2 : ℝ) * (x 1 - 1 / (1 - lam)) ^ (2 : ℕ) +
          (lam - (1 / 2 : ℝ) * lam ^ (2 : ℕ) - 1 / (2 * (1 - lam)) + (1 / 2 : ℝ)) := by
  -- Complete the square in each coordinate and keep the constant term separate.
  rw [lagrangianRelaxationExample_lagrangian_eq_explicit]
  have hdenom : 1 - lam ≠ 0 := sub_ne_zero.mpr h_lam.symm
  field_simp [hdenom]
  ring_nf

/-- Helper for Proposition 1.10.5: the vertical ray `(0,t)` exposes the unbounded-below regime
when `λ ≥ 1`. -/
lemma lagrangianRelaxationExample_lagrangian_on_vertical_ray (lam t : ℝ) :
    lagrangianRelaxationExample.lagrangian (WithLp.toLp 2 ![(0 : ℝ), t]) (single 0 lam) =
      1 - t + ((1 - lam) / 2 : ℝ) * t ^ (2 : ℕ) := by
  -- Evaluate the scalar formula on the ray `x¹ = 0`.
  rw [lagrangianRelaxationExample_lagrangian_eq_explicit]
  simp
  ring

/-- Helper for Proposition 1.10.5: for `λ < 1`, the textbook trajectory realizes the Lagrangian
minimum. -/
lemma lagrangianRelaxationExampleMinimizerTrajectory_mem_lagrangianMinimizers
    (lam : ℝ) (h_lam : lam < 1) :
    lagrangianRelaxationExampleMinimizerTrajectory lam ∈ X⋆ lam := by
  -- Use the completed-square decomposition to compare the trajectory against any point.
  simp only [Function.comp_apply]
  rw [LagrangianProblem.mem_lagrangianMinimizers_iff, isMinOn_iff]
  intro y hy
  have hne : lam ≠ 1 := ne_of_lt h_lam
  rw [lagrangianRelaxationExample_lagrangian_eq_completed_square
      (lagrangianRelaxationExampleMinimizerTrajectory lam) lam hne]
  rw [lagrangianRelaxationExample_lagrangian_eq_completed_square y lam hne]
  have hcoef : 0 ≤ ((1 - lam) / 2 : ℝ) := by
    nlinarith
  have hsquare0 : 0 ≤ (1 / 2 : ℝ) * (y 0 - (1 - lam)) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (y 0 - (1 - lam))]
  have hsquare1 :
      0 ≤ ((1 - lam) / 2 : ℝ) * (y 1 - 1 / (1 - lam)) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (y 1 - 1 / (1 - lam)), hcoef]
  simp [lagrangianRelaxationExampleMinimizerTrajectory]
  nlinarith

/-- Helper for Proposition 1.10.5: every minimizer at `λ < 1` must coincide with the explicit
trajectory point. -/
lemma eq_lagrangianRelaxationExampleMinimizerTrajectory_of_mem_lagrangianMinimizers
    (lam : ℝ) (h_lam : lam < 1) {x : X} (hx : x ∈ X⋆ lam) :
    x = lagrangianRelaxationExampleMinimizerTrajectory lam := by
  have hne : lam ≠ 1 := ne_of_lt h_lam
  have hx' : x ∈ lagrangianRelaxationExample.lagrangianMinimizers (single 0 lam) := by
    simpa only [Function.comp_apply] using hx
  have hxMin :
      IsMinOn (fun y ↦ lagrangianRelaxationExample.lagrangian y (single 0 lam)) Set.univ x := by
    rw [← LagrangianProblem.mem_lagrangianMinimizers_iff]
    exact hx'
  have htraj :
      lagrangianRelaxationExampleMinimizerTrajectory lam ∈ X⋆ lam :=
    lagrangianRelaxationExampleMinimizerTrajectory_mem_lagrangianMinimizers lam h_lam
  have htraj' :
      lagrangianRelaxationExampleMinimizerTrajectory lam ∈
        lagrangianRelaxationExample.lagrangianMinimizers (single 0 lam) := by
    simpa only [Function.comp_apply] using htraj
  have htrajMin :
      IsMinOn
        (fun y ↦ lagrangianRelaxationExample.lagrangian y (single 0 lam))
        Set.univ
        (lagrangianRelaxationExampleMinimizerTrajectory lam) := by
    rw [← LagrangianProblem.mem_lagrangianMinimizers_iff]
    exact htraj'
  -- Compare the unknown minimizer with the explicit trajectory to force equality in the squares.
  have hle_left :=
    (isMinOn_iff.mp hxMin)
      (lagrangianRelaxationExampleMinimizerTrajectory lam) (by simp)
  have hle_right := (isMinOn_iff.mp htrajMin) x (by simp)
  have heq :
      lagrangianRelaxationExample.lagrangian x (single 0 lam) =
        lagrangianRelaxationExample.lagrangian
          (lagrangianRelaxationExampleMinimizerTrajectory lam) (single 0 lam) :=
    le_antisymm hle_left hle_right
  rw [lagrangianRelaxationExample_lagrangian_eq_completed_square x lam hne] at heq
  rw [lagrangianRelaxationExample_lagrangian_eq_completed_square
      (lagrangianRelaxationExampleMinimizerTrajectory lam) lam hne] at heq
  have hsquare0 : 0 ≤ (1 / 2 : ℝ) * (x 0 - (1 - lam)) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (x 0 - (1 - lam))]
  have hcoef : 0 < ((1 - lam) / 2 : ℝ) := by
    nlinarith
  have hsquare1 :
      0 ≤ ((1 - lam) / 2 : ℝ) * (x 1 - 1 / (1 - lam)) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (x 1 - 1 / (1 - lam)), le_of_lt hcoef]
  have hsum :
      (1 / 2 : ℝ) * (x 0 - (1 - lam)) ^ (2 : ℕ) +
        ((1 - lam) / 2 : ℝ) * (x 1 - 1 / (1 - lam)) ^ (2 : ℕ) = 0 := by
    simpa [lagrangianRelaxationExampleMinimizerTrajectory] using heq
  have hsquare0_eq :
      (1 / 2 : ℝ) * (x 0 - (1 - lam)) ^ (2 : ℕ) = 0 := by
    nlinarith [hsquare0, hsquare1, hsum]
  have hsquare1_eq :
      ((1 - lam) / 2 : ℝ) * (x 1 - 1 / (1 - lam)) ^ (2 : ℕ) = 0 := by
    nlinarith [hsquare0, hsquare1, hsum]
  -- Each nonnegative square term must vanish, so both coordinates are forced.
  have hx0 : x 0 = 1 - lam := by
    have hsq : (x 0 - (1 - lam)) ^ (2 : ℕ) = 0 := by
      exact (mul_eq_zero.mp hsquare0_eq).resolve_left (show (1 / 2 : ℝ) ≠ 0 by norm_num)
    have hzero : x 0 - (1 - lam) = 0 := sq_eq_zero_iff.mp hsq
    linarith
  have hx1 : x 1 = 1 / (1 - lam) := by
    have hsq : (x 1 - 1 / (1 - lam)) ^ (2 : ℕ) = 0 := by
      exact (mul_eq_zero.mp hsquare1_eq).resolve_left (ne_of_gt hcoef)
    have hzero : x 1 - 1 / (1 - lam) = 0 := sq_eq_zero_iff.mp hsq
    linarith
  ext i
  fin_cases i
  · simpa [lagrangianRelaxationExampleMinimizerTrajectory] using hx0
  · simpa [lagrangianRelaxationExampleMinimizerTrajectory] using hx1

/-- Helper for Proposition 1.10.5: once `λ ≥ 1`, the example dual function is `-∞`. -/
lemma lagrangianRelaxationExample_dualFunction_eq_bot_of_one_le
    (lam : ℝ) (h_lam : 1 ≤ lam) :
    ψ lam = (⊥ : EReal) := by
  -- Push the vertical ray far enough so that the Lagrangian value falls below any prescribed
  -- real threshold.
  refine (EReal.eq_bot_iff_forall_lt _).2 ?_
  intro c
  let t : ℝ := max 0 (2 - c)
  have ht_gt : 1 - t < c := by
    dsimp [t]
    by_cases hcase : 2 - c ≤ 0
    · rw [max_eq_left hcase]
      linarith
    · have hcase' : 0 < 2 - c := lt_of_not_ge hcase
      rw [max_eq_right hcase'.le]
      linarith
  have hcoef_nonpos : ((1 - lam) / 2 : ℝ) ≤ 0 := by
    nlinarith
  have hray_lt :
      lagrangianRelaxationExample.lagrangian (WithLp.toLp 2 ![(0 : ℝ), t]) (single 0 lam) < c := by
    rw [lagrangianRelaxationExample_lagrangian_on_vertical_ray]
    have hquad_nonpos : ((1 - lam) / 2 : ℝ) * t ^ (2 : ℕ) ≤ 0 := by
      nlinarith [sq_nonneg t, hcoef_nonpos]
    linarith
  -- The dual value is bounded above by every feasible point of the unconstrained subproblem.
  have hdual_le :
      lagrangianRelaxationExample.dualFunction (single 0 lam) ≤
        (lagrangianRelaxationExample.lagrangian (WithLp.toLp 2 ![(0 : ℝ), t]) (single 0 lam) :
          EReal) := by
    simpa [LagrangianProblem.dualFunction] using
      (SetConstrainedMinimizationProblem.optimalValue_le_of_mem_feasibleSet
        (problem := SetConstrainedMinimizationProblem.unconstrained
          (fun x : X ↦ lagrangianRelaxationExample.lagrangian x (single 0 lam)))
        (x := WithLp.toLp 2 ![(0 : ℝ), t])
        (by simp))
  exact lt_of_le_of_lt hdual_le (by exact_mod_cast hray_lt)

/-- Proposition 1.10.5 (1): along the scalar multiplier parametrization, the effective domain of
the example dual function is `(-∞, 1)`. -/
-- Proof sketch: rewrite membership in `lagrangianRelaxationExample.dualDomain` along the scalar
-- multiplier path as boundedness below of the example Lagrangian, then analyze the coefficient of
-- `(x 1)^2` to show boundedness occurs exactly when `λ < 1`.
theorem lagrangianRelaxationExampleMultiplier_mem_dualDomain_iff (lam : ℝ) :
    single 0 lam ∈ lagrangianRelaxationExample.dualDomain ↔ lam < 1 := by
  constructor
  · intro hdom
    -- Outside `(-∞, 1)`, the vertical-ray argument forces the dual value to be `-∞`.
    by_contra hnot
    have hge : 1 ≤ lam := not_lt.mp hnot
    have hbot : lagrangianRelaxationExample.dualFunction (single 0 lam) = (⊥ : EReal) := by
      simpa only [Function.comp_apply] using
        lagrangianRelaxationExample_dualFunction_eq_bot_of_one_le lam hge
    rw [LagrangianProblem.mem_dualDomain_iff, bot_lt_iff_ne_bot, hbot] at hdom
    exact hdom rfl
  · intro h_lam
    -- Inside `(-∞, 1)`, the explicit trajectory attains the dual value as a finite real number.
    have htraj :
        lagrangianRelaxationExampleMinimizerTrajectory lam ∈ X⋆ lam :=
      lagrangianRelaxationExampleMinimizerTrajectory_mem_lagrangianMinimizers lam h_lam
    have htraj' :
        lagrangianRelaxationExampleMinimizerTrajectory lam ∈
          lagrangianRelaxationExample.lagrangianMinimizers (single 0 lam) := by
      simpa only [Function.comp_apply] using htraj
    rw [LagrangianProblem.mem_dualDomain_iff, bot_lt_iff_ne_bot]
    rw [LagrangianProblem.dualFunction_eq_lagrangian
      (problem := lagrangianRelaxationExample) htraj']
    exact EReal.coe_ne_bot _

/-- Proposition 1.10.5 (2): for every `λ < 1`, the Lagrangian subproblem has the unique minimizer
with coordinates `x¹(λ) = 1 - λ` and `x²(λ) = 1 / (1 - λ)`. -/
-- Proof sketch: solve the first-order optimality equations for the example Lagrangian and use
-- strict convexity for `λ < 1` to identify the unique minimizer.
theorem lagrangianRelaxationExample_lagrangianMinimizers_eq_singleton
    (lam : ℝ) (h_lam : lam < 1) :
    X⋆ lam =
      ({lagrangianRelaxationExampleMinimizerTrajectory lam} : Set X) :=
  by
  ext x
  constructor
  · intro hx
    -- Any minimizer must make both completed-square terms vanish.
    have hxeq :
        x = lagrangianRelaxationExampleMinimizerTrajectory lam :=
      eq_lagrangianRelaxationExampleMinimizerTrajectory_of_mem_lagrangianMinimizers lam h_lam hx
    simp [hxeq]
  · intro hx
    -- The explicit trajectory is already known to be a minimizer.
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact lagrangianRelaxationExampleMinimizerTrajectory_mem_lagrangianMinimizers lam h_lam

/-- Proposition 1.10.5 (3): for every `λ < 1`, the dual function of the example is
`λ - (1 / 2) λ² - 1 / (2 (1 - λ)) + 1 / 2`. -/
-- Proof sketch: evaluate the Lagrangian at the explicit minimizer trajectory and simplify the
-- resulting expression using the coordinate formulas for the minimizer.
theorem lagrangianRelaxationExample_dualFunction_eq_closedForm
    (lam : ℝ) (h_lam : lam < 1) :
    ψ lam =
      ((lam - (1 / 2 : ℝ) * lam ^ (2 : ℕ) - 1 / (2 * (1 - lam)) + (1 / 2 : ℝ)) : EReal) :=
  by
  have htraj :
      lagrangianRelaxationExampleMinimizerTrajectory lam ∈ X⋆ lam :=
    lagrangianRelaxationExampleMinimizerTrajectory_mem_lagrangianMinimizers lam h_lam
  have htraj' :
      lagrangianRelaxationExampleMinimizerTrajectory lam ∈
        lagrangianRelaxationExample.lagrangianMinimizers (single 0 lam) := by
    simpa only [Function.comp_apply] using htraj
  have hne : lam ≠ 1 := ne_of_lt h_lam
  -- Evaluate the dual function at the unique minimizer and simplify the completed-square form.
  simp only [Function.comp_apply]
  rw [LagrangianProblem.dualFunction_eq_lagrangian
    (problem := lagrangianRelaxationExample) htraj']
  rw [lagrangianRelaxationExample_lagrangian_eq_completed_square
    (lagrangianRelaxationExampleMinimizerTrajectory lam) lam hne]
  simp [lagrangianRelaxationExampleMinimizerTrajectory]
  have hdenom : 1 - lam ≠ 0 := by
    linarith
  have hvalue :
      (lam - (2⁻¹ : ℝ) * lam ^ (2 : ℕ) - (1 - lam)⁻¹ * (2⁻¹ : ℝ) + (2⁻¹ : ℝ)) =
        (lam - (2⁻¹ : ℝ) * lam ^ (2 : ℕ) - (2 * (1 - lam))⁻¹ + (2⁻¹ : ℝ)) := by
    field_simp [hdenom]
  have hvalueE :
      (↑lam : EReal) - ↑(2⁻¹ : ℝ) * ↑lam ^ (2 : ℕ) - ↑((1 - lam)⁻¹ : ℝ) * ↑(2⁻¹ : ℝ) +
          ↑(2⁻¹ : ℝ) =
        (↑lam : EReal) - ↑(2⁻¹ : ℝ) * ↑lam ^ (2 : ℕ) - ↑((2 * (1 - lam))⁻¹ : ℝ) +
          ↑(2⁻¹ : ℝ) := by
    exact_mod_cast hvalue
  rw [show (2 * (1 - (lam : EReal)))⁻¹ = (((2 * (1 - lam))⁻¹ : ℝ) : EReal) by rfl]
  exact hvalueE

/-! ### Example_1_10_6 (from Chap01) -/
noncomputable section

open EuclideanSpace Filter
open scoped ConstrainedArgmin EuclideanOrthant

local notation "Λ" => EuclideanSpace ℝ (Fin 1)
local notation "λ⋆" => lagrangianRelaxationExampleLambdaStar
local notation "Λ⋆" => single 0 λ⋆

/-
Primary domain: primal optimality certificates in Lagrangian duality.

Relevant owner declarations sampled before refining this file:
* `lagrangianRelaxationExample : LagrangianProblem _ 1` in `Definition_1_10_3`;
* `lagrangianRelaxationExampleMinimizerTrajectory` in `Proposition_1_10_5`;
* `lagrangianRelaxationExampleLambdaStar_mem_dualFeasibleSet` and
  `lagrangianRelaxationExampleLambdaStar_isMaxOn_dualFeasibleSet` in `Proposition_1_10_12`;
* `LagrangianProblem.globalOptimality_of_dualCertificate` in `Theorem_1_10_4`;
* `lagrangianRelaxationExampleTrajectory_atLambdaStar` in `Proposition_1_10_12`.

Best owner abstraction: the primitive owner remains
`lagrangianRelaxationExample : LagrangianProblem (EuclideanSpace ℝ (Fin 2)) 1`.

Primitive data used here:
* the dual maximizer `lagrangianRelaxationExampleLambdaStar`;
* the owner trajectory `lagrangianRelaxationExampleMinimizerTrajectory`.

Derived API used here:
* `argmin[lagrangianRelaxationExample.feasibleSet] lagrangianRelaxationExample`;
* `lagrangianRelaxationExample.lagrangianMinimizers`;
* `lagrangianRelaxationExampleLambdaStar_mem_dualFeasibleSet`;
* `lagrangianRelaxationExampleLambdaStar_isMaxOn_dualFeasibleSet`;
* `LagrangianProblem.globalOptimality_of_dualCertificate`;
* the coordinate rewrite `lagrangianRelaxationExampleTrajectory_atLambdaStar`.

Source/core/bridge triage:
* source-facing: the textbook point `(2^(-1 / 3), 2^(1 / 3))`;
* core/canonical: `lagrangianRelaxationExample` together with
  `LagrangianProblem.globalOptimality_of_dualCertificate`;
* bridge/view: `lagrangianRelaxationExampleTrajectory_atLambdaStar`, which identifies the owner
  trajectory value with the textbook coordinates.
-/

/-- Helper for Example 1.10.6: a multiplier in `ℝ^1` is determined by its single coordinate. -/
lemma one_dim_multiplier_eq_single (lam : Λ) :
    lam = EuclideanSpace.single 0 (lam 0) := by
  -- Collapse the one-dimensional multiplier to its only coordinate.
  ext i
  fin_cases i
  rfl

/-- Helper for Example 1.10.6: every multiplier in the certificate ball still has coordinate
strictly below the domain boundary `1`. -/
lemma multiplier_coord_lt_one_of_mem_certificate_ball {lam : Λ}
    (hmem : lam ∈ Metric.closedBall Λ⋆ ((1 - λ⋆) / 2) ∩ ℝ₊^1) :
    lam 0 < 1 := by
  rcases hmem with ⟨hball, _⟩
  rw [Metric.mem_closedBall, dist_eq_norm] at hball
  -- Rewrite the one-dimensional distance to a scalar absolute value.
  have habs : |lam 0 - λ⋆| ≤ (1 - λ⋆) / 2 := by
    simpa [show lam - Λ⋆ = EuclideanSpace.single 0 (lam 0 - λ⋆) by
      ext i
      fin_cases i
      rfl, PiLp.norm_single, Real.norm_eq_abs] using hball
  have hupper : lam 0 - λ⋆ ≤ (1 - λ⋆) / 2 := (abs_le.mp habs).2
  linarith [lagrangianRelaxationExampleLambdaStar_lt_one]

/-- Helper for Example 1.10.6: the explicit minimizer trajectory varies continuously at the
dual maximizer. -/
lemma lagrangianRelaxationExampleTrajectory_continuousAt_dualMaximizer :
    ContinuousAt (fun lam : Λ ↦ lagrangianRelaxationExampleMinimizerTrajectory (lam 0)) Λ⋆ := by
  -- Read the unique coordinate of `Λ` through `WithLp.ofLp` so coordinate continuity is explicit.
  have hlam0 : ContinuousAt (fun lam : Λ ↦ lam 0) Λ⋆ := by
    have hofLp : ContinuousAt (fun lam : Λ ↦ WithLp.ofLp lam) Λ⋆ := by
      simpa [Function.comp] using
        (PiLp.continuous_ofLp 2 (fun _ : Fin 1 ↦ ℝ)).continuousAt
    simpa [Function.comp] using ((continuous_apply 0).continuousAt.comp hofLp)
  have hcoord0 : ContinuousAt (fun lam : Λ ↦ (1 : ℝ) - lam 0) Λ⋆ :=
    continuousAt_const.sub hlam0
  have hdenom : 1 - λ⋆ ≠ 0 := by
    linarith [lagrangianRelaxationExampleLambdaStar_lt_one]
  have hcoord1 : ContinuousAt (fun lam : Λ ↦ (1 : ℝ) / (1 - lam 0)) Λ⋆ := by
    -- The second coordinate is continuous because the denominator stays nonzero at `λ⋆`.
    exact ContinuousAt.div continuousAt_const hcoord0 hdenom
  -- Package the continuous scalar coordinates back into the trajectory vector.
  change ContinuousAt
    (fun lam : Λ ↦ WithLp.toLp 2 ![(1 : ℝ) - lam 0, (1 : ℝ) / (1 - lam 0)])
    Λ⋆
  refine (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℝ)).continuousAt.comp ?_
  rw [continuousAt_pi]
  intro i
  fin_cases i
  · simpa using hcoord0
  · simpa using hcoord1

/-- Helper for Example 1.10.6: the example constraint vector is continuous at the trajectory
point corresponding to the dual maximizer. -/
lemma lagrangianRelaxationExample_constraintVector_continuousAt_trajectory_dualMaximizer :
    ContinuousAt lagrangianRelaxationExample.constraintVector
      (lagrangianRelaxationExampleMinimizerTrajectory λ⋆) := by
  let xStar := lagrangianRelaxationExampleMinimizerTrajectory λ⋆
  -- Expose the two primal coordinates through `WithLp.ofLp`.
  have hx0 : ContinuousAt (fun x : EuclideanSpace ℝ (Fin 2) ↦ x 0) xStar := by
    have hofLp :
        ContinuousAt (fun x : EuclideanSpace ℝ (Fin 2) ↦ WithLp.ofLp x) xStar := by
      simpa [Function.comp] using
        (PiLp.continuous_ofLp 2 (fun _ : Fin 2 ↦ ℝ)).continuousAt
    simpa [Function.comp] using ((continuous_apply 0).continuousAt.comp hofLp)
  have hx1 : ContinuousAt (fun x : EuclideanSpace ℝ (Fin 2) ↦ x 1) xStar := by
    have hofLp :
        ContinuousAt (fun x : EuclideanSpace ℝ (Fin 2) ↦ WithLp.ofLp x) xStar := by
      simpa [Function.comp] using
        (PiLp.continuous_ofLp 2 (fun _ : Fin 2 ↦ ℝ)).continuousAt
    simpa [Function.comp] using ((continuous_apply 1).continuousAt.comp hofLp)
  have hscalar :
      ContinuousAt
        (fun x : EuclideanSpace ℝ (Fin 2) ↦ x 0 - (1 / 2 : ℝ) * x 1 ^ (2 : ℕ))
        xStar := by
    -- The single scalar constraint is a polynomial in the two coordinates.
    exact hx0.sub (continuousAt_const.mul (hx1.pow 2))
  -- Rewrite the packaged constraint vector into its one-dimensional coordinate form.
  rw [show lagrangianRelaxationExample.constraintVector =
      fun x : EuclideanSpace ℝ (Fin 2) ↦
        WithLp.toLp 2 (fun _ : Fin 1 ↦ x 0 - (1 / 2 : ℝ) * x 1 ^ (2 : ℕ)) by
      funext x
      ext i
      fin_cases i
      rfl]
  refine (PiLp.continuous_toLp 2 (fun _ : Fin 1 ↦ ℝ)).continuousAt.comp ?_
  rw [continuousAt_pi]
  intro i
  fin_cases i
  simpa using hscalar

/-- Example 1.10.6: the point `x(λ_*) = (2^(-1 / 3), 2^(1 / 3))` obtained from the explicit
dual maximizer `λ_* = 1 - (1 / 2)^(1 / 3)` is a global optimal solution of the example
constrained problem. -/
theorem lagrangianRelaxationExampleOptimalPoint_isGlobalOptimal :
    WithLp.toLp 2
        ![Real.rpow (2 : ℝ) (-(1 / 3 : ℝ)),
          Real.rpow (2 : ℝ) (1 / 3 : ℝ)] ∈
      argmin[lagrangianRelaxationExample.feasibleSet] lagrangianRelaxationExample := by
  let ε : ℝ := (1 - λ⋆) / 2
  let xPath : Λ → EuclideanSpace ℝ (Fin 2) :=
    fun lam ↦ lagrangianRelaxationExampleMinimizerTrajectory (lam 0)
  have hlamStar : Λ⋆ ∈ lagrangianRelaxationExample.dualFeasibleSet := by
    simpa using lagrangianRelaxationExampleLambdaStar_mem_dualFeasibleSet
  have hmax :
      IsMaxOn lagrangianRelaxationExample.dualFunction
        lagrangianRelaxationExample.dualFeasibleSet Λ⋆ := by
    simpa using lagrangianRelaxationExampleLambdaStar_isMaxOn_dualFeasibleSet
  have hε : 0 < ε := by
    dsimp [ε]
    linarith [lagrangianRelaxationExampleLambdaStar_lt_one]
  have hxPath :
      ∀ ⦃lam : Λ⦄,
        lam ∈ Metric.closedBall Λ⋆ ε ∩ ℝ₊^1 →
          lam ≠ Λ⋆ →
          xPath lam ∈ lagrangianRelaxationExample.lagrangianMinimizers lam := by
    intro lam hmem _
    -- Inside the certificate ball, the scalar multiplier stays in the dual-domain interval.
    have hlam_lt_one : lam 0 < 1 := by
      simpa [ε] using multiplier_coord_lt_one_of_mem_certificate_ball hmem
    -- Rewrite the one-dimensional multiplier into the scalar form expected by Proposition 1.10.5.
    rw [one_dim_multiplier_eq_single lam]
    simpa [xPath] using
      lagrangianRelaxationExampleMinimizerTrajectory_mem_lagrangianMinimizers
        (lam 0) hlam_lt_one
  have hlim :
      Tendsto xPath
        (nhdsWithin Λ⋆
          ((Metric.closedBall Λ⋆ ε ∩ ℝ₊^1) \ {Λ⋆}))
        (nhds (lagrangianRelaxationExampleMinimizerTrajectory λ⋆)) := by
    -- The punctured-neighborhood limit follows from ordinary continuity at `Λ⋆`.
    have hcontPath : ContinuousAt xPath Λ⋆ := by
      simpa [xPath] using lagrangianRelaxationExampleTrajectory_continuousAt_dualMaximizer
    simpa [xPath] using hcontPath.tendsto.mono_left
      (show nhdsWithin Λ⋆ ((Metric.closedBall Λ⋆ ε ∩ ℝ₊^1) \ {Λ⋆}) ≤ nhds Λ⋆ from
        nhdsWithin_le_nhds)
  have hcont :
      ContinuousAt lagrangianRelaxationExample.constraintVector
        (lagrangianRelaxationExampleMinimizerTrajectory λ⋆) := by
    -- The packaged constraint map is continuous because its single coordinate is polynomial.
    simpa using
      lagrangianRelaxationExample_constraintVector_continuousAt_trajectory_dualMaximizer
  have hxStar :
      lagrangianRelaxationExampleMinimizerTrajectory λ⋆ ∈
        lagrangianRelaxationExample.lagrangianMinimizers Λ⋆ := by
    have hsingleton :
        lagrangianRelaxationExample.lagrangianMinimizers Λ⋆ =
          ({lagrangianRelaxationExampleMinimizerTrajectory λ⋆} :
            Set (EuclideanSpace ℝ (Fin 2))) := by
      change
        lagrangianRelaxationExample.lagrangianMinimizers (single 0 λ⋆) =
          ({lagrangianRelaxationExampleMinimizerTrajectory λ⋆} :
            Set (EuclideanSpace ℝ (Fin 2)))
      simpa using
        lagrangianRelaxationExample_lagrangianMinimizers_eq_singleton λ⋆
          lagrangianRelaxationExampleLambdaStar_lt_one
    rw [hsingleton]
    simp
  have hoptimal :
      lagrangianRelaxationExampleMinimizerTrajectory λ⋆ ∈
        argmin[lagrangianRelaxationExample.feasibleSet] lagrangianRelaxationExample := by
    simpa [ε, xPath] using
      lagrangianRelaxationExample.globalOptimality_of_dualCertificate
        xPath
        (lagrangianRelaxationExampleMinimizerTrajectory λ⋆)
        hlamStar hmax hε hxPath hlim hcont hxStar
  simpa [lagrangianRelaxationExampleTrajectory_atLambdaStar] using hoptimal
