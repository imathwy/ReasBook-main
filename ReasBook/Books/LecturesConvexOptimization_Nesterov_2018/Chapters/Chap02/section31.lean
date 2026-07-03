import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_31 (from Chap02) -/
noncomputable section

universe u v

/- Primary domain: equality-constrained Lagrangian duality for the Chapter 2 owner
`PrimalEqualityConstrainedProblem`.

Owner declarations sampled before refining this file:
* `PrimalEqualityConstrainedProblem.lagrangian`, `dualFunction`, `lagrangianMinimizers`, and
  `constraintResidual` in `LecturesConvexOptimization_Nesterov_2018/Chap02/Definition_2_30.lean`;
* `SetConstrainedMinimizationProblem.optimalValue` and `argmin[Q]` in
  `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_3_7.lean`, which already provide the canonical optimal-value and
  minimizer-set owners used upstream in `Definition_2_30`;
* `LagrangianProblem.dualFunction` and `LagrangianProblem.lagrangianMinimizers` in
  `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_10_2.lean`, showing the chapter's owner style for fixed-multiplier
  Lagrangian subproblems.

Best owner abstraction:
* source-facing: the equality-problem dual objective together with the auxiliary minimizing
  section `LagrangianMinimizerSelection problem`;
* core/canonical: the equality-problem owner API from `Definition_2_30`;
* bridge/view: the selected residual and selected dual profile obtained by evaluating the owner
  constructions along a minimizing section.

Primitive data:
* `problem : PrimalEqualityConstrainedProblem E Λ`;
* `selection : ∀ u : Λ, problem.lagrangianMinimizers u`.

Derived API:
* `problem.dualObjective`;
* `selection.dualResidual`;
* `selection.selectedDualProfile`;
* the selected-point specializations of `IsMinOn` and `dualFunction_eq_lagrangian`.

This file keeps the minimizing section only as auxiliary attainment data over the equality-problem
owner. It does not introduce a second primal/dual wrapper or a parallel dual-function owner. -/

namespace PrimalEqualityConstrainedProblem

variable {E : Type u} {Λ : Type v} [AddCommMonoid E] [Module ℝ E]
variable [NormedAddCommGroup Λ] [InnerProductSpace ℝ Λ]

/-- Definition 2.31: the equality-constrained Lagrangian dual objective is the negation of the
source-facing dual function `φ(u) = inf_{x ∈ Q} 𝓛(x, u)` attached to `problem`;
minimizing this function over `u ∈ ℝᵐ` is the textbook dual problem. -/
def dualObjective (problem : PrimalEqualityConstrainedProblem E Λ) : Λ → EReal :=
  -problem.dualFunction

/-- Evaluating the equality-constrained dual objective recovers `-φ(u)`. -/
-- Proof sketch: unfold `dualObjective`; the statement is exactly the defining formula.
@[simp] theorem dualObjective_eq_neg_dualFunction
    (problem : PrimalEqualityConstrainedProblem E Λ) (u : Λ) :
    problem.dualObjective u = -problem.dualFunction u :=
  rfl

/-- A chosen minimizer `x(u) ∈ argmin_{x ∈ Q} 𝓛(x, u)` for each dual multiplier `u`, viewed as
auxiliary attainment data over the equality-constrained problem `problem`. -/
abbrev LagrangianMinimizerSelection (problem : PrimalEqualityConstrainedProblem E Λ) :=
  ∀ u : Λ, problem.lagrangianMinimizers u

namespace LagrangianMinimizerSelection

variable {problem : PrimalEqualityConstrainedProblem E Λ}

/-- The residual `g(u) = b - A x(u)` attached to a chosen Lagrangian minimizer selection. -/
def dualResidual (selection : LagrangianMinimizerSelection problem) (u : Λ) : Λ :=
  problem.constraintResidual (selection u)

/-- The real-valued selected dual profile `u ↦ 𝓛(x(u), u)` attached to a chosen minimizing
selection. -/
def selectedDualProfile (selection : LagrangianMinimizerSelection problem) : Λ → ℝ :=
  fun u ↦ problem.lagrangian (selection u) u

end LagrangianMinimizerSelection

namespace LagrangianMinimizerSelectionNotation

/- Source-facing notation for the selected dual profile `φ(u) = 𝓛(x(u), u)`. -/
scoped notation:max "φ[" selection:arg "]" =>
  PrimalEqualityConstrainedProblem.LagrangianMinimizerSelection.selectedDualProfile selection

/- Pointwise source-facing notation for the selected dual profile `φ(u)`. -/
scoped notation:max "φ[" selection:arg "](" u:arg ")" =>
  PrimalEqualityConstrainedProblem.LagrangianMinimizerSelection.selectedDualProfile selection u

/- Source-facing notation for the selected dual residual `g(u) = b - A x(u)`. -/
scoped notation:max "g[" selection:arg "]" =>
  PrimalEqualityConstrainedProblem.LagrangianMinimizerSelection.dualResidual selection

/- Pointwise source-facing notation for the selected dual residual `g(u)`. -/
scoped notation:max "g[" selection:arg "](" u:arg ")" =>
  PrimalEqualityConstrainedProblem.LagrangianMinimizerSelection.dualResidual selection u

end LagrangianMinimizerSelectionNotation

open scoped LagrangianMinimizerSelectionNotation

namespace LagrangianMinimizerSelection

variable {problem : PrimalEqualityConstrainedProblem E Λ}

/-- Expanding the selected dual profile recovers the primal objective plus the multiplier pairing
with the selected residual. -/
-- Proof sketch: unfold `selectedDualProfile`, `dualResidual`, and `problem.lagrangian`, then use
-- the residual-identification lemma from `Definition_2_30`.
theorem selectedDualProfile_eq_objective_add_inner_dualResidual
    (selection : LagrangianMinimizerSelection problem) (u : Λ) :
    φ[selection](u) = problem (selection u) + inner ℝ u (g[selection](u)) :=
  rfl

/-- The selected point `x(u)` is a global minimizer of the Lagrangian subproblem over `Q`. -/
-- Proof sketch: each `selection u` is by definition a point of
-- `problem.lagrangianMinimizers u`, and the source-facing characterization of that
-- set is exactly `IsMinOn`.
theorem isMinOn (selection : LagrangianMinimizerSelection problem) (u : Λ) :
    IsMinOn
      (fun x ↦ problem.lagrangian x u)
      problem.feasibleSet
      (selection u) := by
  simpa using (problem.mem_lagrangianMinimizers_iff.mp (selection u).2).2

/-- Evaluating the Lagrangian at a selected minimizer realizes the dual function. -/
-- Proof sketch: apply the equality-problem theorem
-- `problem.dualFunction_eq_lagrangian` to the minimizer witness
-- `(selection u).2`.
theorem dualFunction_eq_lagrangian
    (selection : LagrangianMinimizerSelection problem) (u : Λ) :
    problem.dualFunction u = (problem.lagrangian (selection u) u : EReal) :=
  problem.dualFunction_eq_lagrangian (selection u).2

/-- The dual function equals the selected real-valued dual profile attached to a minimizing
selection. -/
-- Proof sketch: expand `selectedDualProfile` and rewrite with
-- `dualFunction_eq_lagrangian`.
theorem dualFunction_eq_selectedDualProfile
    (selection : LagrangianMinimizerSelection problem) (u : Λ) :
    problem.dualFunction u = (φ[selection](u) : EReal) := by
  simpa [selectedDualProfile] using selection.dualFunction_eq_lagrangian u

/-- A minimizing selection realizes the dual objective as the negated selected Lagrangian value.
-/
-- Proof sketch: rewrite the dual function by
-- `dualFunction_eq_selectedDualProfile` and then unfold `problem.dualObjective`.
theorem dualObjective_eq_neg_selectedDualProfile
    (selection : LagrangianMinimizerSelection problem) (u : Λ) :
    problem.dualObjective u = -(φ[selection](u) : EReal) := by
  rw [dualObjective_eq_neg_dualFunction, selection.dualFunction_eq_selectedDualProfile]

end LagrangianMinimizerSelection

end PrimalEqualityConstrainedProblem

/-! ### Proposition_2_31 (from Chap02) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {m : ℕ} {μ L : ℝ}

open SmoothMinimaxProblem
open scoped Gradient

section

variable {problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L}

local notation "parametricProblem" => problem.toParametricSmoothMinimaxProblem

local notation "objective" =>
  fun t x ↦ (parametricProblem t) x

local notation "modelValue" =>
  problem.regularizedModelValue

local notation "feasibleObjectiveValues" =>
  fun t ↦ Set.range fun x : problem.ambientSet ↦ objective t (x : E)

/-
Primary domain: Chapter 2 constrained suboptimality gaps for the parametric max-type objective.

Owner abstractions sampled before refining:
- `SmoothFunctionalConstraintsMinimizationProblem.toParametricSmoothMinimaxProblem` from
  `Definition_2_47.lean`, the owner fixed-`t` smooth minimax problem;
- `IsMinOn.isGLB` in mathlib and the fixed-parameter `IsGLB` owner interface already used in
  `Proposition_2_30.lean` for exact suboptimality gaps;
- `LagrangianProblem.min_sub_zero_le_constrainedAuxiliaryOptimalValue` from `Lemma_2_21.lean`,
  the owner sign law relating the auxiliary optimal value to the threshold parameter `tStar`;
- the explicit recurrent data `k ↦ (x_k, t_k, x_{k,j^*(k)})`, which are the primitive objects
  actually used by Proposition 2.31;
- `LagrangianProblem.constrainedAuxiliaryObjective_shift_le` from `Lemma_2_21.lean`, the owner
  monotonicity statement in the parameter `t`, used only for the companion bridge corollary;
- `SmoothMinimaxProblem.objective_le_upperRegularizedModel` from `Text_2_4.lean`, the owner
  comparison between the fixed-`t` objective and the `L`-model, likewise used only in the
  companion bridge corollary.

Primitive data here are only the scalar comparison sequence `Δ` and its textbook recurrence.
The fixed-`t` objective and the regularized `L`-model values are derived from the owner
parametric minimax problem, while the exact real optimal value is supplied canonically through the
feasible-range `IsGLB` hypothesis, matching the Chapter 1/2 owner style for source-facing gap
statements. The source-facing proposition takes the displayed comparison inequality
`f(t_{k+1}; x_{k+1}) ≤ f(t_k; x_{k+1}) ≤ f^*(t_k; x_{k,j^*(k)}; L)` as primitive input, while the
stronger derivation from parameter monotonicity and an exact upper-model step is kept as
bridge-level companion API.

Source/core/bridge triage:
- source-facing: the textbook suboptimality gap
  `f(t_k; x_k) - f^*(t_k)`, the threshold data `t_k ≤ tStar`, and the comparison sequence `Δ_k`;
- core/canonical: the fixed-`t` owner `parametricProblem t` together with the exact feasible-range
  value interface `IsGLB (feasibleObjectiveValues t) (fStar t)`, plus the primal-value owner
  `IsGLB (Set.range fun x : problem.feasibleSet ↦ problem x) tStar`;
- bridge/view: `problem.regularizedModelValue`, parameter monotonicity, and the upper-model
  exact-step hypothesis.
-/

/-- Helper for Proposition 2.31: the exact optimal value `fStar k` is nonnegative whenever the
parameter `t k` stays below the primal threshold `tStar`. -/
lemma fstar_nonneg_of_threshold
    (t : ℕ → ℝ)
    (fStar : ℕ → ℝ)
    (tStar : ℝ)
    (hprimal : IsGLB (Set.range fun x : problem.feasibleSet ↦ problem x) tStar)
    (ht_le : ∀ k : ℕ, t k ≤ tStar)
    (hoptimal :
      ∀ k : ℕ, IsGLB (feasibleObjectiveValues (t k)) (fStar k)) :
    ∀ k : ℕ, 0 ≤ fStar k := by
  intro k
  -- Show that `0` is a lower bound for every feasible objective value at the parameter `t k`.
  refine (hoptimal k).2 ?_
  intro y hy
  rcases hy with ⟨x, rfl⟩
  have haux : min (tStar - t k) 0 ≤ problem.constrainedAuxiliaryObjective (t k) x := by
    -- The threshold-sign bridge gives the universal lower bound `min (tStar - t k) 0`.
    simpa using
      problem.min_sub_zero_le_constrainedAuxiliaryObjective (tStar := tStar) hprimal (t k) x
  have hmin_eq : min (tStar - t k) 0 = 0 := by
    -- Below threshold, the bridge lower bound collapses to `0`.
    rw [min_eq_right]
    linarith [ht_le k]
  simpa [hmin_eq] using haux

/-- Helper for Proposition 2.31: an attained minimizer of the selected regularized affine model
realizes the corresponding model value. -/
lemma regularizedModelValue_eq_of_isMinOn
    (τ : ℝ)
    (xBar xPlus : problem.ambientSet)
    (hmin :
      IsMinOn
        (quadraticallyRegularizedObjective
          ((parametricProblem τ).affineApproximation (xBar : E))
          L
          (xBar : E))
        problem.ambientSet
        (xPlus : E)) :
    modelValue τ (xBar : E) L =
      quadraticallyRegularizedObjective
        ((parametricProblem τ).affineApproximation (xBar : E))
        L
        (xBar : E)
        (xPlus : E) := by
  let upperModel : E → ℝ :=
    quadraticallyRegularizedObjective
      ((parametricProblem τ).affineApproximation (xBar : E))
      L
      (xBar : E)
  have hglb : IsGLB (upperModel '' problem.ambientSet) (upperModel (xPlus : E)) :=
    hmin.isGLB xPlus.property
  -- The real infimum defining `modelValue` is exactly the attained minimum of the upper model.
  rw [SmoothFunctionalConstraintsMinimizationProblem.regularizedModelValue]
  exact hglb.csInf_eq ⟨upperModel (xPlus : E), ⟨(xPlus : E), xPlus.property, rfl⟩⟩

/-- Helper for Proposition 2.31: parameter monotonicity and an exact upper-model step produce the
two-sided comparison hypothesis required by the source-facing gap estimate. -/
lemma comparison_of_monotone_upper_model
    (x xSelected : ℕ → problem.ambientSet)
    (t : ℕ → ℝ)
    (ht_mono : Monotone t)
    (hupper_min :
      ∀ k : ℕ,
        IsMinOn
          (quadraticallyRegularizedObjective
            ((parametricProblem (t k)).affineApproximation (xSelected k : E))
            L
            (xSelected k : E))
          problem.ambientSet
          (x (k + 1) : E)) :
    ∀ k : ℕ,
      objective (t (k + 1)) (x (k + 1) : E) ≤ objective (t k) (x (k + 1) : E) ∧
        objective (t k) (x (k + 1) : E) ≤ modelValue (t k) (xSelected k : E) L := by
  intro k
  constructor
  · have hdiff_nonneg : 0 ≤ t (k + 1) - t k := by
      exact sub_nonneg.mpr (ht_mono (Nat.le_succ k))
    have hshift :=
      problem.constrainedAuxiliaryObjective_shift_le
        (t := t k)
        (Δ := t (k + 1) - t k)
        hdiff_nonneg
        (x (k + 1))
    -- Rewrite the shifted-parameter owner inequality back to the fixed-`t` objective notation.
    simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using hshift
  · have hupper :=
      (parametricProblem (t k)).objective_le_upperRegularizedModel
        (xSelected k : E)
        (x (k + 1) : E)
    have hmodel_eq :
        modelValue (t k) (xSelected k : E) L =
          quadraticallyRegularizedObjective
            ((parametricProblem (t k)).affineApproximation (xSelected k : E))
            L
            (xSelected k : E)
            (x (k + 1) : E) := by
      -- The exact-step hypothesis identifies the selected model value with its attained value.
      simpa using regularizedModelValue_eq_of_isMinOn
        (problem := problem)
        (τ := t k)
        (xBar := xSelected k)
        (xPlus := x (k + 1))
        (hmin := hupper_min k)
    -- Combine the upper-model comparison with the attained model-value identity.
    rw [hmodel_eq]
    simpa using hupper

/-- Proposition 2.31: if the master parameters satisfy `t_k ≤ tStar` and the textbook comparison
`f(t_{k+1}; x_{k+1}) ≤ f(t_k; x_{k+1}) ≤ f^*(t_k; x_{k,j^*(k)}; L)` holds at each step, then the
constrained suboptimality gap `f(t_k; x_k) - f^*(t_k)` is bounded by the comparison quantity
`Δ_k`. The exact values `fStar k` are supplied canonically by `IsGLB`, while the nonnegativity of
these values is obtained from `t_k ≤ tStar` through the Chapter 2 threshold-sign owner API rather
than taken as a primitive hypothesis. -/
-- Proof sketch: use `ht_le` together with the primal-value hypothesis `hprimal` and the owner
-- threshold bound from Lemma 2.21 to obtain `0 ≤ fStar k` for every `k`. For `k = 0`, rewrite
-- by `hΔ_zero` and bound `f(t₀; x₀) - f^*(t₀)` by `f(t₀; x₀)`. For `k + 1`, rewrite by
-- `hΔ_succ k`, use the displayed comparison inequality `hcomparison k` to bound
-- `f(t_{k+1}; x_{k+1})` by the selected `L`-model value, and again subtract the nonnegative
-- optimal value `f^*(t_{k+1})`.
theorem suboptimality_le_constrainedMinimizationDelta
    (x xSelected : ℕ → problem.ambientSet)
    (t : ℕ → ℝ)
    (fStar : ℕ → ℝ)
    (Δ : ℕ → ℝ)
    (tStar : ℝ)
    (hΔ_zero : Δ 0 = objective (t 0) (x 0 : E))
    (hΔ_succ : ∀ k : ℕ,
      Δ (k + 1) = modelValue (t k) (xSelected k : E) L)
    (hprimal : IsGLB (Set.range fun x : problem.feasibleSet ↦ problem x) tStar)
    (ht_le : ∀ k : ℕ, t k ≤ tStar)
    (hoptimal :
      ∀ k : ℕ, IsGLB (feasibleObjectiveValues (t k)) (fStar k))
    (hcomparison :
      ∀ k : ℕ,
        objective (t (k + 1)) (x (k + 1) : E) ≤ objective (t k) (x (k + 1) : E) ∧
          objective (t k) (x (k + 1) : E) ≤ modelValue (t k) (xSelected k : E) L) :
    ∀ k : ℕ,
      objective (t k) (x k : E) - fStar k ≤ Δ k := by
  have hfstar_nonneg :
      ∀ k : ℕ, 0 ≤ fStar k :=
    fstar_nonneg_of_threshold
      (problem := problem)
      (t := t)
      (fStar := fStar)
      (tStar := tStar)
      (hprimal := hprimal)
      ht_le
      hoptimal
  intro k
  cases k with
  | zero =>
      -- At the base index, the textbook definition `Δ₀ = f(t₀; x₀)` closes the gap bound once
      -- `fStar 0` is known nonnegative.
      simpa [hΔ_zero] using
        sub_le_self (objective (t 0) (x 0 : E)) (hfstar_nonneg 0)
  | succ k =>
      have hstep :
          objective (t (k + 1)) (x (k + 1) : E) ≤ modelValue (t k) (xSelected k : E) L :=
        (hcomparison k).1.trans (hcomparison k).2
      have hgap :
          objective (t (k + 1)) (x (k + 1) : E) - fStar (k + 1) ≤
            objective (t (k + 1)) (x (k + 1) : E) :=
        sub_le_self _ (hfstar_nonneg (k + 1))
      -- The displayed comparison bounds the current objective, and subtracting the nonnegative
      -- exact optimal value can only decrease it.
      simpa [hΔ_succ k] using hgap.trans hstep

/-- Bridge corollary: the source-facing comparison hypothesis of Proposition 2.31 follows from
parameter monotonicity together with an exact minimizer of the selected upper model. -/
-- Proof sketch: derive
-- `objective (t (k + 1)) (x (k + 1)) ≤ objective (t k) (x (k + 1))`
-- from `ht_mono` and `LagrangianProblem.constrainedAuxiliaryObjective_shift_le`. Then identify
-- the selected `L`-model value with the attained value at `x (k + 1)` using the exact-step
-- hypothesis `hupper_min`, and apply
-- `SmoothMinimaxProblem.objective_le_upperRegularizedModel` to obtain
-- `objective (t k) (x (k + 1)) ≤ modelValue (t k) (xSelected k) L`. Finally invoke the
-- source-facing theorem `suboptimality_le_constrainedMinimizationDelta`.
theorem suboptimality_le_constrainedMinimizationDelta_of_monotone_upperModel
    (x xSelected : ℕ → problem.ambientSet)
    (t : ℕ → ℝ)
    (fStar : ℕ → ℝ)
    (Δ : ℕ → ℝ)
    (tStar : ℝ)
    (hΔ_zero : Δ 0 = objective (t 0) (x 0 : E))
    (hΔ_succ : ∀ k : ℕ,
      Δ (k + 1) = modelValue (t k) (xSelected k : E) L)
    (hprimal : IsGLB (Set.range fun x : problem.feasibleSet ↦ problem x) tStar)
    (ht_le : ∀ k : ℕ, t k ≤ tStar)
    (hoptimal :
      ∀ k : ℕ, IsGLB (feasibleObjectiveValues (t k)) (fStar k))
    (ht_mono : Monotone t)
    (hupper_min :
      ∀ k : ℕ,
        IsMinOn
          (quadraticallyRegularizedObjective
            ((parametricProblem (t k)).affineApproximation (xSelected k : E))
            L
            (xSelected k : E))
          problem.ambientSet
          (x (k + 1) : E)) :
    ∀ k : ℕ,
      objective (t k) (x k : E) - fStar k ≤ Δ k := by
  have hcomparison :
      ∀ k : ℕ,
        objective (t (k + 1)) (x (k + 1) : E) ≤ objective (t k) (x (k + 1) : E) ∧
          objective (t k) (x (k + 1) : E) ≤ modelValue (t k) (xSelected k : E) L :=
    comparison_of_monotone_upper_model
      (problem := problem)
      (x := x)
      (xSelected := xSelected)
      (t := t)
      ht_mono
      hupper_min
  -- Feed the derived comparison family into the source-facing proposition.
  exact suboptimality_le_constrainedMinimizationDelta
    (problem := problem)
    x
    xSelected
    t
    fStar
    Δ
    tStar
    hΔ_zero
    hΔ_succ
    hprimal
    ht_le
    hoptimal
    hcomparison

end

/-! ### Theorem_2_31 (from Chap02) -/
/- Theorem 2.31 corresponds to the textbook Theorem 2.3.1, the constrained optimality criterion
for the max-type problem `min_{x ∈ Q} max_i fᵢ(x)` on `ℝⁿ`.

Primary domain:
* constrained finite max-type convex minimization in the Euclidean textbook presentation

Sampled owner-style declarations:
* `maxTypeObjective` in `Lemma_2_18`, the owner max objective of a nonempty finite family;
* `maxTypeAffineApproximation` in `Definition_2_39`, the owner affine max model at a base point;
* `ConvexOn.isMinOn_iff_variational_inequality_of_hasGradientAt` in `Theorem_2_29`, the chapter's
  constrained first-order optimality owner behind the max-type criterion;
* `isMinOn_maxTypeObjective_iff_affineApproximation_ge` in `Theorem_2_39`, the canonical
  project-level theorem with the exact mathematical content of Theorem 2.3.1.

Best owner abstraction:
* `isMinOn_maxTypeObjective_iff_affineApproximation_ge`

Primitive data:
* the feasible set `Q`;
* the component family `fs`;
* componentwise convexity on `Q`;
* feasibility of the base point `xStar`;
* differentiability of each component at `xStar`.

Derived API:
* the constrained minimizing predicate `IsMinOn (maxTypeObjective fs) Q xStar`;
* the affine lower-model condition
  `∀ x ∈ Q, maxTypeAffineApproximation fs xStar x ≥ maxTypeObjective fs xStar`.

Source/core/bridge triage:
* source-facing: Theorem 2.3.1 in the textbook `ℝⁿ` / `Fin m` presentation;
* core/canonical: `isMinOn_maxTypeObjective_iff_affineApproximation_ge`;
* bridge/view: the specialization `E = EuclideanSpace ℝ (Fin n)` and `ι = Fin m`.

This file therefore keeps no parallel local theorem shell. The numbered textbook item is recalled
directly from the existing chapter owner theorem at the correct abstraction level. -/

/- Theorem 2.31 / Theorem 2.3.1 is the direct owner recall of the constrained max-type
optimality criterion. The textbook `ℝⁿ` / `Fin m` formulation is the Euclidean specialization of
this owner theorem. -/
recall isMinOn_maxTypeObjective_iff_affineApproximation_ge
