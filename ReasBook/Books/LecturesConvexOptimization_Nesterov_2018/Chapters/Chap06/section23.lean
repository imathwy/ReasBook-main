import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_23 (from Chap06) -/
open scoped BigOperators
open scoped ConstrainedArgmin

universe u

noncomputable section

variable {m : ℕ}
variable {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁]

/-
Definition 6.23 lies in the constrained finite-residual `ℓ₁`-minimization domain.

Sampled owner-style declarations:
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner for a
  feasible set together with a real-valued objective;
- `fenchelConjugate` in `Chap06/Definition_6_1`, the chapter owner for source-facing dual data on
  `Module.Dual ℝ E₁`;
- `maxAbsoluteValueOptimizationObjective` in `Chap06/Definition_6_21`, the nearby Chapter 6
  finite-family objective already stated with rows in `Module.Dual ℝ E₁`;
- `vectorMap` in `Chap03/Lemma_3_1_16`, the project owner for packaging a finite scalar family as
  an `ℝ^m`-valued map;
- `EuclideanSpace.l1Seminorm` and `EuclideanSpace.lpSeminorm_one_eq_l1Seminorm` in
  `Chap03/Definition_3_7`, the chapter owner for the finite `ℓ₁` norm and its source-facing
  coordinate formula;
- `equationSystemOptimizationProblem` in `Chap01/Example_1_1_6`, the earlier project pattern of
  defining a source-facing optimization problem directly as a `SetConstrainedMinimizationProblem`
  instead of rebuilding a parallel wrapper.

Best owner abstraction:
- source-facing: `sumAbsoluteValuesObjective` and `sumAbsoluteValuesOptimizationProblem`;
- core/canonical: `SetConstrainedMinimizationProblem`, `vectorMap`, and
  `EuclideanSpace.l1Seminorm`;
- bridge/view: the coordinate expansion `∑ j, |a j x - b j|`.

Primitive data:
- the feasible set `Q₁`;
- a finite row family `a : Fin m → Module.Dual ℝ E₁`;
- a finite offset family `b : Fin m → ℝ`.

Derived API:
- the affine residual family `x ↦ a j x - b j`;
- the residual vector `vectorMap (fun j x ↦ a j x - b j) x`;
- the `ℓ₁`-objective value `EuclideanSpace.l1Seminorm m ...`;
- the packaged constrained problem in the Chapter 1 owner.
-/

/-- The objective `x ↦ ∑ⱼ |aⱼ x - b⁽ʲ⁾|` for the sum-of-absolute-values problem. -/
def sumAbsoluteValuesObjective
    (a : Fin m → Module.Dual ℝ E₁) (b : Fin m → ℝ) : E₁ → ℝ :=
  EuclideanSpace.l1Seminorm m ∘ vectorMap (fun j x ↦ a j x - b j)

/-- Evaluating the sum-of-absolute-values objective expands to the finite sum of absolute
residuals. -/
@[simp] theorem sumAbsoluteValuesObjective_apply
    (a : Fin m → Module.Dual ℝ E₁) (b : Fin m → ℝ) (x : E₁) :
    sumAbsoluteValuesObjective a b x = ∑ j : Fin m, |a j x - b j| := by
  rw [sumAbsoluteValuesObjective, Function.comp_apply, EuclideanSpace.l1Seminorm_apply]
  simp

/-- Definition 6.23: the sum-of-absolute-values optimization problem on a feasible set `Q₁`
minimizes `x ↦ ∑ⱼ |aⱼ x - b⁽ʲ⁾|` over `Q₁`. -/
def sumAbsoluteValuesOptimizationProblem
    (Q₁ : Set E₁) (a : Fin m → Module.Dual ℝ E₁) (b : Fin m → ℝ) :
    SetConstrainedMinimizationProblem E₁ where
  feasibleSet := Q₁
  objective := sumAbsoluteValuesObjective a b

/-- The feasible set of the sum-of-absolute-values optimization problem is exactly `Q₁`. -/
@[simp] theorem sumAbsoluteValuesOptimizationProblem_feasibleSet_eq
    (Q₁ : Set E₁) (a : Fin m → Module.Dual ℝ E₁) (b : Fin m → ℝ) :
    (sumAbsoluteValuesOptimizationProblem Q₁ a b).feasibleSet = Q₁ :=
  rfl

/-- Unfolding the sum-of-absolute-values optimization problem recovers the constrained problem with
feasible set `Q₁` and objective `sumAbsoluteValuesObjective a b`. -/
@[simp] theorem sumAbsoluteValuesOptimizationProblem_def
    (Q₁ : Set E₁) (a : Fin m → Module.Dual ℝ E₁) (b : Fin m → ℝ) :
    sumAbsoluteValuesOptimizationProblem Q₁ a b =
      { feasibleSet := Q₁
        objective := sumAbsoluteValuesObjective a b } :=
  rfl

-- Proof sketch: unfold `sumAbsoluteValuesOptimizationProblem`, then rewrite the objective by
-- `sumAbsoluteValuesObjective_apply`.
/-- Evaluating the objective of the sum-of-absolute-values optimization problem yields the finite
sum of absolute residuals `∑ⱼ |aⱼ x - b⁽ʲ⁾|`. -/
@[simp] theorem sumAbsoluteValuesOptimizationProblem_apply
    (Q₁ : Set E₁) (a : Fin m → Module.Dual ℝ E₁) (b : Fin m → ℝ) (x : E₁) :
    sumAbsoluteValuesOptimizationProblem Q₁ a b x = ∑ j : Fin m, |a j x - b j| := sorry

/-- The feasible set of the sum-of-absolute-values optimization problem is exactly `Q₁`. -/
@[simp] theorem sumAbsoluteValuesOptimizationProblem_feasibleSet
    (Q₁ : Set E₁) (a : Fin m → Module.Dual ℝ E₁) (b : Fin m → ℝ) :
    (sumAbsoluteValuesOptimizationProblem Q₁ a b).feasibleSet = Q₁ :=
  sumAbsoluteValuesOptimizationProblem_feasibleSet_eq Q₁ a b

/-- Evaluating the packaged sum-of-absolute-values problem recovers its source-facing objective. -/
@[simp] theorem sumAbsoluteValuesOptimizationProblem_spec
    (Q₁ : Set E₁) (a : Fin m → Module.Dual ℝ E₁) (b : Fin m → ℝ) (x : E₁) :
    sumAbsoluteValuesOptimizationProblem Q₁ a b x = sumAbsoluteValuesObjective a b x :=
  rfl

/-- The objective field of the sum-of-absolute-values optimization problem is the sum-of-absolute-
values objective `x ↦ ∑ⱼ |aⱼ x - b⁽ʲ⁾|`. -/
@[simp] theorem sumAbsoluteValuesOptimizationProblem_objective
    (Q₁ : Set E₁) (a : Fin m → Module.Dual ℝ E₁) (b : Fin m → ℝ) :
    (sumAbsoluteValuesOptimizationProblem Q₁ a b).objective =
      sumAbsoluteValuesObjective a b :=
  rfl

/-- Coercing the sum-of-absolute-values optimization problem to a function recovers its
source-facing objective. -/
@[simp] theorem sumAbsoluteValuesOptimizationProblem_coe
    (Q₁ : Set E₁) (a : Fin m → Module.Dual ℝ E₁) (b : Fin m → ℝ) :
    ⇑(sumAbsoluteValuesOptimizationProblem Q₁ a b) = sumAbsoluteValuesObjective a b :=
  rfl

/-- The minimizer set of the packaged optimization problem is exactly the constrained argmin of
the sum-of-absolute-values objective on the feasible set `Q₁`. -/
-- Proof sketch: extensionality on points, then unfold membership in `argmin`, rewrite the
-- feasible set and objective with the preceding simp lemmas, and simplify.
@[simp] theorem sumAbsoluteValuesOptimizationProblem_argmin
    (Q₁ : Set E₁) (a : Fin m → Module.Dual ℝ E₁) (b : Fin m → ℝ) :
    argmin[(sumAbsoluteValuesOptimizationProblem Q₁ a b).feasibleSet]
        (sumAbsoluteValuesOptimizationProblem Q₁ a b) =
      argmin[Q₁] (sumAbsoluteValuesObjective a b) := sorry

/-- Minimizing the packaged sum-of-absolute-values problem on its feasible set is exactly
minimizing `sumAbsoluteValuesObjective a b` on `Q₁`. -/
-- Proof sketch: unfold the feasible set and objective of
-- `sumAbsoluteValuesOptimizationProblem`, then simplify with the preceding companion lemmas.
@[simp] theorem sumAbsoluteValuesOptimizationProblem_isMinOn_iff
    (Q₁ : Set E₁) (a : Fin m → Module.Dual ℝ E₁) (b : Fin m → ℝ) {x : E₁} :
    IsMinOn (sumAbsoluteValuesOptimizationProblem Q₁ a b)
        (sumAbsoluteValuesOptimizationProblem Q₁ a b).feasibleSet x ↔
      IsMinOn (sumAbsoluteValuesObjective a b) Q₁ x := sorry

/-- Membership in the canonical argmin set of the packaged sum-of-absolute-values problem means
belonging to `Q₁` and minimizing `sumAbsoluteValuesObjective a b` there. -/
-- Proof sketch: rewrite membership with `mem_constrainedArgmin_iff`, then use
-- `sumAbsoluteValuesOptimizationProblem_feasibleSet` and
-- `sumAbsoluteValuesOptimizationProblem_isMinOn_iff`.
@[simp] theorem mem_sumAbsoluteValuesOptimizationProblem_argmin_iff
    (Q₁ : Set E₁) (a : Fin m → Module.Dual ℝ E₁) (b : Fin m → ℝ) {x : E₁} :
    x ∈ argmin[(sumAbsoluteValuesOptimizationProblem Q₁ a b).feasibleSet]
        (sumAbsoluteValuesOptimizationProblem Q₁ a b) ↔
      x ∈ Q₁ ∧ IsMinOn (sumAbsoluteValuesObjective a b) Q₁ x := sorry

end

/-! ### Proposition_6_23 (from Chap06) -/
open scoped BigOperators
open scoped Gradient

noncomputable section

/- Proposition 6.23 lies in Chapter 6's finite-family log-sum-exp / stable max-shift domain.

Sampled owner-style declarations:
- `logSumExp` and `logSumExp_apply` in `Chap05/Definition_5_4_7_11`, the project owner for the
  unscaled finite log-sum-exp potential on `EuclideanSpace ℝ (Fin n)`;
- `convexOn_log_sum_exp_of_convexOn` in `Chap03/Proposition_3_21`, the project owner theorem for
  finite-family log-sum-exp on a common domain;
- `smoothMaxInnerApproximation` in `Chap07/Definition_7_42`, the later project smoothing owner
  using the canonical positive-parameter surface `{μ : ℝ // 0 < μ}`;
- `logSumExpMaxEigenvalueSmoothing` in `Chap06/Definition_6_47`, the analogous Chapter 6
  positive-parameter log-sum-exp owner for spectral smoothing;
- `entropyRegularizedSimplexObjective_softmax_eq_value` in `Chap06/Lemma_6_4`, a direct
  downstream use of the scaled log-sum-exp owner.

Best owner abstraction:
- source-facing: `coordinateMaximum`, `centeredByCoordinateMaximum`, `η`, and the stable
  shift/gradient identities of Proposition 6.23;
- core/canonical: the finite-family positive-parameter owner `η`;
- bridge/view: `eta_apply`.

Primitive data:
- a finite index type `ι`;
- the positive smoothing parameter `μ : {μ : ℝ // 0 < μ}`;
- the score vector `u : EuclideanSpace ℝ ι`.

Derived API:
- the finite-maximum expansion `coordinateMaximum_def`;
- the coordinate formula `centeredByCoordinateMaximum_apply`;
- the evaluation formula `eta_apply`;
- the shift and gradient invariance theorems.

This file stays at the source-facing Chapter 6 layer. The positive-parameter log-sum-exp owner
`η` is stated at the intrinsic finite-family level, while the stable max-shift specialization
continues to use the coordinate-owner `coordinateMaximum` on the same finite score vectors.
-/

universe v

variable {ι : Type v} [Fintype ι]

/-- The log-sum-exp smoothing potential
`η_μ(u) = μ log (∑ⱼ exp (uⱼ / μ))` on a finite score family for a positive smoothing parameter
`μ`. -/
def η (μ : {μ : ℝ // 0 < μ}) (u : EuclideanSpace ℝ ι) : ℝ :=
  (μ : ℝ) * Real.log (∑ j : ι, Real.exp (u j / (μ : ℝ)))

/-- Evaluating `η μ` at `u` gives the defining log-sum-exp formula
`μ log (∑ⱼ exp (uⱼ / μ))`. -/
theorem eta_apply (μ : {μ : ℝ // 0 < μ}) (u : EuclideanSpace ℝ ι) :
    η μ u = (μ : ℝ) * Real.log (∑ j : ι, Real.exp (u j / (μ : ℝ))) :=
  rfl

section

variable {m : ℕ} [NeZero m]

local notation "U" => EuclideanSpace ℝ (Fin m)

/-- The maximal coordinate of `u ∈ ℝᵐ`. -/
def coordinateMaximum (u : U) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j : Fin m ↦ u j)

/-- Expanding `coordinateMaximum u` gives the finite maximum of the coordinates of `u`. -/
-- Proof sketch: unfold `coordinateMaximum`; the right-hand side is the defining `Finset.sup'`.
theorem coordinateMaximum_def (u : U) :
    coordinateMaximum u =
      Finset.univ.sup' Finset.univ_nonempty (fun j : Fin m ↦ u j) := rfl

/-- The vector obtained from `u` by subtracting its maximal coordinate from every component. -/
def centeredByCoordinateMaximum (u : U) : U :=
  WithLp.toLp 2 (fun j : Fin m ↦ u j - coordinateMaximum u)

/-- Each coordinate of `centeredByCoordinateMaximum u` is obtained by subtracting
`coordinateMaximum u` from the corresponding coordinate of `u`. -/
-- Proof sketch: unfold `centeredByCoordinateMaximum`; `WithLp.toLp` preserves the displayed
-- coordinate formula.
theorem centeredByCoordinateMaximum_apply (u : U) (j : Fin m) :
    centeredByCoordinateMaximum u j = u j - coordinateMaximum u := rfl

/-- Proposition 6.23 (1): if `v` is obtained from `u` by subtracting the maximal coordinate
`coordinateMaximum u` from every component, then the log-sum-exp potential satisfies
`η(u) = coordinateMaximum u + η(v)`. -/
-- Proof sketch: factor `exp (coordinateMaximum u / μ)` out of the finite sum
-- `∑ⱼ exp (uⱼ / μ)`, rewrite the remaining summand using
-- `centeredByCoordinateMaximum_apply`, and then apply `Real.log_mul` to pull out the additive
-- term `coordinateMaximum u`.
theorem eta_eq_coordinateMaximum_add_eta_centered
    (μ : {μ : ℝ // 0 < μ}) (u : U) :
    η μ u = coordinateMaximum u + η μ (centeredByCoordinateMaximum u) := sorry

/-- Proposition 6.23 (2): subtracting the same maximal coordinate from every component leaves the
gradient of the log-sum-exp potential unchanged. -/
-- Proof sketch: differentiate the explicit softmax formula for `η`, or differentiate the identity
-- from `eta_eq_coordinateMaximum_add_eta_centered` on regions where the maximizing index is fixed
-- and then use the explicit coordinate formula to remove the local partition.
theorem gradient_eta_eq_gradient_eta_centered
    (μ : {μ : ℝ // 0 < μ}) (u : U) :
    ∇ (η μ) u = ∇ (η μ) (centeredByCoordinateMaximum u) := sorry

end

end
