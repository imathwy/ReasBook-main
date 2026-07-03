import Mathlib
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_1_8_6 (from Chap01) -/
open Matrix
open scoped Gradient

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "PosMat" => {A : Mat // Matrix.PosDef A}

/- Proposition 1.8.6 is a bridge/view statement in weighted differential calculus.

Source/core/bridge triage:
* source-facing: the formulas expressing the gradient and Hessian in the inner product induced by a
  positive-definite matrix `A`
* core/canonical: the intrinsic owners `gradient` and `hessian` for the weighted inner-product
  structure determined by `A`
* bridge/view: the Euclidean carrier owners `weightedGradient A` and `weightedHessian A`, which
  make the metric parameter explicit and record the weighted owners through Euclidean formulas

Primary domain:
* weighted first- and second-order differential calculus on finite-dimensional real inner-product
  spaces

Sampled owner-style declarations:
* `Matrix.PosDef.WeightedSpace` from Definition 1.8.3
* `HasWeightedGradientSecondOrderExpansionAt.iff_hasGradientAt_and_hasFDerivAt_gradient` from
  Definition 1.8.4
* `gradient` from mathlib's gradient API
* `hessian` from Definition 1.4.16

Best owner abstraction:
* the weighted-space `gradient`/`hessian` pair as core owners
* the coordinate transport `EuclideanSpace.equiv (Fin n) ℝ`, used only as a bridge from the
  weighted coordinate model to the Euclidean formulas

Primitive data:
* `A : PosMat`
* `f : Matrix.PosDef.WeightedSpace A → ℝ`
* `x : E`

Derived API:
* the transported weighted gradient `e.symm (∇ f (e x))`
* the transported weighted Hessian
  `(e.symm : _ →L[ℝ] _).comp (hessian f (e x)).comp (e : _ →L[ℝ] _)`
* the Euclidean formulas identifying those intrinsic weighted owners with `A⁻¹` applied to the
  Euclidean gradient/Hessian of the transported function

The proposition therefore stays at the `bridge/view` layer: it keeps the chapter's canonical
weighted `gradient`/`hessian` owners central, and records only their coordinate transport to the
Euclidean formulas. -/

namespace Matrix.PosDef

section
variable (A : PosMat)

/-- Proposition 1.8.6 (1): after transporting the intrinsic weighted gradient on
`Matrix.PosDef.WeightedSpace A` to Euclidean coordinates, one obtains `A⁻¹` applied to the
Euclidean gradient of the transported function. -/
theorem gradient_eq_inverse_gradient (f : WeightedSpace A → ℝ) (x : E) :
    let e : E ≃L[ℝ] WeightedSpace A :=
      (EuclideanSpace.equiv (Fin n) ℝ).toLinearEquiv.toContinuousLinearEquiv
    e.symm (∇ f (e x)) = (A.1⁻¹).toEuclideanLin (∇ (f ∘ e) x) := by
  sorry

/-- Proposition 1.8.6 (2): after transporting the intrinsic weighted Hessian on
`Matrix.PosDef.WeightedSpace A` to Euclidean coordinates, one obtains the inverse metric composed
with the Euclidean Hessian of the transported function. -/
theorem hessian_eq_inverse_comp_hessian (f : WeightedSpace A → ℝ) (x : E) :
    let e : E ≃L[ℝ] WeightedSpace A :=
      (EuclideanSpace.equiv (Fin n) ℝ).toLinearEquiv.toContinuousLinearEquiv
    let K : WeightedSpace A →L[ℝ] WeightedSpace A := hessian f (e x)
    let H₀ : WeightedSpace A →L[ℝ] E := (e.symm : WeightedSpace A →L[ℝ] E).comp K
    let H : E →L[ℝ] E :=
      H₀.comp (e : E →L[ℝ] WeightedSpace A)
    H =
      (A.1⁻¹).toEuclideanLin.toContinuousLinearMap.comp (hessian (f ∘ e) x) := by
  sorry

end

end Matrix.PosDef

end

/-! ### Example_1_8_7 (from Chap01) -/
open scoped Gradient
open Matrix

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Example 1.8.7 is `source-facing`: it identifies the textbook Newton direction for a quadratic
objective with the displacement to the minimizer, and therefore shows that one Newton step lands
at the minimizer.

Sampled owner-style declarations:
* `NewtonSystem.step` from Algorithm 1.7.1
* `newtonSystem_step_eq_matrixFormula` from Proposition 1.8.2
* `UnconstrainedQuadraticMinimizationProblem.gradient_eq` from Proposition 1.9.11

Best owner abstractions:
* the canonical Newton step `NewtonSystem.step (∇ problem.objective)`
* `UnconstrainedQuadraticMinimizationProblem n` for the quadratic objective data

Primitive data:
* `problem`
* `x`

Derived API:
* the source-facing Newton direction formula
* the source-facing textbook Newton update formula

Source/core/bridge triage:
* source-facing: the Newton direction and the one-step textbook update formula
* core/canonical: the Newton owner `NewtonSystem.step (∇ problem.objective)`
* bridge/view: the quadratic identities `problem.gradient_eq x` and
  `newtonSystem_step_eq_matrixFormula`
-/

namespace UnconstrainedQuadraticMinimizationProblem

private theorem hessian_eq
    (problem : UnconstrainedQuadraticMinimizationProblem n) (x : E) :
    ∇² problem.objective x = problem.A := by
  let A := problem.A.toEuclideanLin
  apply Matrix.toEuclideanLin.injective
  have hgrad :
      fderiv ℝ (∇ problem.objective) x = A.toContinuousLinearMap := by
    have hfun :
        ∇ problem.objective = fun y : E ↦
          A y - A problem.minimizer := by
      funext y
      simpa [LinearMap.map_sub] using problem.gradient_eq y
    rw [hfun]
    simpa [A] using ((A.toContinuousLinearMap.hasFDerivAt).sub_const
      (A problem.minimizer)).fderiv
  calc
    (∇² problem.objective x).toEuclideanLin = hessian problem.objective x := by
      simpa using hessianMatrix_toEuclideanLin problem.objective x
    _ = A := by
      exact congrArg ContinuousLinearMap.toLinearMap hgrad

private theorem hessian_posDef
    (problem : UnconstrainedQuadraticMinimizationProblem n) (x : E) :
    (∇² problem.objective x).PosDef := by
  simpa [hessian_eq problem x] using problem.posDef

private theorem gradient_det_ne_zero
    (problem : UnconstrainedQuadraticMinimizationProblem n) (x : E) :
    (fderiv ℝ (∇ problem.objective) x).det ≠ 0 :=
  hessian_det_ne_zero_of_posDef problem.objective x (hessian_posDef problem x)

theorem newtonDirection_eq_sub_minimizer
    (problem : UnconstrainedQuadraticMinimizationProblem n) (x : E) :
    (problem.A⁻¹).toEuclideanLin (∇ problem.objective x) = x - problem.minimizer := by
  rw [problem.gradient_eq]
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hdet : problem.A.det ≠ 0 := ne_of_gt problem.posDef.det_pos
  change toLin b b (problem.A⁻¹) (toLin b b problem.A (x - problem.minimizer)) =
      x - problem.minimizer
  rw [← toLin_mul_apply b b b (problem.A⁻¹) problem.A (x - problem.minimizer)]
  simp [toLin_one, b, hdet]

/-- Example 1.8.7: the canonical Newton step for the quadratic stationarity system `∇ f = 0`
lands at the minimizer in one iteration. -/
theorem newtonStep_eq_minimizer
    (problem : UnconstrainedQuadraticMinimizationProblem n) (x : E) :
    NewtonSystem.step (∇ problem.objective) ⟨x, gradient_det_ne_zero problem x⟩ =
      problem.minimizer := by
  calc
    NewtonSystem.step (∇ problem.objective) ⟨x, gradient_det_ne_zero problem x⟩
        = x - ((∇² problem.objective x)⁻¹).toEuclideanLin (∇ problem.objective x) := by
            simpa [gradient_det_ne_zero] using
              newtonSystem_step_eq_matrixFormula problem.objective x (hessian_posDef problem x)
    _ = x - (problem.A⁻¹).toEuclideanLin (∇ problem.objective x) := by
      rw [hessian_eq problem x]
    _ = problem.minimizer := by
      rw [problem.newtonDirection_eq_sub_minimizer x]
      simp

/-- Example 1.8.7 companion: the Newton update reaches the canonical minimizer in one step. -/
theorem newtonUpdate_eq_minimizer
    (problem : UnconstrainedQuadraticMinimizationProblem n) (x : E) :
    x - (problem.A⁻¹).toEuclideanLin (∇ problem.objective x) = problem.minimizer := by
  calc
    x - (problem.A⁻¹).toEuclideanLin (∇ problem.objective x)
        = NewtonSystem.step (∇ problem.objective) ⟨x, gradient_det_ne_zero problem x⟩ := by
            symm
            calc
              NewtonSystem.step (∇ problem.objective) ⟨x, gradient_det_ne_zero problem x⟩
                  = x - ((∇² problem.objective x)⁻¹).toEuclideanLin (∇ problem.objective x) := by
                      simpa [gradient_det_ne_zero] using
                        newtonSystem_step_eq_matrixFormula problem.objective x
                          (hessian_posDef problem x)
              _ = x - (problem.A⁻¹).toEuclideanLin (∇ problem.objective x) := by
                rw [hessian_eq problem x]
    _ = problem.minimizer := problem.newtonStep_eq_minimizer x

end UnconstrainedQuadraticMinimizationProblem

end

/-! ### Lemma_1_8_8 (from Chap01) -/
noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Lemma 1.8.8 lies in the domain of transporting global minimizers along ambient translations in
Euclidean space.

Sampled owner-style declarations before refinement:
* `IsMinOn.on_preimage` in mathlib’s `Order.Filter.Extr`, the canonical transport rule for minima
  under pullback along a map;
* `isMinOn_univ_iff` in the same file, the canonical univ-specialization of global minimality;
* `UnconstrainedQuadraticMinimizationProblem.minimizer` in `Definition_1_9_1`;
* `Matrix.isPositive_toEuclideanLin_iff`, the bridge from positive semidefinite matrices to
  positive operators on Euclidean space.

Owner abstraction:
* `IsMinOn` transported by `IsMinOn.on_preimage`.

Primitive data:
* an unconstrained quadratic problem `problem`;
* a translation vector `xBar`.

Derived API:
* `problem.objective`;
* `problem.minimizer`;
* the local centered minimizer statement proved below;
* the translated minimizer statement below.

Source/core/bridge triage:
* source-facing: the translated quadratic model centered at `xBar`;
* core/canonical: completing the square around `problem.minimizer`;
* bridge/view: the affine translation `x ↦ x - xBar`.
-/

namespace UnconstrainedQuadraticMinimizationProblem

/-- Helper for Lemma 1.8.8: the canonical point `problem.minimizer = -A⁻¹ a` satisfies
`A problem.minimizer = -a`. -/
lemma apply_matrix_to_minimizer_eq_neg_linear_coefficient
    (problem : UnconstrainedQuadraticMinimizationProblem n) :
    problem.A.toEuclideanLin problem.minimizer = -problem.a := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hdet : problem.A.det ≠ 0 := ne_of_gt problem.posDef.det_pos
  -- Move to matrix coordinates so that `A * A⁻¹ = 1` cancels directly.
  change Matrix.toLin b b problem.A (-Matrix.toLin b b problem.A⁻¹ problem.a) = -problem.a
  rw [LinearMap.map_neg]
  rw [← Matrix.toLin_mul_apply b b b problem.A problem.A⁻¹ problem.a]
  simp [Matrix.toLin_one, b, hdet]

/-- Helper for Lemma 1.8.8: symmetry of the positive-definite matrix lets us move `A` across the
Euclidean inner product. -/
lemma matrix_inner_apply_swap
    (problem : UnconstrainedQuadraticMinimizationProblem n) (z w : E) :
    inner ℝ (problem.A.toEuclideanLin z) w =
      inner ℝ z (problem.A.toEuclideanLin w) := by
  have hsymm : problem.A.IsSymm := by
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using problem.posDef.1
  -- Rewrite the adjoint action through the transpose, then use symmetry of `A`.
  calc
    inner ℝ (problem.A.toEuclideanLin z) w
      = inner ℝ z ((Matrix.transpose problem.A).toEuclideanLin w) := by
          simpa using matrix_transpose_adjointness problem.A z w
    _ = inner ℝ z (problem.A.toEuclideanLin w) := by
          simp [Matrix.IsSymm.eq hsymm]

/-- Helper for Lemma 1.8.8: completing the square around `problem.minimizer` separates the
objective into its minimum value plus a nonnegative quadratic error. -/
lemma objective_eq_objective_minimizer_add_quadratic_error
    (problem : UnconstrainedQuadraticMinimizationProblem n) (y : E) :
    problem.objective y =
      problem.objective problem.minimizer +
        (1 / 2 : ℝ) * inner ℝ (problem.A.toEuclideanLin (y - problem.minimizer))
          (y - problem.minimizer) := by
  let z : E := y - problem.minimizer
  have hy : y = problem.minimizer + z := by
    simp [z]
  have hmix :
      inner ℝ (problem.A.toEuclideanLin z) problem.minimizer =
        inner ℝ (problem.A.toEuclideanLin problem.minimizer) z := by
    -- Use symmetry to identify the two mixed terms in the square expansion.
    calc
      inner ℝ (problem.A.toEuclideanLin z) problem.minimizer
        = inner ℝ z (problem.A.toEuclideanLin problem.minimizer) :=
            matrix_inner_apply_swap problem z problem.minimizer
      _ = inner ℝ (problem.A.toEuclideanLin problem.minimizer) z := by
            simpa using (real_inner_comm z (problem.A.toEuclideanLin problem.minimizer)).symm
  have hAmin : problem.A.toEuclideanLin problem.minimizer = -problem.a :=
    apply_matrix_to_minimizer_eq_neg_linear_coefficient problem
  -- Expand the objective at `problem.minimizer + z` and cancel the mixed linear terms.
  calc
    problem.objective y
      = problem.α + inner ℝ problem.a problem.minimizer + inner ℝ problem.a z +
          (1 / 2 : ℝ) * inner ℝ (problem.A.toEuclideanLin problem.minimizer)
            problem.minimizer +
          (1 / 2 : ℝ) * inner ℝ (problem.A.toEuclideanLin problem.minimizer) z +
          (1 / 2 : ℝ) * inner ℝ (problem.A.toEuclideanLin z) problem.minimizer +
          (1 / 2 : ℝ) * inner ℝ (problem.A.toEuclideanLin z) z := by
            conv_lhs =>
              rw [UnconstrainedQuadraticMinimizationProblem.objective, quadraticObjective, hy]
              rw [LinearMap.map_add, inner_add_right, inner_add_left, inner_add_right,
                inner_add_right]
            ring
    _ = problem.α + inner ℝ problem.a problem.minimizer + inner ℝ problem.a z +
          (1 / 2 : ℝ) * inner ℝ (problem.A.toEuclideanLin problem.minimizer)
            problem.minimizer +
          inner ℝ (problem.A.toEuclideanLin problem.minimizer) z +
          (1 / 2 : ℝ) * inner ℝ (problem.A.toEuclideanLin z) z := by
            rw [hmix]
            ring
    _ = problem.α + inner ℝ problem.a problem.minimizer +
          (1 / 2 : ℝ) * inner ℝ (problem.A.toEuclideanLin problem.minimizer)
            problem.minimizer +
          (1 / 2 : ℝ) * inner ℝ (problem.A.toEuclideanLin z) z := by
            rw [hAmin]
            have hcancel : inner ℝ problem.a z + inner ℝ (-problem.a) z = 0 := by
              simp
            nlinarith
    _ = problem.objective problem.minimizer +
          (1 / 2 : ℝ) * inner ℝ (problem.A.toEuclideanLin z) z := by
            simp [UnconstrainedQuadraticMinimizationProblem.objective, quadraticObjective]
    _ = problem.objective problem.minimizer +
          (1 / 2 : ℝ) * inner ℝ (problem.A.toEuclideanLin (y - problem.minimizer))
            (y - problem.minimizer) := by
            simp [z]

/-- Helper for Lemma 1.8.8: the quadratic error term is nonnegative because a positive-definite
matrix induces a positive linear operator on Euclidean space. -/
private lemma quadratic_error_nonneg
    (problem : UnconstrainedQuadraticMinimizationProblem n) (y : E) :
    0 ≤ inner ℝ (problem.A.toEuclideanLin y) y := by
  have hpositive : (problem.A.toEuclideanLin : E →ₗ[ℝ] E).IsPositive :=
    Matrix.isPositive_toEuclideanLin_iff.mpr problem.posDef.posSemidef
  -- Positivity of the operator is exactly the nonnegativity of the quadratic form.
  exact hpositive.inner_nonneg_left y

/-- Helper for Lemma 1.8.8: the canonical point `problem.minimizer` minimizes the centered
quadratic objective on the whole space. -/
lemma minimizer_isMinOn
    (problem : UnconstrainedQuadraticMinimizationProblem n) :
    IsMinOn problem Set.univ problem.minimizer := by
  rw [isMinOn_univ_iff]
  intro y
  -- Rewrite the objective as its minimum value plus a nonnegative quadratic error.
  have hobjective :=
    objective_eq_objective_minimizer_add_quadratic_error problem y
  have hnonneg :
      0 ≤ inner ℝ (problem.A.toEuclideanLin (y - problem.minimizer))
        (y - problem.minimizer) :=
    quadratic_error_nonneg problem (y - problem.minimizer)
  have hmin : problem.objective problem.minimizer ≤ problem.objective y := by
    nlinarith [hobjective, hnonneg]
  simpa using hmin

/-- Lemma 1.8.8, owner-centered form: translating the ambient coordinates of an unconstrained
quadratic minimization problem by `xBar` translates its global minimizer by the same amount. -/
theorem isMinOn_translate (problem : UnconstrainedQuadraticMinimizationProblem n) (xBar : E) :
    IsMinOn (fun x ↦ problem (x - xBar)) Set.univ (xBar + problem.minimizer) := by
  let g : E → E := fun x ↦ x - xBar
  -- Pull the centered minimum back through the translation map `x ↦ x - xBar`.
  have hcentered : IsMinOn problem Set.univ (g (xBar + problem.minimizer)) := by
    -- The translated candidate maps back to the centered minimizer.
    simpa [g, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      minimizer_isMinOn problem
  have htranslated : IsMinOn (problem ∘ g) (g ⁻¹' Set.univ) (xBar + problem.minimizer) :=
    hcentered.on_preimage g
  simpa [g, Function.comp, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using htranslated

end UnconstrainedQuadraticMinimizationProblem

end

/-! ### Lemma_1_8_9 (from Chap01) -/
open scoped Gradient

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Lemma 1.8.9 lies in the variable-metric / quasi-Newton recursion domain.

Primary domain:
* variable-metric and quasi-Newton methods on Euclidean space

Sampled owner-style declarations:
* `VariableMetricMethod.metric`
* `VariableMetricMethod.metric_inv_eq_inverseMetric`
* `VariableMetricMethod.x_succ_eq_sub_metric_inv_gradient`
* `hessianMatrix`

Best owner abstraction:
* `VariableMetricMethod.x_succ_eq_sub_metric_inv_gradient`

Primitive data:
* a variable-metric method `method`
* the unit-step specialization `method.stepSize = 1`

Derived/contextual API:
* the metric sequence `Gₖ = Hₖ⁻¹`
* the local-minimum and Hessian-limit quasi-Newton context often used around this recursion

Source/core/bridge triage:
* source-facing: the unit-step quasi-Newton iterate identity
* core/canonical: `VariableMetricMethod.x_succ_eq_sub_metric_inv_gradient`
* bridge/view: the surrounding local-minimum / Hessian-limit interpretation, which does not alter
  the displayed recursion formula

The former file packaged extra quasi-Newton context into a separate predicate and then restated the
owner theorem through that wrapper. The recursion formula itself only depends on the unit-step
specialization, so this refinement keeps the owner theorem directly as the public entry. -/

recall VariableMetricMethod.x_succ_eq_sub_metric_inv_gradient
    {f : E → ℝ} {x0 : E}
    (method : VariableMetricMethod f x0)
    (hstep : method.stepSize = 1) (k : ℕ) :
    method (k + 1) =
      method k -
        ((method.metric k)⁻¹).toEuclideanLin (∇ f (method k))

/-! ### Definition_1_8_11 (from Chap01) -/
variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/-
Definition 1.8.11 is a source-facing recall item in the quasi-Newton inverse-Hessian domain.

Source/core/bridge triage:
* source-facing: the textbook quasi-Newton rule for a candidate next inverse-Hessian matrix
* core/canonical: `Matrix.PosDef` and the matrix action `Matrix.toEuclideanLin`
* bridge/view: the direct proposition `HkNext.PosDef ∧ HkNext.toEuclideanLin γk = δk`, where
  `Matrix.PosDef` packages symmetry together with positive definiteness

Primary domain:
* positive-definite inverse-Hessian matrices and their Euclidean-space action in quasi-Newton
  methods

Sampled owner-style declarations:
* `Matrix.PosDef` in mathlib, the canonical owner for symmetry plus positive definiteness
* `Matrix.toEuclideanLin` in mathlib, the owner linear action of a matrix on Euclidean space
* `Definition_1_4_18` in this chapter, which already recalls `Matrix.PosDef` as the canonical
  owner for `H = Hᵀ > 0`
* `VariableMetricMethod.inverseMetric_posDef` in Algorithm 1.8.10, which records positive
  definiteness of quasi-Newton inverse-metric iterates through `Matrix.PosDef`

Owner abstraction:
* the canonical owner pair `Matrix.PosDef` and `Matrix.toEuclideanLin`

Primitive data:
* the candidate next inverse-Hessian matrix `HkNext`
* the gradient difference `γk`
* the step `δk`

Derived API:
* there is no additional wrapper predicate here; the textbook quasi-Newton rule is the direct
  conjunction of the canonical SPD owner `HkNext.PosDef` with the secant equation
  `HkNext.toEuclideanLin γk = δk`

This recall file intentionally introduces no parallel public wrapper. Downstream Chapter 1 files
should use `Matrix.PosDef` together with the secant equation directly, rather than rebuilding a
local quasi-Newton predicate.
-/

section

variable (HkNext : Mat) (γk δk : E)

/- Definition 1.8.11: a quasi-Newton inverse-Hessian approximation `Hₖ₊₁` is required to be
symmetric positive definite and to satisfy the secant equation `Hₖ₊₁ γₖ = δₖ`. Using the chapter's
canonical owners, this is the proposition `HkNext.PosDef ∧ HkNext.toEuclideanLin γk = δk`, where
`Matrix.PosDef` packages `Hₖ₊₁ = Hₖ₊₁ᵀ > 0`. -/
#check (HkNext.PosDef ∧ HkNext.toEuclideanLin γk = δk : Prop)

end

/-! ### Definition_1_8_11 (from Items/Chap01) -/
variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/-
Definition 1.8.11 is a source-facing recall item in the quasi-Newton inverse-Hessian domain.

Source/core/bridge triage:
* source-facing: the textbook quasi-Newton rule for a candidate next inverse-Hessian matrix
* core/canonical: `Matrix.PosDef` and the matrix action `Matrix.toEuclideanLin`
* bridge/view: the direct proposition `HkNext.PosDef ∧ HkNext.toEuclideanLin γk = δk`, where
  `Matrix.PosDef` packages symmetry together with positive definiteness

Primary domain:
* positive-definite inverse-Hessian matrices and their Euclidean-space action in quasi-Newton
  methods

Sampled owner-style declarations:
* `Matrix.PosDef` in mathlib, the canonical owner for symmetry plus positive definiteness
* `Matrix.toEuclideanLin` in mathlib, the owner linear action of a matrix on Euclidean space
* `Definition_1_4_18` in this chapter, which already recalls `Matrix.PosDef` as the canonical
  owner for `H = Hᵀ > 0`
* `VariableMetricMethod.inverseMetric_posDef` in Algorithm 1.8.10, which records positive
  definiteness of quasi-Newton inverse-metric iterates through `Matrix.PosDef`

Owner abstraction:
* the canonical owner pair `Matrix.PosDef` and `Matrix.toEuclideanLin`

Primitive data:
* the candidate next inverse-Hessian matrix `HkNext`
* the gradient difference `γk`
* the step `δk`

Derived API:
* there is no additional wrapper predicate here; the textbook quasi-Newton rule is the direct
  conjunction of the canonical SPD owner `HkNext.PosDef` with the secant equation
  `HkNext.toEuclideanLin γk = δk`

This recall file intentionally introduces no parallel public wrapper. Downstream Chapter 1 files
should use `Matrix.PosDef` together with the secant equation directly, rather than rebuilding a
local quasi-Newton predicate.
-/

section

recall Matrix.PosDef
    {n : Type*} {R : Type*} [Ring R] [PartialOrder R] [StarRing R] (B : Matrix n n R) :
    Prop

recall Matrix.toEuclideanLin

variable (HkNext : Mat) (γk δk : E)

/- Definition 1.8.11: a quasi-Newton inverse-Hessian approximation `Hₖ₊₁` is required to be
symmetric positive definite and to satisfy the secant equation `Hₖ₊₁ γₖ = δₖ`. Using the chapter's
canonical owners, this is the proposition `HkNext.PosDef ∧ HkNext.toEuclideanLin γk = δk`, where
`Matrix.PosDef` packages `Hₖ₊₁ = Hₖ₊₁ᵀ > 0`. -/
#check (HkNext.PosDef ∧ HkNext.toEuclideanLin γk = δk : Prop)

end

/-! ### Definition_1_8_12 (from Chap01) -/
noncomputable section

open Matrix InnerProductSpace

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/-
Definition 1.8.12 is source-facing through the correction matrix `ΔHₖ`.
Its owner abstraction is the canonical rank-one continuous linear endomorphism of Euclidean space,
and the matrix formula is the standard-basis realization of that operator.

Primary domain:
- rank-one endomorphisms of Euclidean space and their matrix realizations.

Owner declarations sampled before refinement:
- `InnerProductSpace.rankOne`
- `InnerProductSpace.rankOne_apply`
- `Matrix.toEuclideanLin`
- `InnerProductSpace.symm_toEuclideanLin_rankOne`

Primitive data:
- the current inverse-Hessian approximation `Hk`
- the gradient difference `γk`
- the step `δk`

Derived API:
- the source-facing correction matrix `ΔHₖ`
- the action of `ΔHₖ` on `γₖ`
- the secant-equation consequences under the standard SR1 denominator condition

Layer triage:
- `source-facing`: `rankOneCorrectionMatrixDifference`
- `core/canonical`: `Matrix.toEuclideanLin`, `InnerProductSpace.rankOne`
- `bridge/view`: `rankOneCorrectionMatrixDifference_apply`
-/

private abbrev sr1Residual (Hk : Mat) (γk δk : E) : E :=
  δk - Hk.toEuclideanLin γk

/-- Definition 1.8.12: `ΔHₖ` is the standard-basis matrix of the canonical rank-one correction
operator built from the secant residual `δₖ - Hₖ γₖ`, equivalently the textbook SR1
outer-product update. The nonzero denominator hypothesis belongs on the secant consequences rather
than on this source-facing matrix formula itself. -/
def rankOneCorrectionMatrixDifference (Hk : Mat) (γk δk : E) : Mat :=
  let r := sr1Residual Hk γk δk
  toEuclideanLin.symm ((inner ℝ r γk)⁻¹ • rankOne ℝ r r)

/-- Applying the rank-one correction matrix to `γₖ` returns the secant residual. -/
theorem rankOneCorrectionMatrixDifference_apply
    {Hk : Mat} {γk δk : E}
    (hdenom : inner ℝ (δk - Hk.toEuclideanLin γk) γk ≠ 0) :
    (rankOneCorrectionMatrixDifference Hk γk δk).toEuclideanLin γk =
      δk - Hk.toEuclideanLin γk := by
  let r := sr1Residual Hk γk δk
  have hr : inner ℝ r γk ≠ 0 := by
    simpa [r, sr1Residual] using hdenom
  rw [rankOneCorrectionMatrixDifference]
  simp only [LinearEquiv.apply_symm_apply]
  change ((inner ℝ r γk)⁻¹ • rankOne ℝ r r) γk = r
  rw [ContinuousLinearMap.smul_apply, rankOne_apply, smul_smul, inv_mul_cancel₀ hr, one_smul]

/-- Adding the rank-one correction matrix to `Hₖ` enforces the secant equation. -/
-- Proof sketch: evaluate `ΔHₖ` on `γₖ` via its canonical rank-one operator view; the denominator
-- cancellation leaves the secant residual `δₖ - Hₖ γₖ`, so the correction term exactly repairs
-- the original image `Hₖ γₖ`.
theorem rankOneCorrectionMatrixDifference_secantEquation
    (Hk : Mat) (γk δk : E)
    (hdenom : inner ℝ (δk - Hk.toEuclideanLin γk) γk ≠ 0) :
    (Hk + rankOneCorrectionMatrixDifference Hk γk δk).toEuclideanLin γk = δk := by
  rw [show (Hk + rankOneCorrectionMatrixDifference Hk γk δk).toEuclideanLin γk =
      Hk.toEuclideanLin γk +
        (rankOneCorrectionMatrixDifference Hk γk δk).toEuclideanLin γk by
    simp]
  rw [rankOneCorrectionMatrixDifference_apply hdenom]
  simp

end

/-! ### Definition_1_8_13 (from Chap01) -/
noncomputable section

open Matrix InnerProductSpace LinearMap

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/-
Definition 1.8.13 is `source-facing`: it names the Davidon--Fletcher--Powell inverse-Hessian
update matrix.

Primary domain:
- quasi-Newton inverse-Hessian updates on Euclidean space.

Owner abstractions sampled before refinement:
- `Matrix.toEuclideanLin`
- `InnerProductSpace.rankOne`
- `LinearMap.adjoint`
- `LinearMap.adjoint_inner_right`

Primitive data:
- the current inverse-Hessian approximation `Hk`
- the gradient difference `γk`
- the step `δk`

Derived API:
- the source-facing DFP update matrix
- its canonical operator realization under `toEuclideanLin`
- the secant-equation consequence under the two nonvanishing DFP denominators

Layer triage:
- `source-facing`: `dfpUpdatedMatrix`
- `core/canonical`: `Matrix.toEuclideanLin`, `InnerProductSpace.rankOne`
- `bridge/view`: `dfpUpdatedMatrix_toEuclideanLin`
-/

private abbrev dfpUpdateOperator (Hk : Mat) (γk δk : E) : E →ₗ[ℝ] E :=
  let H := Hk.toEuclideanLin
  let curvature := inner ℝ γk δk
  let hγ := H γk
  let imageCurvature := inner ℝ γk hγ
  H + curvature⁻¹ • rankOne ℝ δk δk -
    imageCurvature⁻¹ • rankOne ℝ hγ (adjoint H γk)

/-- Definition 1.8.13: the Davidon--Fletcher--Powell update defines the next inverse-Hessian
approximation by
`Hₖ₊₁ = Hₖ + δₖ δₖᵀ / ⟪γₖ, δₖ⟫ - Hₖ γₖ γₖᵀ Hₖ / ⟪γₖ, Hₖ γₖ⟫`. -/
def dfpUpdatedMatrix (Hk : Mat) (γk δk : E) : Mat :=
  toEuclideanLin.symm (dfpUpdateOperator Hk γk δk)

/-- The DFP update matrix realizes the canonical operator-level DFP formula on Euclidean space. -/
theorem dfpUpdatedMatrix_toEuclideanLin (Hk : Mat) (γk δk : E) :
    (dfpUpdatedMatrix Hk γk δk).toEuclideanLin =
      let H := Hk.toEuclideanLin
      let curvature := inner ℝ γk δk
      let hγ := H γk
      let imageCurvature := inner ℝ γk hγ
      H + curvature⁻¹ • rankOne ℝ δk δk -
        imageCurvature⁻¹ • rankOne ℝ hγ (adjoint H γk) := by
  simp [dfpUpdatedMatrix, dfpUpdateOperator]

/-- The DFP-updated inverse-Hessian approximation satisfies the secant equation `Hₖ₊₁ γₖ = δₖ`
whenever the two DFP denominators are nonzero. -/
-- Proof sketch: pass to the canonical operator formula, apply the two rank-one terms to `γₖ`, and
-- use the adjoint pairing identity to identify the denominator of the second correction term with
-- `⟪γₖ, Hₖ γₖ⟫`.
theorem dfpUpdatedMatrix_secantEquation (Hk : Mat) (γk δk : E)
    (hγδ : inner ℝ γk δk ≠ 0)
    (hγHγ : inner ℝ γk (Hk.toEuclideanLin γk) ≠ 0) :
    (dfpUpdatedMatrix Hk γk δk).toEuclideanLin γk = δk := by
  have hadjoint :
      inner ℝ (LinearMap.adjoint (Hk.toEuclideanLin) γk) γk =
        inner ℝ γk (Hk.toEuclideanLin γk) := by
    calc
      inner ℝ (LinearMap.adjoint (Hk.toEuclideanLin) γk) γk =
          inner ℝ γk (LinearMap.adjoint (Hk.toEuclideanLin) γk) := by
        rw [real_inner_comm]
      _ = inner ℝ (Hk.toEuclideanLin γk) γk := by
        simpa using LinearMap.adjoint_inner_right (Hk.toEuclideanLin) γk γk
      _ = inner ℝ γk (Hk.toEuclideanLin γk) := by
        rw [real_inner_comm]
  rw [dfpUpdatedMatrix]
  simp only [LinearEquiv.apply_symm_apply]
  simp [dfpUpdateOperator, hadjoint, real_inner_comm, hγδ, hγHγ]

end

/-! ### Definition_1_8_14 (from Chap01) -/
noncomputable section

open Matrix InnerProductSpace LinearMap

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/-
Definition 1.8.14 is `source-facing` through the Broyden--Fletcher--Goldfarb--Shanno correction
`ΔHₖ`, with the next inverse-Hessian approximation and the algorithmic update rule derived from
that increment.

Primary domain:
- quasi-Newton inverse-Hessian updates on Euclidean space.

Owner abstractions sampled before refinement:
- the direct secant equation `HkNext.toEuclideanLin γk = δk`, recalled in
  `Definition_1_8_11`
- `Matrix.toEuclideanLin`
- `InnerProductSpace.rankOne`
- `LinearMap.adjoint`

Primitive data:
- the current inverse-Hessian approximation `Hk`
- the gradient difference `γk`
- the step `δk`

Derived API:
- the source-facing BFGS increment `bfgsMatrixDifference`
- the next inverse-Hessian approximation `bfgsUpdatedMatrix = Hk + ΔHₖ`
- the secant-equation and positive-definiteness consequences under the usual curvature hypotheses
- the direct specialization of the secant equation to consecutive gradient and iterate differences

Layer triage:
- `source-facing`: `bfgsMatrixDifference`
- `core/canonical`: the direct secant equation from `Definition_1_8_11`,
  `Matrix.toEuclideanLin`, `Matrix.PosDef`, `InnerProductSpace.rankOne`, `LinearMap.adjoint`
- `bridge/view`: `bfgsUpdatedMatrix`,
  `bfgsUpdatedMatrix_step_secantEquation`
-/
private abbrev bfgsDifferenceOperator (Hk : Mat) (γk δk : E) : E →ₗ[ℝ] E :=
  let H := Hk.toEuclideanLin
  let rho : ℝ := (inner ℝ γk δk)⁻¹
  let hγ := H γk
  let beta := 1 + inner ℝ hγ γk * rho
  H + (beta * rho) • rankOne ℝ δk δk -
    rho • (rankOne ℝ hγ δk + rankOne ℝ δk (adjoint H γk))

/-- Definition 1.8.14: `ΔHₖ` is the Broyden--Fletcher--Goldfarb--Shanno (BFGS) correction
`(βₖ / ⟪γₖ, δₖ⟫) δₖ δₖᵀ - (Hₖ γₖ δₖᵀ + δₖ γₖᵀ Hₖ) / ⟪γₖ, δₖ⟫`,
where `βₖ = 1 + ⟪Hₖ γₖ, γₖ⟫ / ⟪γₖ, δₖ⟫`. The curvature hypotheses belong on the secant and
positivity theorems rather than on this source-facing matrix formula. -/
def bfgsMatrixDifference (Hk : Mat) (γk δk : E) : Mat :=
  toEuclideanLin.symm (bfgsDifferenceOperator Hk γk δk - Hk.toEuclideanLin)

/-- The BFGS correction matrix realizes the canonical operator-level BFGS formula on Euclidean
space. -/
theorem bfgsMatrixDifference_toEuclideanLin (Hk : Mat) (γk δk : E) :
    (bfgsMatrixDifference Hk γk δk).toEuclideanLin =
      let H := Hk.toEuclideanLin
      let rho : ℝ := (inner ℝ γk δk)⁻¹
      let hγ := H γk
      let beta := 1 + inner ℝ hγ γk * rho
      (beta * rho) • rankOne ℝ δk δk -
        rho • (rankOne ℝ hγ δk + rankOne ℝ δk (adjoint H γk)) := by
  rw [bfgsMatrixDifference]
  simp only [LinearEquiv.apply_symm_apply]
  dsimp [bfgsDifferenceOperator]
  abel

/-- The BFGS update defines the next inverse-Hessian approximation by `Hₖ₊₁ = Hₖ + ΔHₖ`. -/
def bfgsUpdatedMatrix (Hk : Mat) (γk δk : E) : Mat :=
  Hk + bfgsMatrixDifference Hk γk δk

/-- Helper for Definition 1.8.14: evaluating the adjoint on the same vector recovers the same
quadratic scalar as evaluating the original map. -/
theorem inner_adjoint_apply_self_eq_inner_apply_self (H : E →ₗ[ℝ] E) (γ : E) :
    inner ℝ (LinearMap.adjoint H γ) γ = inner ℝ γ (H γ) := by
  -- Rewrite the left inner product through the adjoint pairing and then commute the real inner
  -- product back to the source-side quadratic scalar.
  calc
    inner ℝ (LinearMap.adjoint H γ) γ =
        inner ℝ γ (LinearMap.adjoint H γ) := by
      rw [real_inner_comm]
    _ = inner ℝ (H γ) γ := by
      simpa using LinearMap.adjoint_inner_right H γ γ
    _ = inner ℝ γ (H γ) := by
      rw [real_inner_comm]

/-- Helper for Definition 1.8.14: the BFGS-updated matrix realizes the canonical operator-level
BFGS formula on Euclidean space. -/
theorem bfgsUpdatedMatrix_toEuclideanLin (Hk : Mat) (γk δk : E) :
    (bfgsUpdatedMatrix Hk γk δk).toEuclideanLin =
      let H := Hk.toEuclideanLin
      let rho : ℝ := (inner ℝ γk δk)⁻¹
      let hγ := H γk
      let beta := 1 + inner ℝ hγ γk * rho
      H + (beta * rho) • rankOne ℝ δk δk -
        rho • (rankOne ℝ hγ δk + rankOne ℝ δk (adjoint H γk)) := by
  -- The updated operator is exactly the original map plus the canonical BFGS correction term.
  rw [bfgsUpdatedMatrix]
  rw [LinearEquiv.map_add]
  rw [bfgsMatrixDifference_toEuclideanLin]
  simp [sub_eq_add_neg, add_assoc]

/-- Helper for Definition 1.8.14: symmetry of `Hₖ` lets us swap `Hₖ` across the Euclidean inner
product. -/
theorem isSymm_inner_toEuclideanLin_swap (Hk : Mat) (hHk : Hk.IsSymm) (x y : E) :
    inner ℝ x (Hk.toEuclideanLin y) = inner ℝ (Hk.toEuclideanLin x) y := by
  -- Transport matrix symmetry to the linear operator view and use the defining symmetric identity.
  have hsymm : (Hk.toEuclideanLin : E →ₗ[ℝ] E).IsSymmetric :=
    (Matrix.isSymmetric_toEuclideanLin_iff (A := Hk)).2 <| by
      simpa [Matrix.IsSymm, Matrix.IsHermitian] using hHk
  exact (hsymm x y).symm

/-- Helper for Definition 1.8.14: when `Hₖ` is symmetric, the BFGS operator has the standard
factorized form `(I - ρ δ γᵀ) Hₖ (I - ρ γ δᵀ) + ρ δ δᵀ`. -/
theorem bfgsUpdatedMatrix_toEuclideanLin_factorized (Hk : Mat) (γk δk : E)
    (hHk : Hk.IsSymm) :
    (bfgsUpdatedMatrix Hk γk δk).toEuclideanLin =
      let H := Hk.toEuclideanLin
      let rho : ℝ := (inner ℝ γk δk)⁻¹
      (((1 : E →ₗ[ℝ] E) - rho • rankOne ℝ δk γk) * H *
        ((1 : E →ₗ[ℝ] E) - rho • rankOne ℝ γk δk)) +
        rho • rankOne ℝ δk δk := by
  -- Route correction: expand the factorization at a test vector and rewrite the mixed
  -- `⟪γₖ, Hₖ x⟫` term only once using symmetry of `Hₖ.toEuclideanLin`.
  rw [bfgsUpdatedMatrix_toEuclideanLin]
  dsimp
  have hsymm : (Hk.toEuclideanLin : E →ₗ[ℝ] E).IsSymmetric :=
    (Matrix.isSymmetric_toEuclideanLin_iff (A := Hk)).2 <| by
      simpa [Matrix.IsSymm, Matrix.IsHermitian] using hHk
  have hAdj : LinearMap.adjoint (Hk.toEuclideanLin : E →ₗ[ℝ] E) = Hk.toEuclideanLin := by
    simpa using hsymm.adjoint_eq
  -- Compare the two operators coordinatewise after one common expansion.
  ext x i
  simp only [smul_add, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
    ContinuousLinearMap.coe_coe, rankOne_apply, PiLp.sub_apply, PiLp.add_apply, ofLp_toLpLin,
    toLin'_apply, PiLp.smul_apply, smul_eq_mul, Module.End.mul_apply, Module.End.one_apply,
    map_sub, map_smul]
  rw [hAdj, isSymm_inner_toEuclideanLin_swap Hk hHk γk γk,
    isSymm_inner_toEuclideanLin_swap Hk hHk γk x]
  ring_nf

/-- Helper for Definition 1.8.14: the left BFGS rank-one perturbation is the adjoint of the
corresponding right perturbation. -/
theorem bfgs_rankOne_perturbation_adjoint (γk δk : E) (rho : ℝ) :
    ((1 : E →ₗ[ℝ] E) - rho • rankOne ℝ δk γk) =
      ((1 : E →ₗ[ℝ] E) - rho • rankOne ℝ γk δk).adjoint := by
  -- Verify the adjoint identity through the defining inner-product relation.
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  simp [rankOne_apply, sub_eq_add_neg, smul_smul, real_inner_comm, inner_add_left,
    inner_add_right, inner_smul_left, inner_smul_right, mul_comm]
  ring

/-- Helper for Definition 1.8.14: a positive-definite matrix yields a strictly positive Euclidean
quadratic form on every nonzero vector. -/
theorem posDef_inner_toEuclideanLin_pos (Hk : Mat) (hHkPosDef : Hk.PosDef) {x : E} (hx : x ≠ 0) :
    0 < inner ℝ x (Hk.toEuclideanLin x) := by
  have hx' : x.ofLp ≠ 0 := by
    simpa using hx
  have hdot : 0 < x.ofLp ⬝ᵥ Hk *ᵥ x.ofLp := hHkPosDef.dotProduct_mulVec_pos (x := x.ofLp) hx'
  calc
    0 < x.ofLp ⬝ᵥ Hk *ᵥ x.ofLp := hdot
    _ = (Hk.toEuclideanLin x).ofLp ⬝ᵥ x.ofLp := by
      simp [Matrix.ofLp_toLpLin, Matrix.toLin'_apply, dotProduct_comm]
    _ = inner ℝ x (Hk.toEuclideanLin x) := by
      simpa using (EuclideanSpace.inner_eq_star_dotProduct x (Hk.toEuclideanLin x)).symm

/-- Helper for Definition 1.8.14: a positive-definite `Hₖ` gives a strictly positive quadratic
form for the updated BFGS operator under the curvature condition. -/
theorem bfgsUpdatedMatrix_inner_pos (Hk : Mat) (γk δk : E) (hHkPosDef : Hk.PosDef)
    (hγδ : 0 < inner ℝ γk δk) {x : E} (hx : x ≠ 0) :
    0 < inner ℝ x ((bfgsUpdatedMatrix Hk γk δk).toEuclideanLin x) := by
  have hHkSymm : Hk.IsSymm := by
    simpa using hHkPosDef.1
  let rho : ℝ := (inner ℝ γk δk)⁻¹
  let S : E →ₗ[ℝ] E := (1 : E →ₗ[ℝ] E) - rho • rankOne ℝ γk δk
  have hrepr : (bfgsUpdatedMatrix Hk γk δk).toEuclideanLin =
      ((1 : E →ₗ[ℝ] E) - rho • rankOne ℝ δk γk) * Hk.toEuclideanLin * S +
        rho • rankOne ℝ δk δk := by
    simpa [S, rho] using bfgsUpdatedMatrix_toEuclideanLin_factorized Hk γk δk hHkSymm
  -- The factorization exposes the transported vector `v = (I - ρ γ δᵀ) x`.
  rw [hrepr, bfgs_rankOne_perturbation_adjoint γk δk rho]
  let v : E := S x
  have hrho : 0 < rho := by
    dsimp [rho]
    exact inv_pos.mpr hγδ
  have hdecomp :
      inner ℝ x ((S.adjoint * Hk.toEuclideanLin * S + rho • rankOne ℝ δk δk) x) =
        inner ℝ v (Hk.toEuclideanLin v) + rho * (inner ℝ δk x)^2 := by
    -- Move the left factor across the inner product and collect the explicit rank-one term.
    dsimp [v]
    simp only [inner_add_right, inner_smul_right]
    rw [LinearMap.adjoint_inner_right, real_inner_comm x δk]
    ring_nf
  rw [hdecomp]
  by_cases hv : v = 0
  · -- If the transported vector vanishes, the curvature term must carry the positivity.
    have hs : inner ℝ δk x ≠ 0 := by
      intro hs0
      apply hx
      dsimp [v, S, rho] at hv
      ext i
      have hi := congrArg (fun z : E => z.ofLp i) hv
      simp only [hs0, PiLp.zero_apply, PiLp.sub_apply, PiLp.smul_apply, zero_smul] at hi
      simpa using hi
    have hsq : 0 < (inner ℝ δk x)^2 := sq_pos_of_ne_zero hs
    have hterm : 0 < rho * (inner ℝ δk x)^2 := mul_pos hrho hsq
    simpa [hv] using hterm
  · -- Otherwise the conjugated positive-definite quadratic form is already strictly positive.
    have hmain : 0 < inner ℝ v (Hk.toEuclideanLin v) :=
      posDef_inner_toEuclideanLin_pos Hk hHkPosDef hv
    have hterm : 0 ≤ rho * (inner ℝ δk x)^2 := mul_nonneg hrho.le (sq_nonneg _)
    linarith

/-- The BFGS updated matrix remains symmetric when the current quasi-Newton matrix is symmetric. -/
-- Proof sketch: `Hₖ` is symmetric by hypothesis, `δₖ δₖᵀ` is symmetric, and if `Hₖ` is symmetric
-- then `(Hₖᵀ) γₖ = Hₖ γₖ`, so the mixed term in `ΔHₖ` is the sum of a matrix and its transpose.
theorem bfgsUpdatedMatrix_isSymm (Hk : Mat) (γk δk : E) (hHk : Hk.IsSymm) :
    (bfgsUpdatedMatrix Hk γk δk).IsSymm := by
  apply (Matrix.isSymmetric_toEuclideanLin_iff (A := bfgsUpdatedMatrix Hk γk δk)).1
  let rho : ℝ := (inner ℝ γk δk)⁻¹
  let S : E →ₗ[ℝ] E := (1 : E →ₗ[ℝ] E) - rho • rankOne ℝ γk δk
  have hrepr : (bfgsUpdatedMatrix Hk γk δk).toEuclideanLin =
      ((1 : E →ₗ[ℝ] E) - rho • rankOne ℝ δk γk) * Hk.toEuclideanLin * S +
        rho • rankOne ℝ δk δk := by
    simpa [S, rho] using bfgsUpdatedMatrix_toEuclideanLin_factorized Hk γk δk hHk
  have hsymm : (Hk.toEuclideanLin : E →ₗ[ℝ] E).IsSymmetric :=
    (Matrix.isSymmetric_toEuclideanLin_iff (A := Hk)).2 <| by
      simpa [Matrix.IsSymm, Matrix.IsHermitian] using hHk
  -- Replace the left perturbation by the adjoint of the right perturbation.
  rw [hrepr, bfgs_rankOne_perturbation_adjoint γk δk rho]
  have hconj : (S.adjoint * Hk.toEuclideanLin * S).IsSymmetric :=
    hsymm.adjoint_conj S
  have hrank : (rankOne ℝ δk δk : E →ₗ[ℝ] E).IsSymmetric := by
    simp
  have hrho : star rho = rho := by
    simp [rho]
  -- The factorized term is symmetric by conjugation, and the correction is a symmetric rank-one
  -- operator scaled by a real scalar.
  exact hconj.add (LinearMap.IsSymmetric.smul hrho hrank)

/-- Helper for Definition 1.8.14: the Euclidean quadratic form of `A.toEuclideanLin` matches the
matrix quadratic form `xᵀ A x`. -/
theorem inner_toEuclideanLin_eq_dotProduct_mulVec (A : Mat) (x : E) :
    inner ℝ x (A.toEuclideanLin x) = x.ofLp ⬝ᵥ A *ᵥ x.ofLp := by
  -- First view the Euclidean inner product as a dot product, then unfold the matrix action.
  calc
    inner ℝ x (A.toEuclideanLin x) = (A.toEuclideanLin x).ofLp ⬝ᵥ x.ofLp := by
      simpa using (EuclideanSpace.inner_eq_star_dotProduct x (A.toEuclideanLin x))
    _ = x.ofLp ⬝ᵥ A *ᵥ x.ofLp := by
      simp [Matrix.ofLp_toLpLin, Matrix.toLin'_apply, dotProduct_comm]

/-- The BFGS updated matrix remains positive definite under the usual curvature condition. -/
-- Proof sketch: rewrite `bfgsUpdatedMatrix` in the standard factorized BFGS form and apply the
-- classical preservation argument using `⟪γₖ, δₖ⟫ > 0` and positive definiteness of `Hₖ`.
theorem bfgsUpdatedMatrix_posDef (Hk : Mat) (γk δk : E) (hHkPosDef : Hk.PosDef)
    (hγδ : 0 < inner ℝ γk δk) :
    (bfgsUpdatedMatrix Hk γk δk).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · -- Positive definiteness over `ℝ` needs Hermitian symmetry, which is exactly matrix symmetry.
    simpa [Matrix.IsSymm, Matrix.IsHermitian] using
      bfgsUpdatedMatrix_isSymm Hk γk δk (by simpa using hHkPosDef.1)
  · intro x hx
    let y : E := WithLp.toLp 2 x
    have hy : y ≠ 0 := by
      dsimp [y]
      simpa using hx
    have hinner :
        0 < inner ℝ y ((bfgsUpdatedMatrix Hk γk δk).toEuclideanLin y) :=
      bfgsUpdatedMatrix_inner_pos Hk γk δk hHkPosDef hγδ hy
    -- Transport the Euclidean-space inequality back to the matrix quadratic form.
    calc
      0 < inner ℝ y ((bfgsUpdatedMatrix Hk γk δk).toEuclideanLin y) := hinner
      _ = x ⬝ᵥ (bfgsUpdatedMatrix Hk γk δk) *ᵥ x := by
        dsimp [y]
        change inner ℝ (WithLp.toLp 2 x)
          (WithLp.toLp 2 ((bfgsUpdatedMatrix Hk γk δk) *ᵥ x)) =
            x ⬝ᵥ (bfgsUpdatedMatrix Hk γk δk) *ᵥ x
        simpa [dotProduct_comm] using
          (EuclideanSpace.inner_toLp_toLp (x := x)
            (y := (bfgsUpdatedMatrix Hk γk δk) *ᵥ x))

/-- Helper for Definition 1.8.14: the scalar BFGS secant coefficient simplifies to `1` once the
curvature denominator is nonzero. -/
theorem bfgs_secant_scalar_cleanup {a c : ℝ} (hc : c ≠ 0) :
    c * (c⁻¹ * (1 + c⁻¹ * a)) - c⁻¹ * a = 1 := by
  -- Clear the denominator and normalize the remaining scalar polynomial identity.
  field_simp [hc]
  ring

/-- The BFGS updated matrix satisfies the quasi-Newton secant equation whenever the curvature
denominator is nonzero. -/
-- Proof sketch: write `Hₖ₊₁ = Hₖ + ΔHₖ`, apply the two rank-one terms in `ΔHₖ` to `γₖ`, and use
-- the nonvanishing curvature denominator `⟪γₖ, δₖ⟫` to cancel the old image `Hₖ γₖ`.
theorem bfgsUpdatedMatrix_secantEquation (Hk : Mat) (γk δk : E)
    (hγδ : inner ℝ γk δk ≠ 0) :
    (bfgsUpdatedMatrix Hk γk δk).toEuclideanLin γk = δk := by
  rw [bfgsUpdatedMatrix_toEuclideanLin]
  dsimp
  -- Expand the update on `γₖ`, then isolate the remaining scalar coefficient on `δₖ`.
  ext i
  have hc : inner ℝ δk γk ≠ 0 := by
    simpa [real_inner_comm] using hγδ
  have hInv : inner ℝ δk γk * (inner ℝ δk γk)⁻¹ = 1 := mul_inv_cancel₀ hc
  simp [inner_adjoint_apply_self_eq_inner_apply_self, sub_eq_add_neg, smul_smul, mul_comm]
  rw [real_inner_comm δk γk, hInv, real_inner_comm γk (Hk.toEuclideanLin γk)]
  have hCoeff := congrArg (fun t : ℝ ↦ δk.ofLp i * t)
    (bfgs_secant_scalar_cleanup (a := inner ℝ γk (Hk.toEuclideanLin γk))
      (c := inner ℝ δk γk) hc)
  ring_nf at hCoeff ⊢
  linarith

/-- Specializing the BFGS secant equation to consecutive iterates and gradients uses only the
curvature witness for that actual step data. -/
theorem bfgsUpdatedMatrix_step_secantEquation
    (xk xNext gk gNext : E) (Hk : Mat)
    (hcurvature : inner ℝ (gNext - gk) (xNext - xk) ≠ 0) :
    (bfgsUpdatedMatrix Hk (gNext - gk) (xNext - xk)).toEuclideanLin (gNext - gk) =
      xNext - xk := by
  simpa using
    bfgsUpdatedMatrix_secantEquation Hk (gNext - gk) (xNext - xk) hcurvature

end

/-! ### Definition_1_8_15 (from Chap01) -/
universe u

variable {E : Type u} [SeminormedAddCommGroup E]

/-
Definition 1.8.15 is source-facing: it records superlinear convergence of a trajectory family near
`xStar`.

Primary domain:
- trajectory-level superlinear convergence organized around genuine convergence
  `Filter.Tendsto (trajectory x0) Filter.atTop (nhds xStar)`
  together with the scalar recurrence owner
  `HasEventuallySuperlinearErrorBound`.

Relevant owner-style declarations sampled before refining:
- `HasEventuallySuperlinearErrorBound` from `Definition_1_2_7.lean`
- `gradient_descent_local_linear_rate` from `Theorem_1_6_15.lean`
- `LocalQuadraticNewtonConvergence` from `Theorem_5_0_5.lean`

Owner abstraction:
- for each admissible initial point `x0`, the trajectory itself tends to `xStar`, while its
  induced scalar error sequence `fun k ↦ ‖trajectory x0 k - xStar‖` carries an eventual
  superlinear bound `HasEventuallySuperlinearErrorBound ... lag c N`

Primitive data:
- the trajectory family `trajectory`
- the reference point `xStar`
- the lag `lag`

Derived API:
- the neighborhood constants `ε` and `c`
- convergence of `trajectory x0` to `xStar`
- equivalently, convergence of the induced scalar error sequence to `0`
- the eventual recurrence bound for the induced scalar error sequence

The previous version fixed the ambient space to the concrete display model `EuclideanSpace ℝ
(Fin dim)` even though the definition only uses the seminormed additive-group structure through
`‖trajectory x0 k - xStar‖` and the induced neighborhood filter of `xStar`. The owner layer is
therefore trajectory convergence plus the induced scalar recurrence, not a coordinate presentation
of the ambient space.
-/

/-- Definition 1.8.15: a trajectory family has a superlinear rate of convergence to `xStar` with
lag `lag` if there are positive constants `ε` and `c` such that every initial point `x₀` with
`‖x₀ - xStar‖ < ε` generates a trajectory starting at `x₀`, the induced error sequence
`‖x_k - xStar‖` is eventually controlled by the superlinear recurrence, while the trajectory
itself converges to `xStar`, and from some index `N ≥ lag`
onward, satisfying
`‖x_{k+1} - xStar‖ ≤ c * ‖x_k - xStar‖ * ‖x_{k-lag} - xStar‖`. -/
def HasSuperlinearRateOfConvergence
    (trajectory : E → ℕ → E)
    (xStar : E) (lag : ℕ) : Prop :=
  ∃ ε > 0, ∃ c > 0,
    ∀ ⦃x0 : E⦄, ‖x0 - xStar‖ < ε →
      trajectory x0 0 = x0 ∧
        Filter.Tendsto (trajectory x0) Filter.atTop (nhds xStar) ∧
        ∃ N,
          HasEventuallySuperlinearErrorBound
            (fun k ↦ ‖trajectory x0 k - xStar‖)
            lag c N
