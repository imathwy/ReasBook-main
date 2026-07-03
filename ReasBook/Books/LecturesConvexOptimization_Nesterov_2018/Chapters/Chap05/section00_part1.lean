import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_5_0_1 (from Chap05) -/
noncomputable section

variable {n m : ℕ}

/-
Definition 5.0.1 lies in the convex constrained minimization domain.

Sampled owner declarations:
- `LagrangianProblem` and `LagrangianProblem.feasibleSet` in `Chap01/Definition_1_10_2`, the
  project owner for the primitive objective-and-constraint data and its derived inequality
  feasible set;
- `GeneralConvexMinimizationProblem` and `GeneralConvexMinimizationProblem.ofReal` in
  `Chap03/Definition_3_1_1_1`, the chapter owner for ambient convex inequality-constrained
  minimization and the canonical real-valued whole-space bridge;
- `SmoothFunctionalConstraintsMinimizationProblem` in `Chap02/Definition_2_44`, the local project
  pattern of extending `LagrangianProblem` and adding only the extra regularity data specific to
  the refined source-facing notion.

Best owner abstraction:
- source-facing: `ConvexInequalityConstrainedMinimizationProblem n m`, the textbook whole-space
  real-valued specialization on `ℝⁿ`;
- core/canonical: `LagrangianProblem (EuclideanSpace ℝ (Fin n)) m` for the primitive functional
  data, together with `GeneralConvexMinimizationProblem (EuclideanSpace ℝ (Fin n)) m` for the
  convex-analysis owner;
- bridge/view: the inherited parent projection `toLagrangianProblem` and the Chapter 3 bridge
  `toGeneralConvexMinimizationProblem`.

Primitive data:
- the inherited real-valued objective and constraint family from `LagrangianProblem`;
- the whole-space convexity witnesses.

Derived API:
- the coercion to the objective function;
- the inherited `LagrangianProblem` feasible-set and feasibility API;
- the explicit Chapter 3 bridge `toGeneralConvexMinimizationProblem`.
-/

/-- Definition 5.0.1: a convex minimization problem with inequality constraints on `ℝⁿ`
consists of a real-valued objective function `f₀` and constraint functions `fⱼ`, `j = 1, …, m`,
all convex on the whole space, representing the problem of minimizing `f₀(x)` subject to the
inequalities `fⱼ(x) ≤ 0`. -/
structure ConvexInequalityConstrainedMinimizationProblem (n m : ℕ)
    extends LagrangianProblem (EuclideanSpace ℝ (Fin n)) m where
  /-- The objective is convex on all of `ℝⁿ`. -/
  objective_convex : ConvexOn ℝ Set.univ objective
  /-- Each constraint function is convex on all of `ℝⁿ`. -/
  constraints_convex (j : Fin m) : ConvexOn ℝ Set.univ (constraints j)

/-- A convex minimization problem with inequality constraints can be used as its objective
function. -/
instance :
    CoeFun (ConvexInequalityConstrainedMinimizationProblem n m)
      (fun _ ↦ EuclideanSpace ℝ (Fin n) → ℝ) where
  coe problem := problem.objective

namespace ConvexInequalityConstrainedMinimizationProblem

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The Chapter 3 owner view of a whole-space real-valued convex inequality problem. -/
def toGeneralConvexMinimizationProblem
    (problem : ConvexInequalityConstrainedMinimizationProblem n m) :
    GeneralConvexMinimizationProblem E m :=
  GeneralConvexMinimizationProblem.ofReal
    (SetConstrainedMinimizationProblem.unconstrained problem)
    problem.constraints isClosed_univ convex_univ
    problem.objective_convex problem.constraints_convex

@[simp] theorem toGeneralConvexMinimizationProblem_apply
    (problem : ConvexInequalityConstrainedMinimizationProblem n m) (x : E) :
    problem.toGeneralConvexMinimizationProblem x = problem x :=
  rfl

@[simp] theorem toGeneralConvexMinimizationProblem_feasibleSet
    (problem : ConvexInequalityConstrainedMinimizationProblem n m) :
    problem.toGeneralConvexMinimizationProblem.feasibleSet = Set.univ :=
  rfl

end ConvexInequalityConstrainedMinimizationProblem

end

/-! ### Definition_5_0_3 (from Chap05) -/
noncomputable section

universe u

open scoped Gradient
open FunctionalConstraintsMinimizationProblem

namespace SetConstrainedMinimizationProblem

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Definition 5.0.3 lies in the unconstrained twice-differentiable minimization domain on complete
real inner-product spaces.

Sampled owner declarations:
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner for the
  primitive feasible-set/objective data of an ambient real-valued minimization problem;
- `SetConstrainedMinimizationProblem.toFunctionalConstraintsMinimizationProblem` in
  `Chap01/Definition_1_3_3`, the canonical bridge from a set-constrained problem to the generic
  functional-constraint owner with zero scalar constraints;
- `FunctionalConstraintsMinimizationProblem.IsConstrained` and
  `FunctionalConstraintsMinimizationProblem.not_isConstrained_iff_feasibleSet_eq_univ` in
  `Chap01/Definition_1_1_4_1`, the generic owner predicate and whole-space bridge for
  constrainedness;
- `SetConstrainedMinimizationProblem.unconstrainedSmooth_iff` in `Chap01/Definition_1_4_3`, the
  earlier chapter pattern of keeping unconstrainedness on the owner surface and whole-space
  equalities as companion bridge API.

Best owner abstraction:
- source-facing/core:
  `¬ problem.toFunctionalConstraintsMinimizationProblem.IsConstrained ∧
    Differentiable ℝ problem.objective ∧
    Differentiable ℝ (∇ problem.objective)`;
- bridge/view:
  `problem.feasibleSet = Set.univ ∧
    Differentiable ℝ problem.objective ∧
    Differentiable ℝ (∇ problem.objective)`.

Primitive data:
- `problem.feasibleSet`
- `problem.objective`

Derived API:
- the generic-owner unconstrained-and-twice-differentiable expression above;
- the whole-space reformulation `twiceDifferentiableUnconstrained_iff`.

Source/core/bridge triage:
- source-facing: the unconstrained twice-differentiable minimization problem;
- core/canonical: `SetConstrainedMinimizationProblem E` together with the zero-constraint bridge
  owner `problem.toFunctionalConstraintsMinimizationProblem.IsConstrained` and the regularity
  layer `Differentiable ℝ problem.objective ∧ Differentiable ℝ (∇ problem.objective)`;
- bridge/view: the reformulation `problem.feasibleSet = Set.univ`.

Definition 5.0.3 does not need a Euclidean coordinate model: the source notion is intrinsic to the
ambient real Hilbert space. The public core therefore lives on `SetConstrainedMinimizationProblem
E`, while the whole-space formulation is kept only as a companion bridge theorem.
-/

variable (problem : SetConstrainedMinimizationProblem E)

/- Definition 5.0.3: an unconstrained twice-differentiable minimization problem is a
set-constrained minimization problem whose canonical zero-constraint owner is unconstrained and
whose objective is differentiable with differentiable gradient on the ambient space. -/
#check (
  ¬ problem.toFunctionalConstraintsMinimizationProblem.IsConstrained ∧
    Differentiable ℝ problem.objective ∧
    Differentiable ℝ (∇ problem.objective)
)

section

variable {problem : SetConstrainedMinimizationProblem E}

/-- The canonical owner expression for Definition 5.0.3 is equivalent to the textbook whole-space
twice-differentiability formulation. -/
theorem twiceDifferentiableUnconstrained_iff :
    (¬ problem.toFunctionalConstraintsMinimizationProblem.IsConstrained ∧
      Differentiable ℝ problem.objective ∧
      Differentiable ℝ (∇ problem.objective)) ↔
      problem.feasibleSet = Set.univ ∧
        Differentiable ℝ problem.objective ∧
        Differentiable ℝ (∇ problem.objective) := by
  have hiff :
      ¬ problem.toFunctionalConstraintsMinimizationProblem.IsConstrained ↔
        ((problem.toFunctionalConstraintsMinimizationProblem.feasibleSet : Set E) = Set.univ) :=
    not_isConstrained_iff_feasibleSet_eq_univ
  constructor
  · rintro ⟨hunconstrained, hdiff, hgradDiff⟩
    refine ⟨?_, hdiff, hgradDiff⟩
    simpa using hiff.mp hunconstrained
  · rintro ⟨hfeasible, hdiff, hgradDiff⟩
    refine ⟨?_, hdiff, hgradDiff⟩
    exact hiff.mpr <| by
      simpa using hfeasible

end

end SetConstrainedMinimizationProblem

end

/-! ### Theorem_5_0_5 (from Chap05) -/
open scoped Gradient

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Theorem 5.0.5 lies in the Chapter 1 local Newton-convergence domain specialized to `ℝⁿ`.

Source/core/bridge triage:
* source-facing: the Euclidean Newton theorem stated with the Hessian matrix lower bound
  `μ I ≤ ∇² f(xStar)`
* core/canonical: `localQuadraticNewtonOrbit` and
  `newtonOptimizationIterates_mem_ball_and_quadratic_error_bound`
* bridge/view: the Euclidean matrix-to-operator positivity bridge used to feed the Chapter 1
  owner theorem

Primary domain:
* local quadratic convergence of Newton's method for smooth unconstrained optimization on
  Euclidean space

Sampled owner-style declarations:
* `NewtonSystem.step`
* `NewtonSystem.orbit`
* `localQuadraticNewtonOrbit`
* `newtonOptimizationIterates_mem_ball_and_quadratic_error_bound`

Owner abstraction:
* the Chapter 1 local Newton orbit `localQuadraticNewtonOrbit` together with its owner theorem
  `newtonOptimizationIterates_mem_ball_and_quadratic_error_bound`

Primitive data:
* `f`, `xStar`, `x0`, `μ`, and `M`
* `f ∈ C22[M]`, `∇ f xStar = 0`, positivity of `μ`
* the Euclidean Hessian matrix lower bound
  `(∇² f xStar - μ • (1 : Mat)).PosSemidef`
* the initial closed-ball hypothesis `‖x0 - xStar‖ ≤ localQuadraticNewtonRadius μ M`

Derived API:
* the operator-positivity hypothesis required by the Chapter 1 owner theorem
* iteratewise Hessian nondegeneracy on the canonical operator owner `hessian`
* the closed-ball invariance and quadratic one-step error estimate for the canonical local
  Newton orbit

This file therefore keeps only the Euclidean/source-facing bridge and reuses the established
Chapter 1 Newton owner layer directly instead of rebuilding a parallel step/orbit package.
-/

private theorem hessianMatrix_lower_isPositive
    {f : E → ℝ} {x : E} {μ : ℝ}
    (h : (∇² f x - μ • (1 : Mat)).PosSemidef) :
    (hessian f x - μ • (1 : E →L[ℝ] E)).IsPositive := by
  have hpos :
      (∇² f x - μ • (1 : Mat)).toEuclideanLin.IsPositive :=
    Matrix.isPositive_toEuclideanLin_iff.mpr h
  have hsub :
      (∇² f x - μ • (1 : Mat)).toEuclideanLin =
        (∇² f x).toEuclideanLin - μ • (1 : E →L[ℝ] E) := by
    ext v i
    simp [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  rw [hsub] at hpos
  rw [hessianMatrix_toEuclideanLin] at hpos
  simpa [hessian] using hpos

/-- Theorem 5.0.5: if `f : ℝⁿ → ℝ` is twice continuously differentiable, `x*` is a critical
point, `∇² f(x*) - μ I` is positive semidefinite, and the Hessian is `M`-Lipschitz, then the
canonical local Newton orbit started in the closed ball of radius `2 μ / (3 M)` around `x*`
stays in that ball, has nonsingular Hessian at every iterate, and satisfies the standard
quadratic one-step error estimate. -/
theorem newton_method_has_local_quadratic_convergence
    (f : E → ℝ) (xStar x0 : E) {μ : ℝ} {M : NNRealˣ}
    (hf : f ∈ C22[M])
    (hcrit : ∇ f xStar = 0)
    (hμ : 0 < μ)
    (hessian_lower : (∇² f xStar - μ • (1 : Mat)).PosSemidef)
    (hx0 : ‖x0 - xStar‖ ≤ localQuadraticNewtonRadius μ M) :
    let traj :=
      localQuadraticNewtonOrbit hμ hf hcrit
        (hessianMatrix_lower_isPositive hessian_lower) hx0
    (∀ k, ‖traj k - xStar‖ ≤ localQuadraticNewtonRadius μ M) ∧
      (∀ k, (hessian f (traj k)).det ≠ 0) ∧
      ∀ k,
        ‖traj (k + 1) - xStar‖ ≤
          ((M : ℝ) * ‖traj k - xStar‖ ^ (2 : ℕ)) /
            (2 * (μ - (M : ℝ) * ‖traj k - xStar‖)) := by
  let hHstar : (hessian f xStar - μ • (1 : E →L[ℝ] E)).IsPositive :=
    hessianMatrix_lower_isPositive hessian_lower
  let traj := localQuadraticNewtonOrbit hμ hf hcrit hHstar hx0
  rcases
      newtonOptimizationIterates_mem_ball_and_quadratic_error_bound hμ hf hcrit hHstar hx0 with
    ⟨hball, hdet, hquad⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [traj] using hball
  · intro k
    simpa [traj, hessian] using hdet k
  · simpa [traj] using hquad

end

/-! ### Definition_5_0_6 (from Chap05) -/
noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Definition 5.0.6 is a recall-only item in the Euclidean linear-change-of-variables domain.

Layer targeted by this refinement:
- source-facing recall of the core/canonical pullback `f ∘ B.toEuclideanLin`

Primary domain:
- linear changes of variables on `ℝⁿ`, viewed as precomposition by the linear map
  attached to a matrix.

Sampled owner-style declarations:
- mathlib `Matrix.toEuclideanLin`
- mathlib `Matrix.toEuclideanLin_apply`
- mathlib `Matrix.toEuclideanCLM`
- mathlib `Matrix.coe_toEuclideanCLM_eq_toEuclideanLin`

Best owner abstraction:
- core/canonical: `f ∘ B.toEuclideanLin`

Primitive data:
- `f : E → ℝ`
- `B : Matrix (Fin n) (Fin n) ℝ`

Derived API:
- pointwise evaluation by `Function.comp_apply`
- the matrix-action bridge `Matrix.toEuclideanLin_apply`
- the bundled continuous-linear-map view by `Matrix.coe_toEuclideanCLM_eq_toEuclideanLin`

Source/core/bridge triage:
- source-facing: the textbook pullback under the substitution `x = By`
- core/canonical: precomposition with `B.toEuclideanLin`
- bridge/view: the bundled continuous-linear-map realization `B.toEuclideanCLM`

The previous local abbrev `linearChangeOfVariables` and theorem
`linearChangeOfVariables_apply` were exact-interface duplicates of this canonical composition. The
nonsingularity hypothesis is not primitive data for defining the pullback itself, so the refined
file removes that redundant wrapper and recalls the chapter's established owner surface directly. -/

section

recall Matrix.toEuclideanLin

variable (f : E → ℝ) (B : Matrix (Fin n) (Fin n) ℝ)

/- Definition 5.0.6: the pullback induced by `x = By` is exactly the canonical composition of `f`
with the chapter's owner linear map attached to `B`. -/
#check (f ∘ B.toEuclideanLin : E → ℝ)

end

/- The matrix-action bridge for the canonical pullback is the standard evaluation formula for
`Matrix.toEuclideanLin`. -/
recall Matrix.toEuclideanLin_apply

end

/-! ### Definition_5_0_7 (from Chap05) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Domain design notes:

Primary domain:
* functions with Lipschitz-continuous Hessian on a real Hilbert space

Sampled owner-style declarations:
* `HasLipschitzContinuousHessian` in `Chap04/Definition_4_2_7`
* `HasLipschitzContinuousHessian.contDiff`
* `HasLipschitzContinuousHessian.norm_sub_le`
* the theorem-surface notation `f ∈ C22[M]`

Source/core/bridge triage:
* source-facing: the textbook class `C_M^{2,2}(ℝⁿ)`
* core/canonical: `HasLipschitzContinuousHessian M f`
* bridge/view: the theorem-surface notation `f ∈ C22[M]`, the `C²` projection
  `HasLipschitzContinuousHessian.contDiff`, and the Hessian-difference estimate
  `HasLipschitzContinuousHessian.norm_sub_le`

Primitive data:
* none; this is a recall-only item

Derived API:
* the owner predicate `HasLipschitzContinuousHessian M f`
* the textbook notation `f ∈ C22[M]`
* the `C²` regularity projection
* the Hessian-difference estimate

This item therefore reuses the Chapter 4 owner directly instead of introducing a second local
wrapper. The textbook `ℝⁿ` statement is the specialization
`E = EuclideanSpace ℝ (Fin n)`. -/

section

variable {M : NNReal} {f : E → ℝ}

/- Definition 5.0.7: the textbook class `C_M^{2,2}(ℝⁿ)` is represented in this project by the
canonical owner `HasLipschitzContinuousHessian M f`, written on theorem surfaces as
`f ∈ C22[M]`. Its defining consequences are the inherited `C²` regularity and the displayed
Hessian Lipschitz estimate `‖∇² f(x) - ∇² f(y)‖ ≤ M ‖x - y‖`. -/
recall HasLipschitzContinuousHessian

set_option linter.hashCommand false in
#check (f ∈ C22[M])

recall HasLipschitzContinuousHessian.contDiff
recall HasLipschitzContinuousHessian.norm_sub_le

end

/-! ### Definition_5_0_8 (from Chap05) -/
open scoped Gradient

noncomputable section

/- Definition 5.0.8 lies in the finite-dimensional real Euclidean third-order differential
calculus domain.

Source/core/bridge triage:
* source-facing: the textbook matrix surface `f'''(x)[u]`
* core/canonical: the directional derivative operator `fderiv ℝ (hessian f) x u`
* bridge/view: its standard-basis matrix on `ℝⁿ`

Primary domain:
* third-order differential calculus for real-valued functions on finite-dimensional real
  inner-product spaces, with a Euclidean matrix bridge on `ℝⁿ`

Sampled owner-style declarations:
* `hessian` / `hessianMatrix` / `∇²` in `Chap01/Definition_1_4_16`
* `LinearMap.toMatrixOrthonormal`
* `LinearMap.toMatrixOrthonormal_apply_apply`
* `Matrix.toEuclideanLin_eq_toLin_orthonormal`

Best owner abstraction:
* the operator-valued directional derivative of the Hessian map, reused directly as
  `fderiv ℝ (hessian f) x u` from the chapter owner `hessian`

Primitive data:
* `f : E → ℝ`
* `x u : E`

Derived API:
* the intrinsic operator expression `fderiv ℝ (hessian f) x u`
* its standard-basis matrix surface on `ℝⁿ`

This refinement keeps `fderiv ℝ (hessian f) x u` as the owner and exposes the Euclidean matrix
surface only as a thin bridge abbreviation plus notation, matching the chapter style for `∇²`. -/

section EuclideanMatrix

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "e" => EuclideanSpace.basisFun (Fin n) ℝ

/-- Definition 5.0.8: the textbook matrix `f'''(x)[u]`, viewed as the standard-basis matrix of
the canonical operator `fderiv ℝ (hessian f) x u`. This is only a Euclidean matrix bridge; the
owner remains the operator `fderiv ℝ (hessian f) x u`. -/
abbrev thirdDerivativeMatrix (f : E → ℝ) (x u : E) : Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toMatrixOrthonormal e (fderiv ℝ (hessian f) x u)

@[inherit_doc thirdDerivativeMatrix]
scoped[Gradient] notation "∇³" => thirdDerivativeMatrix

-- Proof sketch: unfold `thirdDerivativeMatrix` and apply the entrywise formula for
-- `LinearMap.toMatrixOrthonormal` in the standard orthonormal basis.
/-- The `(i,j)` entry of the textbook matrix `∇³ f x u` is the inner product of the `i`th
standard basis vector with the Hessian-direction operator `fderiv ℝ (hessian f) x u` applied to
the `j`th standard basis vector. -/
theorem thirdDerivativeMatrix_apply (f : E → ℝ) (x u : E) (i j : Fin n) :
    ∇³ f x u i j = inner ℝ (e i) (fderiv ℝ (hessian f) x u (e j)) := by
  simpa [thirdDerivativeMatrix] using
    (LinearMap.toMatrixOrthonormal_apply_apply e (fderiv ℝ (hessian f) x u) i j)

-- Proof sketch: rewrite `∇³ f x u` as `LinearMap.toMatrixOrthonormal e (fderiv ℝ (hessian f) x
-- u)` and apply `Matrix.toEuclideanLin_eq_toLin_orthonormal`.
/-- Turning the Euclidean matrix `∇³ f x u` back into its linear action recovers the intrinsic
directional derivative operator of the Hessian. -/
theorem thirdDerivativeMatrix_toEuclideanLin (f : E → ℝ) (x u : E) :
    (∇³ f x u).toEuclideanLin = fderiv ℝ (hessian f) x u := by
  rw [thirdDerivativeMatrix, Matrix.toEuclideanLin_eq_toLin_orthonormal]
  simp

end EuclideanMatrix

/-! ### Definition_5_0_9 (from Chap05) -/
noncomputable section

open scoped Gradient
open scoped HessianLocalNorm

/- Definition 5.0.9 lies in the local Hessian norm domain.

Source/core/bridge triage:
* source-facing: the local norm induced by the Hessian quadratic form at a point
* core/canonical: `hessianLocalNorm`
* bridge/view: the owner-level source-facing notation `‖u‖[f; x]`

Sampled owner declarations:
* `hessian` in `Chap01/Definition_1_4_16`, the intrinsic Hessian operator owner
* `hessianLocalNorm` in `Chap05/Definition_5_1_1`, the chapter owner for the Hessian-induced
  local norm
* `hessianLocalNorm_def` in `Chap05/Definition_5_1_1`, the canonical expansion of that owner
* `LinearMap.BilinForm.primalSeminorm` together with the source-facing norm notation
  `‖x‖[B]` from `Chap04/Definition_4_2_6`, the chapter owner pattern for induced quadratic norms

Best owner abstraction:
* `hessianLocalNorm`

Primitive data:
* a function `f`
* a base point `x`
* a direction `u`

Derived API:
* the owner-level source-facing notation `‖u‖[f; x]`
* the Hessian quadratic form `inner ℝ u (hessian f x u)`
* the owner expansion theorem `hessianLocalNorm_def`

This item is therefore refined to direct reuse of the chapter owner `hessianLocalNorm` together
with its owner-level source-facing notation, rather than a second local norm owner, a local
notation copy, or a separate squared-norm wrapper theorem. -/

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 5.0.9 recalls the canonical Hessian local norm owner. -/
recall hessianLocalNorm

/-! ### Definition_5_0_10 (from Chap05) -/
open scoped Gradient

noncomputable section

universe u

/- Definition 5.0.10 lies in the chapter's directional differential-calculus domain.

Sampled owner declarations:
* mathlib `HasLineDerivAt`, the canonical owner for first directional derivatives along affine
  lines;
* mathlib `lineDeriv`, the totalized directional derivative operator corresponding to
  `t ↦ f (x + t • u)` at `t = 0`;
* mathlib `DifferentiableAt.lineDeriv_eq_fderiv` and `inner_gradient_left`, the primitive
  first-order bridge from directional derivatives to gradient pairings;
* `hessian` in `Chap01/Definition_1_4_16`, the chapter owner for the second Fréchet derivative of
  a real-valued function on a Hilbert space;
* `iteratedFDeriv`, the canonical multilinear owner for the third Fréchet derivative.

Source/core/bridge triage:
* source-facing: the directional slice `t ↦ f (x + t • u)` and its first, second, and third
  derivatives at `0`;
* core/canonical: `lineDeriv ℝ f x u` for the first derivative and `hessian f x` for the
  second-order quadratic form;
* bridge/view: the identification of the third directional derivative with
  `iteratedFDeriv ℝ 3 f x (fun _ ↦ u)` under `C³` regularity.

Primitive data:
* a function `f`;
* a base point `x`;
* a direction `u`.

Derived API:
* the source-facing slice `directionalSlice f x u`;
* the owner-level first directional derivative `lineDeriv ℝ f x u`;
* the Hessian quadratic form `inner ℝ u (hessian f x u)`;
* the Fréchet third-derivative bridge for smooth functions.

The slice itself remains source-facing, but the first- and second-order derived API should reuse
the canonical owners `lineDeriv` and `hessian` instead of repeating their raw formulas. -/

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Definition 5.0.10: the directional slice of `f` at `x` along `u` is the univariate function
`t ↦ f (x + t • u)`, from which the first, second, and third directional derivatives at `x` in
the direction `u` are taken at `t = 0`. -/
def directionalSlice (f : E → ℝ) (x u : E) : ℝ → ℝ :=
  fun t ↦ f (x + t • u)

/-- Evaluating the directional slice gives the textbook formula `φ(x; t) = f (x + t u)`. -/
@[simp] theorem directionalSlice_apply (f : E → ℝ) (x u : E) (t : ℝ) :
    directionalSlice f x u t = f (x + t • u) := rfl

/- The textbook first directional derivative at `x` along `u` is the canonical owner
`lineDeriv ℝ f x u`, i.e. the derivative at `0` of the slice `t ↦ f (x + t • u)`. -/
recall lineDeriv

/-- The second directional derivative is the second iterated derivative at `0` of the directional
slice. -/
def secondDirectionalDerivative (f : E → ℝ) (x u : E) : ℝ :=
  iteratedDeriv 2 (directionalSlice f x u) 0

/-- The third directional derivative is the third iterated derivative at `0` of the directional
slice. -/
def thirdDirectionalDerivative (f : E → ℝ) (x u : E) : ℝ :=
  iteratedDeriv 3 (directionalSlice f x u) 0

/-- The third directional derivative is odd in the direction argument. -/
@[simp] theorem thirdDirectionalDerivative_neg (f : E → ℝ) (x u : E) :
    thirdDirectionalDerivative f x (-u) = -thirdDirectionalDerivative f x u := by
  rw [thirdDirectionalDerivative]
  have hs : directionalSlice f x (-u) = fun t ↦ directionalSlice f x u (-t) := by
    funext t
    simp [directionalSlice]
  rw [hs]
  calc
    iteratedDeriv 3 (fun t ↦ directionalSlice f x u (-t)) 0
      = (-1 : ℝ) ^ (3 : ℕ) * iteratedDeriv 3 (directionalSlice f x u) 0 := by
          simpa [smul_eq_mul] using
            (iteratedDeriv_comp_neg 3 (directionalSlice f x u) 0)
    _ = -thirdDirectionalDerivative f x u := by
      norm_num [thirdDirectionalDerivative]

/-- For a `C³` function, the third directional derivative is the third Fréchet derivative of `f`
evaluated on the triple `(u, u, u)`. -/
-- Proof sketch: differentiate the slice three times and rewrite the result as evaluation of the
-- canonical trilinear map `iteratedFDeriv ℝ 3 f x` on the constant tuple `u`.
theorem thirdDirectionalDerivative_eq_iteratedFDeriv
    {f : E → ℝ} {x u : E} (hf : ContDiffAt ℝ 3 f x) :
    thirdDirectionalDerivative f x u = iteratedFDeriv ℝ 3 f x (fun _ ↦ u) := sorry

section Hilbert

variable [InnerProductSpace ℝ E] [CompleteSpace E]

/- Under differentiability, the textbook gradient pairing formula for the directional derivative is
the direct combination of the canonical bridge lemmas `DifferentiableAt.lineDeriv_eq_fderiv` and
`inner_gradient_left`. -/
recall DifferentiableAt.lineDeriv_eq_fderiv
recall inner_gradient_left

/-- If `f` is differentiable at `x` and its gradient is differentiable at `x`, then the second
directional derivative equals the Hessian quadratic form in the direction `u`. -/
-- Proof sketch: apply the chain rule twice to the directional slice and identify the derivative of
-- the gradient with the Hessian operator `fderiv ℝ (∇ f) x`.
theorem secondDirectionalDerivative_eq_hessian_quadratic_form
    {f : E → ℝ} {x u : E} (hf : DifferentiableAt ℝ f x)
    (hgrad : DifferentiableAt ℝ (∇ f) x) :
    secondDirectionalDerivative f x u = inner ℝ u (hessian f x u) := sorry

end Hilbert

end

/-! ### Definition_5_0_11 (from Chap05) -/
/- Definition 5.0.11 lies in the Hessian-induced local-norm domain.

Sampled owner declarations:
* `hessian` in `Chap01/Definition_1_4_16`, the intrinsic second-order owner;
* `secondDirectionalDerivative_eq_hessian_quadratic_form` in `Definition_5_0_10`, the bridge from
  directional differentiation to the Hessian quadratic form;
* `hessianLocalNorm` in `Definition_5_1_1`, the chapter owner for the local norm induced by the
  Hessian;
* `hessianLocalNorm_def`, the source-facing square-root expansion theorem.

Best owner abstraction:
* source-facing: the primal local norm of a direction at a point;
* core/canonical: `hessianLocalNorm f x h`;
* bridge/view: `hessianLocalNorm_def`.

Primitive data:
* a function `f`;
* a base point `x`;
* a direction `h`.

Derived API:
* the canonical local norm owner `hessianLocalNorm`;
* its source-facing notation `‖h‖[f; x]`;
* the square-root expansion theorem `hessianLocalNorm_def`.

This file therefore does not keep a parallel `primalLocalNorm` wrapper. The project already owns
the notion canonically as `hessianLocalNorm`, so Definition 5.0.11 is refined to a direct recall
of that owner and its defining expansion. -/

/- Definition 5.0.11 recalls the canonical Hessian local norm owner for the textbook primal local
norm. -/
recall hessianLocalNorm

/- The source-facing square-root formula is the owner expansion theorem. -/
recall hessianLocalNorm_def

/-! ### Definition_5_0_12 (from Chap05) -/
open scoped Gradient HessianLocalNorm

noncomputable section

universe u

/- Definition 5.0.12 lies in the self-concordant local-norm / directional-slice domain.

Sampled owner declarations:
* `hessianLocalNorm` in `Definition_5_1_1`, the chapter owner for the Hessian-induced local norm;
* the notation `‖u‖[f; x]`, the source-facing surface for that owner;
* `hessianLocalNorm_def`, the bridge from the owner to the square root of the Hessian quadratic
  form;
* `directionalSlice` in `Definition_5_0_10`, the chapter's source-facing owner for restricting a
  function to an affine line;
* `Set.restrict`, the canonical mathlib owner for viewing an ambient function on a subtype domain.

Source/core/bridge triage:
* source-facing: the associated univariate reciprocal local-norm function along the line
  `t ↦ x + t • h`;
* core/canonical: the Hessian local norm `‖h‖[f; x + t • h]`;
* bridge/view: the expansion of that local norm as
  `Real.sqrt (inner ℝ h ((fderiv ℝ (∇ f) (x + t • h)) h))`.

Primitive data:
* a domain `dom`;
* a function `f`;
* a base point `x`;
* a direction `h`.

Derived API:
* the natural parameter set where the shifted point stays in `dom` and the local norm is
  positive;
* the reciprocal local-norm function as the canonical restriction of the ambient slice
  `t ↦ 1 / ‖h‖[f; x + t • h]` to that parameter set;
* companion theorems expanding the owner-level statements to the textbook Hessian formula.

This file therefore keeps the associated univariate function as the source-facing owner, but it is
implemented by the canonical restriction owner `Set.restrict` rather than by a bespoke subtype
lambda. The core owner is the chapter local norm `hessianLocalNorm`, and the raw square-root
formula is kept only as bridge API.
-/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The natural parameter domain of the associated univariate function along the line
`t ↦ x + t • h`. -/
def associatedUnivariateFunctionDomain (dom : Set E) (f : E → ℝ) (x h : E) : Set ℝ :=
  {t | x + t • h ∈ dom ∧ 0 < ‖h‖[f; x + t • h]}

/-- Membership in `associatedUnivariateFunctionDomain dom f x h` means that the shifted point
`x + t • h` lies in `dom` and the Hessian local norm of `h` there is strictly positive. -/
theorem mem_associatedUnivariateFunctionDomain_iff
    (dom : Set E) (f : E → ℝ) (x h : E) (t : ℝ) :
    t ∈ associatedUnivariateFunctionDomain dom f x h ↔
      x + t • h ∈ dom ∧ 0 < ‖h‖[f; x + t • h] :=
  Iff.rfl

/-- Expanding membership in `associatedUnivariateFunctionDomain dom f x h` recovers the textbook
positivity condition on the Hessian quadratic form in the direction `h`. -/
theorem mem_associatedUnivariateFunctionDomain_iff_hessian
    (dom : Set E) (f : E → ℝ) (x h : E) (t : ℝ) :
    t ∈ associatedUnivariateFunctionDomain dom f x h ↔
      x + t • h ∈ dom ∧ 0 < inner ℝ h ((fderiv ℝ (∇ f) (x + t • h)) h) := by
  simp [mem_associatedUnivariateFunctionDomain_iff, hessianLocalNorm_def, hessian, Real.sqrt_pos]

/-- Definition 5.0.12: the associated univariate function is the reciprocal of the square root of
the Hessian quadratic form of `f` in the direction `h`, along the line `t ↦ x + t • h`, with
domain consisting of those `t` for which `x + t • h ∈ dom` and the quadratic form is positive. -/
def associatedUnivariateFunction (dom : Set E) (f : E → ℝ) (x h : E) :
    associatedUnivariateFunctionDomain dom f x h → ℝ :=
  (associatedUnivariateFunctionDomain dom f x h).restrict
    (directionalSlice (fun y ↦ 1 / ‖h‖[f; y]) x h)

/-- Evaluating the associated univariate function gives the reciprocal of the Hessian local norm
of `h` along the line `t ↦ x + t • h`. -/
@[simp] theorem associatedUnivariateFunction_apply
    (dom : Set E) (f : E → ℝ) (x h : E)
    (t : associatedUnivariateFunctionDomain dom f x h) :
    associatedUnivariateFunction dom f x h t = 1 / ‖h‖[f; x + (t : ℝ) • h] :=
  rfl

/-- Expanding `associatedUnivariateFunction dom f x h t` recovers the textbook formula
`1 / ⟨∇² f (x + t h) h, h⟩^(1/2)`. -/
theorem associatedUnivariateFunction_apply_eq_inv_sqrt_hessian
    (dom : Set E) (f : E → ℝ) (x h : E)
    (t : associatedUnivariateFunctionDomain dom f x h) :
    associatedUnivariateFunction dom f x h t =
      1 / Real.sqrt (inner ℝ h ((fderiv ℝ (∇ f) (x + (t : ℝ) • h)) h)) := by
  simp [associatedUnivariateFunction, hessianLocalNorm_def, hessian]

/-- If `x ∈ dom` and the Hessian quadratic form of `f` at `x` is positive along `h`, then `0`
belongs to the natural domain of the associated univariate function. -/
theorem zero_mem_associatedUnivariateFunctionDomain
    {dom : Set E} {f : E → ℝ} {x h : E}
    (hx : x ∈ dom)
    (hh : 0 < inner ℝ h ((fderiv ℝ (∇ f) x) h)) :
    (0 : ℝ) ∈ associatedUnivariateFunctionDomain dom f x h := by
  exact
    (mem_associatedUnivariateFunctionDomain_iff_hessian dom f x h 0).2
      ⟨by simpa, by simpa⟩

end

/-! ### Definition_5_0_13 (from Chap05) -/
open scoped Gradient HessianLocalNorm

noncomputable section

universe u

/- Definition 5.0.13 lies in the Hessian-local-norm / Dikin-ellipsoid domain.

 Sampled owner declarations:
* `hessianLocalNorm` in `Definition_5_1_1`, the chapter owner for the Hessian-induced local norm;
* the notation `‖u‖[f; x]`, the source-facing surface for that owner;
* `hessianLocalNorm_def`, the bridge back to the square-root Hessian quadratic form;
* the notational-owner precedent `W(G, v)` in `Definition_5_4_5_6`, showing that source-facing
  ellipsoid owners in this project should expose textbook notation on the theorem surface.

Best owner abstraction:
* source-facing: `openDikinEllipsoid f x r` and `dikinEllipsoid f x r`;
* core/canonical: `‖y - x‖[f; x]` for the local-norm quantity;
* bridge/view: the membership lemmas and `hessianLocalNorm_def`.

Primitive data:
* a function `f`;
* a center `x`;
* a radius `r`.

 Derived API:
* the open-ball owner `openDikinEllipsoid`;
* the closed-ball owner `dikinEllipsoid`;
* the textbook notations `W⁰[f; x](r)` and `W[f; x](r)`;
* membership lemmas stated first in local-norm form, then as raw square-root expansions, and
  finally in quadratic-form form under the Hessian-positivity regime.

This file owns the Dikin-ellipsoid layer directly rather than recalling it from a downstream
theorem file. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The open Dikin ellipsoid of `f` centered at `x` with radius `r` is the open ball in the
Hessian local norm at `x`. -/
def openDikinEllipsoid (f : E → ℝ) (x : E) (r : ℝ) : Set E :=
  {y | ‖y - x‖[f; x] < r}

/-- Definition 5.0.13: the Dikin ellipsoid of `f` at `x` with radius `r` is the closed ball in
the Hessian local norm at `x`. -/
def dikinEllipsoid (f : E → ℝ) (x : E) (r : ℝ) : Set E :=
  {y | ‖y - x‖[f; x] ≤ r}

namespace DikinEllipsoidNotation

/-- Textbook notation for the open Dikin ellipsoid centered at `x` with radius `r` for the
ambient objective `f`. -/
scoped notation:max "W⁰[" f "; " x "](" r ")" => openDikinEllipsoid f x r

/-- Textbook notation for the closed Dikin ellipsoid centered at `x` with radius `r` for the
ambient objective `f`. -/
scoped notation:max "W[" f "; " x "](" r ")" => dikinEllipsoid f x r

end DikinEllipsoidNotation

open scoped DikinEllipsoidNotation

/-- Membership in `W⁰[f; x](r)` is exactly the strict local-norm inequality
`‖y - x‖[f; x] < r`. -/
@[simp] theorem mem_openDikinEllipsoid_iff
    (f : E → ℝ) (x y : E) (r : ℝ) :
    y ∈ W⁰[f; x](r) ↔ ‖y - x‖[f; x] < r :=
  Iff.rfl

/-- Expanding membership in `W⁰[f; x](r)` gives the square root of the Hessian quadratic form.
The quadratic-form reformulation below is the source-facing ellipsoid API in the Hessian-positive
regime. -/
theorem mem_openDikinEllipsoid_iff_sqrt_hessian
    (f : E → ℝ) (x y : E) (r : ℝ) :
    y ∈ W⁰[f; x](r) ↔
      Real.sqrt (inner ℝ (y - x) (hessian f x (y - x))) < r := by
  simp [openDikinEllipsoid, hessianLocalNorm_def]

/-- In the Hessian-positive regime and for a nonnegative radius, membership in `W⁰[f; x](r)` is
equivalent to the strict quadratic bound `⟪∇² f(x) (y - x), y - x⟫ < r²`. -/
theorem mem_openDikinEllipsoid_iff_hessian_quadratic_lt_sq
    (f : E → ℝ) (x y : E) {r : ℝ}
    (hquad_nonneg : 0 ≤ inner ℝ (y - x) (hessian f x (y - x))) (hr : 0 ≤ r) :
    y ∈ W⁰[f; x](r) ↔
      inner ℝ (y - x) (hessian f x (y - x)) < r ^ (2 : ℕ) := by
  rw [mem_openDikinEllipsoid_iff_sqrt_hessian]
  simpa using (Real.sqrt_lt hquad_nonneg hr)

/-- Membership in `W[f; x](r)` is exactly the closed local-norm inequality
`‖y - x‖[f; x] ≤ r`. -/
@[simp] theorem mem_dikinEllipsoid_iff
    (f : E → ℝ) (x y : E) (r : ℝ) :
    y ∈ W[f; x](r) ↔ ‖y - x‖[f; x] ≤ r :=
  Iff.rfl

/-- Expanding membership in `W[f; x](r)` gives the square root of the Hessian quadratic form.
The quadratic-form reformulation below is the source-facing ellipsoid API in the Hessian-positive
regime. -/
theorem mem_dikinEllipsoid_iff_sqrt_hessian
    (f : E → ℝ) (x y : E) (r : ℝ) :
    y ∈ W[f; x](r) ↔
      Real.sqrt (inner ℝ (y - x) (hessian f x (y - x))) ≤ r := by
  simp [dikinEllipsoid, hessianLocalNorm_def]

/-- For a nonnegative radius, membership in `W[f; x](r)` is equivalent to the quadratic bound
`⟪∇² f(x) (y - x), y - x⟫ ≤ r²`. The nonnegativity of the quadratic form is supplied
automatically by `Real.sqrt`. -/
theorem mem_dikinEllipsoid_iff_hessian_quadratic_le_sq
    (f : E → ℝ) (x y : E) {r : ℝ} (hr : 0 ≤ r) :
    y ∈ W[f; x](r) ↔
      inner ℝ (y - x) (hessian f x (y - x)) ≤ r ^ (2 : ℕ) := by
  rw [mem_dikinEllipsoid_iff_sqrt_hessian]
  constructor
  · intro hy
    exact (Real.sqrt_le_iff.mp (by simpa using hy)).2
  · intro hy
    exact (Real.sqrt_le_iff.mpr ⟨hr, by simpa using hy⟩)

end

/-! ### Definition_5_0_14 (from Chap05) -/
universe u

open scoped DikinEllipsoidNotation

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 5.0.14 lies in the Hessian-local-norm / Dikin-ellipsoid domain.

Sampled owner declarations:
* `hessianLocalNorm` in `Definition_5_1_1`, the chapter owner for the Hessian local norm;
* `hessianLocalNorm_def` in `Definition_5_1_1`, the canonical owner expansion;
* `openDikinEllipsoid` and the notation `W⁰[f; x](r)` in `Definition_5_0_13`, the chapter owner
  for the Dikin-radius neighborhood;
* `mem_openDikinEllipsoid_iff_hessian_quadratic_lt_sq` in `Definition_5_0_13`, the owner-level
  quadratic membership bridge.

Source/core/bridge triage:
* source-facing: the textbook radius-`1 / M_f` open Dikin neighborhood condition;
* core/canonical: `openDikinEllipsoid f x r`;
* bridge/view: the specialized quadratic membership theorem below.

Primitive data:
* a function `f`;
* a center `x`;
* a self-concordance parameter `Mf`;
* a point `y`.

Derived API:
* the special radius `r = 1 / M_f`;
* the source-facing Dikin neighborhood `W⁰[f; x](1 / (Mf : ℝ))`;
* the corresponding quadratic inequality `⟪∇² f(x) (y - x), y - x⟫ < 1 / M_f^2`.

This item stays source-facing by specializing the chapter owner `openDikinEllipsoid` to the
textbook radius `1 / M_f`, while keeping the generic Dikin-ellipsoid owner in
`Definition_5_0_13`. -/

variable (f : E → ℝ) (x : E) (Mf : NNReal)

/- Definition 5.0.14 specializes the chapter owner to the textbook inverse-parameter Dikin
neighborhood `W⁰[f; x](1 / M_f)`. -/
#check W⁰[f; x](1 / (Mf : ℝ))

variable {f x Mf}

/-- Membership in the textbook inverse-parameter Dikin neighborhood is equivalent to the strict
inverse-square Hessian quadratic bound. -/
theorem mem_openDikinEllipsoid_inv_constant_iff_hessian_quadratic_lt_inv_sq
    (f : E → ℝ) (x y : E) (Mf : NNReal)
    (hquad_nonneg : 0 ≤ inner ℝ (y - x) (hessian f x (y - x))) :
    y ∈ W⁰[f; x](1 / (Mf : ℝ)) ↔
      inner ℝ (y - x) (hessian f x (y - x)) < 1 / (Mf : ℝ) ^ (2 : ℕ) := by
  simpa [one_div] using
    (mem_openDikinEllipsoid_iff_hessian_quadratic_lt_sq
      f x y hquad_nonneg (by positivity : 0 ≤ 1 / (Mf : ℝ)))

/-! ### Proposition_5_0_15 (from Chap05) -/
open scoped DikinEllipsoidNotation Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace IsSelfConcordantOnWith

/- Proposition 5.0.15 lies in the Chapter 5 self-concordance / Hessian-comparison domain.

Sampled owner declarations:
* `IsSelfConcordantOnWith` in `Definition_5_1_1`, the quantitative source-facing owner for
  self-concordance on a domain;
* `hessian` in `Chap01/Definition_1_4_16`, the canonical second-order operator owner;
* `hessianLocalNorm` and the notation `‖u‖[f; x]` in `Definition_5_1_1`, the chapter owner for
  the local Hessian norm;
* `openDikinEllipsoid` together with the notation `W⁰[f; x](r)` in `Definition_5_0_13`, the
  source-facing owner for the Dikin-radius hypothesis.

Source/core/bridge triage:
* source-facing: the pointwise Hessian comparison between `x` and `y` under the textbook
  open-Dikin hypothesis;
* core/canonical: `IsSelfConcordantOnWith dom Mf f`, `hessian f z`, and `W⁰[f; x](r)`;
* bridge/view: the local-norm inequality encoded by membership in `W⁰[f; x](r)`.

Primitive data:
* a domain `dom`, a self-concordance constant `Mf`, and a function `f`;
* points `x y : E` and a radius `r`;
* the owner hypothesis `hself : IsSelfConcordantOnWith dom Mf f`;
* the source-facing inputs `hx : x ∈ dom`, `hr : r < 1 / (Mf : ℝ)`, and
  `hxy : y ∈ W⁰[f; x](r)`.

Derived API:
* the lower and upper Loewner-order bounds comparing `hessian f x` and `hessian f y`.

The theorem should therefore stay directly on the bundled self-concordance owner and the canonical
Hessian owner, rather than reintroducing scalarized quadratic-form wrappers as primitive public
data. -/

-- Proof sketch: for a fixed direction `v`, apply the one-dimensional self-concordance estimate
-- along the segment from `x` to `y` to the univariate function obtained by restricting the
-- Hessian quadratic form in the direction `v`. The Dikin-radius bound
-- `hessianLocalNorm f x (y - x) < r < 1 / M_f` then yields the factor `(1 - M_f r)^2` and its
-- reciprocal uniformly in `v`, which is exactly the Loewner-order comparison of the intrinsic
-- Hessian operators at `x` and `y`. The hypotheses `y ∈ dom`, `0 ≤ r`, and `0 < M_f` are
-- redundant here: `hxy` together with `hr` already forces `r > 0`, and the Chapter 5 Dikin-ball
-- inclusion theorem then recovers `y ∈ dom`.
/-- Proposition 5.0.15: if `f` is self-concordant on `dom` with parameter `M_f`, `x ∈ dom`,
`r < 1 / M_f`, and `y ∈ W⁰[f; x](r)`, then the Hessians at `x` and `y` are comparable in
Loewner order by the factors `(1 - M_f r)^2` and `(1 - M_f r)⁻²`. The statement is expressed
with the canonical Hessian owner `hessian f`. -/
theorem hessian_loewner_bounds_of_mem_openDikinEllipsoid
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    (hself : IsSelfConcordantOnWith dom Mf f)
    {x y : E} {r : ℝ} (hx : x ∈ dom) (hr : r < 1 / (Mf : ℝ))
    (hxy : y ∈ W⁰[f; x](r)) :
    ((1 - (Mf : ℝ) * r) ^ (2 : ℕ)) • hessian f x ≤ hessian f y ∧
      hessian f y ≤ ((1 - (Mf : ℝ) * r) ^ (2 : ℕ))⁻¹ • hessian f x := sorry

end IsSelfConcordantOnWith

end

/-! ### Definition_5_0_16 (from Chap05) -/
open scoped WithTopConvexAnalysis

universe u

/- Definition 5.0.16 lies in the chapter's `WithTop`-valued convex-analysis domain.

Sampled owner-style declarations:
- `withTopEffectiveDomain` / `dom` in `Chap03/Definition_3_3`, the chapter owner for the
  effective domain of a `WithTop ℝ`-valued function;
- `withTopRealPart` in `Chap03/Definition_3_3`, the canonical finite real representative on that
  domain;
- the direct chapter recall `#check ConvexOn ℝ (dom f) (withTopRealPart f)` in
  `Chap03/Definition_3_3`;
- mathlib `ConvexOn`, the core owner for convexity on a set.

Best owner abstraction:
- `ConvexOn ℝ (dom f) (withTopRealPart f)`.

Primitive data:
- the function `f : X → WithTop ℝ`.

Derived API:
- convexity of `dom f`;
- the Jensen inequality on `dom f` specialized to coefficients `1 - t` and `t`.

Source/core/bridge triage:
- source-facing: Definition 5.0.16, the convexity notion for `ℝ ∪ {+∞}`-valued functions;
- core/canonical: `ConvexOn ℝ (dom f) (withTopRealPart f)`;
- bridge/view: the domain-convexity and Jensen-inequality consequence lemmas below.

This file uses the Chapter 3 owner directly for its main entry: the exact effective-domain and
finite-real-part surface already exists upstream, so the previous Chapter 5 duplicate wrappers are
deleted instead of being preserved under parallel names. -/

section

variable {X : Type u} [AddCommMonoid X] [Module ℝ X]
variable (f : X → WithTop ℝ)

/- Definition 5.0.16 uses the canonical Chapter 3 specialization of `ConvexOn` to define
convexity for `ℝ ∪ {+∞}`-valued functions. -/
set_option linter.hashCommand false in
#check ConvexOn ℝ (dom f) (withTopRealPart f)

end

section

variable {X : Type u} [AddCommMonoid X] [Module ℝ X]

/-- A convex `ℝ ∪ {+∞}`-valued function has convex effective domain. -/
-- Proof sketch: `ConvexOn` is defined as convexity of the domain together with the Jensen
-- inequality, so the domain-convexity claim is exactly the first projection of `hf`.
theorem convex_effectiveDomain
    {f : X → WithTop ℝ} (hf : ConvexOn ℝ (dom f) (withTopRealPart f)) :
    Convex ℝ (dom f) :=
  hf.1

/-- For a convex `ℝ ∪ {+∞}`-valued function, the convexity inequality holds on its effective
domain. -/
-- Proof sketch: apply the Jensen-inequality field `hf.2` of `ConvexOn`; the interval hypothesis
-- gives `0 ≤ 1 - t` and `0 ≤ t`, and `sub_add_cancel 1 t` supplies the coefficient sum.
theorem withTopRealPart_combo_le
    {f : X → WithTop ℝ} (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    {x y : X} (hx : x ∈ dom f) (hy : y ∈ dom f)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    withTopRealPart f ((1 - t) • x + t • y) ≤
      (1 - t) * withTopRealPart f x + t * withTopRealPart f y :=
  hf.2 hx hy (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)

end

/-! ### Proposition_5_0_17 (from Chap05) -/
open scoped Gradient HessianLocalNorm SelfConcordantAuxiliaryFunction

noncomputable section

universe u

/- Proposition 5.0.17 lies in the Chapter 5 lower-remainder / self-concordance domain.

Sampled owner declarations in this domain:
* `thirdDirectionalDerivative` and `directionalSlice` from `Definition_5_0_10`, the chapter
  source-facing cubic-directional owner and its affine-line restriction;
* mathlib `iteratedDerivWithin`, the canonical one-variable owner for the auxiliary one-sided
  reverse-slice derivative on `Set.Ici (0 : ℝ)`;
* `hessianLocalNorm` and the notation `‖u‖[f; x]` from `Definition_5_1_1`, the chapter owner
  for the local Hessian norm;
* `taylor_lower_bound_of_hessian_loewner_lower` from `Theorem_5_1_8`, the nearby owner-level
  lower-remainder theorem already stated on genuine interior data.

Source/core/bridge triage:
* source-facing: the cubic bound on `thirdDirectionalDerivative f x u` at points `x ∈ dom`;
* core/canonical: the chapter owners `thirdDirectionalDerivative f x u` and `‖u‖[f; x]`;
* bridge/view: the one-sided reverse-slice derivative
  `iteratedDerivWithin 3 (directionalSlice f x (-u)) (Set.Ici (0 : ℝ)) 0`.

Primitive data:
* an open domain `dom` and a `C³` function on `dom`;
* a positive self-concordance parameter `Mf`;
* the global lower remainder inequality with the source-facing `ω` term.

Derived API:
* the auxiliary one-sided reverse-slice cubic bound along a reverse ray inside `dom`;
* the source-facing cubic estimate for `thirdDirectionalDerivative`;
* its absolute-value companion and the resulting owner-level bridge to
  `IsSelfConcordantOnWith`.

The public proposition must therefore live on `thirdDirectionalDerivative`, with the reverse-slice
within-derivative kept only as a private bridge used to encode the one-sided proof route. The
parameter must also be positive: when `Mf = 0`, the nearby Chapter 5 remainder API switches to
the quadratic remainder `r² / 2`, so the cubic conclusion below is false. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Auxiliary bridge: the one-sided third derivative at the origin of the reverse directional slice
`α ↦ f (x - α • u)` agrees with the negative of `thirdDirectionalDerivative f x u` when `f` is
genuinely `C³` at `x`. -/
-- Proof sketch: apply the one-variable chain rule three times to the map
-- `α ↦ f (x - α • u)`. Each differentiation contributes a factor `-1`, so the third derivative
-- picks up the sign `(-1)^3 = -1`, and `iteratedDerivWithin` on `Set.Ici (0 : ℝ)` agrees with the
-- unrestricted derivative at `0` because `f` is `C³` there.
private theorem reverse_directionalSlice_thirdDerivWithin_eq_neg
    {f : E → ℝ} {x u : E} (hf : ContDiffAt ℝ 3 f x) :
    iteratedDerivWithin 3 (directionalSlice f x (-u)) (Set.Ici (0 : ℝ)) 0 =
      -thirdDirectionalDerivative f x u := sorry

/- Private reverse-slice bound used to prove Proposition 5.0.17: if the lower Taylor remainder
bound holds at the base point `x`, with positive parameter `M_f`, and the reverse ray from `x` in
direction `u` stays in `dom` near `0`, then the negative one-sided third derivative of
`α ↦ f (x - α • u)` at `0` is bounded above by `2 M_f ‖u‖_x^3`. -/
private theorem reverse_directionalSlice_thirdDerivWithin_bound_of_remainder_lower_bound
    {dom : Set E} {Mf : NNReal} {f : E → ℝ} {x u : E}
    (hf : ContDiffAt ℝ 3 f x)
    (hMf : 0 < Mf)
    (hremainder :
      ∀ ⦃y : E⦄, y ∈ dom →
        (1 / (Mf : ℝ) ^ (2 : ℕ)) *
            ω (selfConcordantOmegaArg Mf ‖y - x‖[f; x]
              (neg_one_lt_mf_mul_of_nonneg
                (hessianLocalNorm_nonneg f x (y - x)))) ≤
          f y - f x - inner ℝ (∇ f x) (y - x))
    (hline : ∃ ε > 0, Set.Icc (0 : ℝ) ε ⊆ (fun α : ℝ ↦ x - α • u) ⁻¹' dom) :
    -iteratedDerivWithin 3 (directionalSlice f x (-u)) (Set.Ici (0 : ℝ)) 0 ≤
      2 * (Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ) := sorry

-- Proof sketch: openness of `dom` upgrades `ContDiffOn ℝ 3 f dom` to `ContDiffAt ℝ 3 f x`,
-- and provides a small two-sided ball around `x` inside `dom`; restricting that ball to the
-- reverse ray gives the private reverse-slice bound above. Rewriting the resulting one-sided
-- derivative by `reverse_directionalSlice_thirdDerivWithin_eq_neg` recovers the source-facing
-- cubic estimate on `thirdDirectionalDerivative f x u`.
/-- Proposition 5.0.17: if the global lower Taylor remainder bound from
`Theorem_5_1_8.taylor_lower_bound_of_hessian_loewner_lower` holds on an open domain `dom` for a
`C³` function `f`, with positive parameter `M_f`, then at every point `x ∈ dom` the chapter owner
`thirdDirectionalDerivative f x u` is bounded above by
`2 M_f ‖u‖_x^3`. -/
theorem thirdDirectionalDerivative_le_of_global_remainder_lower_bound
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    (hopen : IsOpen dom)
    (hcont : ContDiffOn ℝ 3 f dom)
    (hMf : 0 < Mf)
    (hremainder :
      ∀ ⦃x y : E⦄ (_ : x ∈ dom) (_ : y ∈ dom),
        (1 / (Mf : ℝ) ^ (2 : ℕ)) *
            ω (selfConcordantOmegaArg Mf ‖y - x‖[f; x]
              (neg_one_lt_mf_mul_of_nonneg
                (hessianLocalNorm_nonneg f x (y - x)))) ≤
          f y - f x - inner ℝ (∇ f x) (y - x))
    (x u : E) (hx : x ∈ dom) :
    thirdDirectionalDerivative f x u ≤
      2 * (Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ) := sorry

/-- Under the same hypotheses as Proposition 5.0.17, the third directional derivative is bounded
in absolute value by `2 M_f ‖u‖_x^3`. This is the exact cubic field used by the chapter owner
`IsSelfConcordantOnWith`. -/
theorem thirdDirectionalDerivative_abs_le_of_global_remainder_lower_bound
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    (hopen : IsOpen dom)
    (hcont : ContDiffOn ℝ 3 f dom)
    (hMf : 0 < Mf)
    (hremainder :
      ∀ ⦃x y : E⦄ (_ : x ∈ dom) (_ : y ∈ dom),
        (1 / (Mf : ℝ) ^ (2 : ℕ)) *
            ω (selfConcordantOmegaArg Mf ‖y - x‖[f; x]
              (neg_one_lt_mf_mul_of_nonneg
                (hessianLocalNorm_nonneg f x (y - x)))) ≤
          f y - f x - inner ℝ (∇ f x) (y - x))
    (x u : E) (hx : x ∈ dom) :
    |thirdDirectionalDerivative f x u| ≤
      2 * (Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ) := by
  have hupper :
      thirdDirectionalDerivative f x u ≤
        2 * (Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ) :=
    thirdDirectionalDerivative_le_of_global_remainder_lower_bound
      hopen hcont hMf hremainder x u hx
  have hneg :
      -thirdDirectionalDerivative f x u ≤
        2 * (Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ) := by
    simpa using
      (thirdDirectionalDerivative_le_of_global_remainder_lower_bound
        hopen hcont hMf hremainder x (-u) hx)
  rw [abs_le]
  constructor
  · linarith
  · exact hupper

namespace IsSelfConcordantOnWith

/-- If the global lower Taylor remainder bound from
`Theorem_5_1_8.taylor_lower_bound_of_hessian_loewner_lower` holds on an open domain with convex
underlying set for a `C³` function with positive parameter `M_f`, then the function is
self-concordant on that domain with constant `M_f`. This is the canonical owner-level bridge from
Proposition 5.0.17 to `IsSelfConcordantOnWith`. -/
theorem of_global_remainder_lower_bound
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    (hopen : IsOpen dom)
    (hcont : ContDiffOn ℝ 3 f dom)
    (hdom : Convex ℝ dom)
    (hMf : 0 < Mf)
    (hremainder :
      ∀ ⦃x y : E⦄ (_ : x ∈ dom) (_ : y ∈ dom),
        (1 / (Mf : ℝ) ^ (2 : ℕ)) *
            ω (selfConcordantOmegaArg Mf ‖y - x‖[f; x]
              (neg_one_lt_mf_mul_of_nonneg
                (hessianLocalNorm_nonneg f x (y - x)))) ≤
          f y - f x - inner ℝ (∇ f x) (y - x)) :
    IsSelfConcordantOnWith dom Mf f where
  isOpen_domain := hopen
  contDiffOn := hcont
  convexOn := by
    have hcont₁ : ContDiffOn ℝ 1 f dom := hcont.of_le (by norm_num)
    refine (convexOn_iff_lower_tangent_plane_of_contDiffOn hdom hcont₁).2 ?_
    intro x hx y hy
    have hMf' : 0 < (Mf : ℝ) := by
      exact_mod_cast hMf
    have hgrad :
        gradientWithin f dom x = ∇ f x := by
      rw [gradientWithin, gradient]
      congr
      exact fderivWithin_eq_fderiv (hopen.uniqueDiffWithinAt hx)
        ((hcont₁.contDiffAt (hopen.mem_nhds hx)).differentiableAt_one)
    have homega_nonneg :
        0 ≤ ω (selfConcordantOmegaArg Mf ‖y - x‖[f; x]
          (neg_one_lt_mf_mul_of_nonneg
            (hessianLocalNorm_nonneg f x (y - x)))) := by
      rw [selfConcordantOmega_apply, coe_selfConcordantOmegaArg]
      have harg_nonneg : 0 ≤ (Mf : ℝ) * ‖y - x‖[f; x] := by
        exact mul_nonneg hMf'.le (hessianLocalNorm_nonneg f x (y - x))
      have hlog :
          Real.log (1 + (Mf : ℝ) * ‖y - x‖[f; x]) ≤
            (Mf : ℝ) * ‖y - x‖[f; x] := by
        have hpos : 0 < 1 + (Mf : ℝ) * ‖y - x‖[f; x] := by positivity
        simpa using Real.log_le_sub_one_of_pos hpos
      linarith
    have hgap_nonneg :
        0 ≤ f y - f x - inner ℝ (∇ f x) (y - x) := by
      have hcoeff_nonneg : 0 ≤ 1 / (Mf : ℝ) ^ (2 : ℕ) := by positivity
      exact le_trans (mul_nonneg hcoeff_nonneg homega_nonneg) (hremainder hx hy)
    have hlower :
        f y ≥ f x + inner ℝ (∇ f x) (y - x) := by
      linarith
    simpa [hgrad] using hlower
  third_deriv_bound := fun {x} hx u ↦
    thirdDirectionalDerivative_abs_le_of_global_remainder_lower_bound
      hopen hcont hMf hremainder x u hx

end IsSelfConcordantOnWith

end

/-! ### Definition_5_0_18 (from Chap05) -/
noncomputable section

universe u v w

open scoped ConvexAnalysis

variable {E₁ : Type u} {E₂ : Type v}

/- Definition 5.0.18 lies in the chapter's partial-minimization / infimal-projection domain.

Primary domain:
* fiberwise infima of a partial objective `Φ : E₁ × E₂ → ℝ` over a feasible set
  `domΦ ⊆ E₁ × E₂`

Sampled owner-style declarations:
* chapter `partialInfProjection` in `Chap03/Theorem_3_1_2_3`, the canonical owner of constrained
  fiberwise infima with `EReal` values
* chapter `partialInfProjection_eq_sInf` in `Chap03/Theorem_3_1_2_3`, the owner specification
  theorem on the fiber in `E₁ × E₂`
* chapter `extendedRealRealPart` in `Chap03/Definition_3_1_1_3`, the finite-value bridge from
  `EReal` to `ℝ`
* chapter `extendedRealRealPart_partialInfProjection_eq_sInf` in
  `Chap03/Theorem_3_1_2_3`, the finite-real-part bridge for the fiberwise infimum

Best owner abstraction:
* core/canonical: `partialInfProjection domΦ (Real.toEReal ∘ Φ)`
* source-facing: its finite real part `extendedRealRealPart` on
  `dom (partialInfProjection domΦ (Real.toEReal ∘ Φ))`
* bridge/view: the `y`-fiber reformulation
  `extendedRealRealPart_partialInfProjection_eq_sInf_image`

Primitive data:
* the feasible relation `domΦ : Set (E₁ × E₂)`
* the real-valued partial objective `Φ : E₁ × E₂ → ℝ`

Derived API:
* the canonical Chapter 3 infimal projection
* its finite-value domain `dom (partialInfProjection domΦ (Real.toEReal ∘ Φ))`
* the real-surface bridge theorem below

Source/core/bridge triage:
* source-facing: the finite real value of the partial-minimization problem at a base point `x`
* core/canonical: `partialInfProjection domΦ (Real.toEReal ∘ Φ)`
* bridge/view: `extendedRealRealPart_partialInfProjection_eq_sInf_image`

This file therefore introduces no parallel public `valueFunction` owner. The partial value
function is the Chapter 3 owner `partialInfProjection`, and the textbook real-valued surface is
obtained only on its finite-value domain via `extendedRealRealPart`.
-/

section

variable (domΦ : Set (E₁ × E₂)) (Φ : E₁ × E₂ → ℝ) (x : E₁)

/- Definition 5.0.18: the partial-minimization value function is the canonical Chapter 3
infimal-projection owner `partialInfProjection domΦ (Real.toEReal ∘ Φ)`, with real values
recovered on its finite-value domain by `extendedRealRealPart`. -/
recall partialInfProjection
recall extendedRealRealPart
recall extendedRealRealPart_partialInfProjection_eq_sInf

set_option linter.hashCommand false in
#check (dom (partialInfProjection domΦ (Real.toEReal ∘ Φ)) : Set E₁)

set_option linter.hashCommand false in
#check (extendedRealRealPart (partialInfProjection domΦ (Real.toEReal ∘ Φ)) : E₁ → ℝ)

end

private theorem pairFiber_image_eq_secondFiber_image
    {α : Type w} (domΦ : Set (E₁ × E₂)) (Φ : E₁ × E₂ → α) (x : E₁) :
    Φ '' {z : E₁ × E₂ | z ∈ domΦ ∧ z.1 = x} =
      (fun y : E₂ ↦ Φ (x, y)) '' {y | (x, y) ∈ domΦ} := by
  ext r
  constructor
  · rintro ⟨⟨x', y⟩, hz, rfl⟩
    rcases hz with ⟨hxy, rfl⟩
    exact ⟨y, hxy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(x, y), ⟨hy, rfl⟩, rfl⟩

/-- On the finite-value domain of the canonical Chapter 3 infimal projection, the real part of
the partial value function agrees with the textbook infimum of `Φ (x, y)` over the feasible
second-coordinate fiber above `x`. -/
theorem extendedRealRealPart_partialInfProjection_eq_sInf_image
    {domΦ : Set (E₁ × E₂)} {Φ : E₁ × E₂ → ℝ} {x : E₁}
    (hx : x ∈ dom (partialInfProjection domΦ (Real.toEReal ∘ Φ))) :
    extendedRealRealPart (partialInfProjection domΦ (Real.toEReal ∘ Φ)) x =
      sInf ((fun y : E₂ ↦ Φ (x, y)) '' {y | (x, y) ∈ domΦ}) := by
  rw [extendedRealRealPart_partialInfProjection_eq_sInf hx]
  rw [pairFiber_image_eq_secondFiber_image domΦ Φ x]

end
