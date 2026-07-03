import Mathlib
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_1_8_1 (from Chap01) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain:
* first-order smooth optimization on real Hilbert spaces

Relevant owner-style declarations sampled before refining:
* `firstOrderTaylorModelAt` in `FirstOrderTaylorModel.lean`
* `quadraticallyRegularizedObjective` in `FirstOrderTaylorModel.lean`
* `gradient_quadratic_model_eq_completedSquare` in `FirstOrderTaylorModel.lean`
* `gradientMethod` in `Algorithm_1_6_1.lean`
* `isMinOn_univ_iff` in mathlib's `Order.Filter.Extr`
* `taylor_upper_bound_of_contDiffOne_withLipschitzGradient` in `Lemma_1_5_10.lean`

Source/core/bridge triage:
* source-facing: Proposition 1.8.1's quadratically regularized first-order Taylor model,
  its minimizer, and its global upper-approximation inequality
* core/canonical owner:
  `quadraticallyRegularizedObjective (firstOrderTaylorModelAt f xBar) (1 / h) xBar`
  together with `gradient_quadratic_model_eq_completedSquare`, `IsMinOn`, `gradientMethod`, and
  the smooth upper Taylor estimate from `Lemma_1_5_10`
* bridge/view: the owner completed-square rewrite, which turns the regularized model into a
  manifestly nonnegative quadratic error term

Primitive data:
* the objective `f`, the base point `xBar`, and the step size `h`
* the smoothness hypotheses `ContDiff ℝ 1 f` and `LipschitzWith L (∇ f)`

Derived API:
* the source-facing minimizer statement for the regularized first-order model
* the global upper-approximation inequality

The public API is therefore organized around the source-facing regularized first-order model.
Since the proposition uses only the Hilbert-space owners above and no coordinate-specific data,
the Euclidean matrix quadratic bridge is removed rather than retained as a parallel local API. -/

/-- Proposition 1.8.1 (1): the regularized first-order Taylor model with quadratic parameter `1 / h`
is minimized at the first iterate of the constant-step gradient method. -/
-- Proof sketch: rewrite the regularized first-order model by completing the square around the
-- gradient step `xBar - h • ∇ f xBar`, identify that point with
-- `gradientMethod (fun _ ↦ h) f xBar 1`, using the owner theorem
-- `gradient_quadratic_model_eq_completedSquare`, and then use nonnegativity of the remaining
-- quadratic term.
theorem gradientMethodUpperModel_isMinOn (f : E → ℝ)
    (xBar : E) {h : ℝ} (hh : 0 < h) :
    IsMinOn
      (quadraticallyRegularizedObjective (firstOrderTaylorModelAt f xBar) (1 / h) xBar)
      Set.univ
      (gradientMethod (fun _ ↦ h) f xBar 1) := by
  rw [isMinOn_univ_iff]
  intro x
  have hδ : (1 / h : ℝ) ≠ 0 := one_div_ne_zero hh.ne'
  have hstep : gradientMethod (fun _ ↦ h) f xBar 1 = xBar - h • ∇ f xBar := by
    simp
  have hstepModel :
      quadraticallyRegularizedObjective (firstOrderTaylorModelAt f xBar) (1 / h) xBar
        (gradientMethod (fun _ ↦ h) f xBar 1) =
        f xBar - (h / 2) * ‖∇ f xBar‖ ^ (2 : ℕ) := by
    simpa [hstep, one_div, hh.ne'] using
      gradient_quadratic_model_eq_completedSquare
        f xBar (gradientMethod (fun _ ↦ h) f xBar 1) hδ
  have hxModel :
      quadraticallyRegularizedObjective (firstOrderTaylorModelAt f xBar) (1 / h) xBar x =
        f xBar + ((1 / h : ℝ) / 2) * ‖x - (xBar - h • ∇ f xBar)‖ ^ (2 : ℕ) -
          (h / 2) * ‖∇ f xBar‖ ^ (2 : ℕ) := by
    simpa [one_div, hh.ne'] using gradient_quadratic_model_eq_completedSquare f xBar x hδ
  rw [hstepModel, hxModel]
  have hnonneg : 0 ≤ ((1 / h : ℝ) / 2) * ‖x - (xBar - h • ∇ f xBar)‖ ^ (2 : ℕ) := by
    positivity
  linarith

/-- Proposition 1.8.1 (2): if `f` belongs to the chapter's `C^{1,1}_L` owner class and
`0 < h` with `(L : ℝ) * h ≤ 1`, then the regularized first-order Taylor model with quadratic
parameter `1 / h` is a global upper approximation of `f`. -/
-- Proof sketch: apply the standard quadratic upper Taylor bound at `xBar` and compare the
-- coefficient `L / 2` with `((1 / h) / 2)` using `(L : ℝ) * h ≤ 1`.
theorem gradientMethodUpperModel_isGlobalUpperApproximation {L : NNReal}
    (f : E → ℝ) (xBar x : E) {h : ℝ}
    (hf : ContDiff ℝ 1 f) (hgrad : LipschitzWith L (∇ f))
    (hh : 0 < h) (hLh : (L : ℝ) * h ≤ 1) :
    f x ≤
      quadraticallyRegularizedObjective (firstOrderTaylorModelAt f xBar) (1 / h) xBar x := by
  have hcoeff : ((L : ℝ) / 2) ≤ (1 / h) / 2 := by
    have hLinv : (L : ℝ) ≤ 1 / h := by
      rw [le_div_iff₀ hh]
      simpa [mul_comm] using hLh
    exact div_le_div_of_nonneg_right hLinv (by norm_num)
  calc
    f x ≤ firstOrderTaylorModelAt f xBar x + ((L : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ) :=
      taylor_upper_bound_of_contDiffOne_withLipschitzGradient hf hgrad xBar x
    _ ≤ quadraticallyRegularizedObjective (firstOrderTaylorModelAt f xBar) (1 / h) xBar x := by
      rw [quadraticallyRegularizedObjective_apply]
      gcongr

end

/-! ### Proposition_1_8_1 (from Items/Chap01) -/
open scoped Gradient

universe u

/- Proposition 1.8.1 lies in the first-order smooth optimization / quadratic upper-model domain.

Relevant owner-style declarations sampled before drafting:
* `gradientMethodUpperModel_isMinOn`
* `gradientMethodUpperModel_isGlobalUpperApproximation`
* `gradientMethod`
* `quadraticallyRegularizedObjective`

Best owner abstraction:
* the canonical upper model
  `quadraticallyRegularizedObjective (firstOrderTaylorModelAt f xBar) (1 / h) xBar`
  together with its minimizer and upper-approximation theorems already proved in
  `LecturesConvexOptimization_Nesterov_2018.Chap01.Proposition_1_8_1`

Primitive data:
* the objective `f`, base point `xBar`, and step size `h`
* the smoothness data `ContDiff ℝ 1 f` and `LipschitzWith L (∇ f)`

Derived API:
* the minimizer statement for the quadratic upper model
* the global upper-approximation inequality under `h ≤ 1 / L`

Source/core/bridge triage:
* source-facing: the textbook model `φ₁` and its minimizer / upper-bound properties
* core/canonical: the chapter owner
  `quadraticallyRegularizedObjective (firstOrderTaylorModelAt f xBar) (1 / h) xBar`
* bridge/view: identifying the minimizer with the first constant-step gradient iterate

This item is therefore recall-only: the chapter already contains the exact canonical theorems for
both atomic clauses of the proposition, so this file reuses them directly instead of introducing
parallel wrapper declarations or a redundant local `φ₁` owner. -/

/- Proposition 1.8.1 (1): the quadratically regularized first-order Taylor model with parameter
`1 / h` is minimized at the first iterate of the constant-step gradient method, equivalently at
`xBar - h • ∇ f xBar`. -/
recall gradientMethodUpperModel_isMinOn
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (xBar : E) {h : ℝ} (hh : 0 < h) :
    IsMinOn
      (quadraticallyRegularizedObjective (firstOrderTaylorModelAt f xBar) (1 / h) xBar)
      Set.univ
      (gradientMethod (fun _ ↦ h) f xBar 1)

/- Proposition 1.8.1 (2): if `f` has `L`-Lipschitz gradient and `0 < h` with `(L : ℝ) * h ≤ 1`,
then the same quadratic model is a global upper approximation of `f`. -/
recall gradientMethodUpperModel_isGlobalUpperApproximation
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {L : NNReal} (f : E → ℝ) (xBar x : E) {h : ℝ}
    (hf : ContDiff ℝ 1 f) (hgrad : LipschitzWith L (∇ f))
    (hh : 0 < h) (hLh : (L : ℝ) * h ≤ 1) :
    f x ≤
      quadraticallyRegularizedObjective (firstOrderTaylorModelAt f xBar) (1 / h) xBar x

/-! ### Proposition_1_8_2 (from Chap01) -/
open scoped Gradient
open NewtonSystem (AdmissiblePoint)

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 1.8.2 lies in the domain of second-order Taylor models for Euclidean optimization.

Sampled owner-style declarations:
* `secondOrderTaylorModelAt` in `Definition_1_4_17`, the source-facing quadratic Taylor model;
* `hessianMatrix` in `Definition_1_4_16`, the Euclidean matrix view of the Hessian operator;
* `NewtonSystem.step` in `Algorithm_1_7_1`, the chapter owner of the full Newton update for
  the stationarity system `∇ f = 0`;
* `UnconstrainedQuadraticMinimizationProblem.isMinOn_translate` in `Lemma_1_8_8`, the translated
  quadratic minimization theorem used internally.

Owner abstractions:
* the source-facing quadratic model `secondOrderTaylorModelAt`;
* the Newton update owner `NewtonSystem.step (∇ f)`.

Primitive data:
* the objective `f`;
* the center `xBar`;
* the positive-definite Hessian matrix `∇² f xBar`.

Derived API:
* the coordinate realization
  `quadraticObjective (f xBar) (∇ f xBar) (∇² f xBar) (x - xBar)`;
* the canonical Newton step `NewtonSystem.step (∇ f)` at the admissible point given by Hessian
  nondegeneracy;
* the inverse-Hessian coordinate formula
  `xBar - ((∇² f xBar)⁻¹).toEuclideanLin (∇ f xBar)` as a bridge view of that step;
* the internal translated quadratic problem used to prove global minimality.

Source/core/bridge triage:
* source-facing: the quadratic Taylor model `secondOrderTaylorModelAt f xBar` together with its
  minimizer statement;
* core/canonical: `secondOrderTaylorModelAt`, `NewtonSystem.step (∇ f)`, and the owner bridge
  `DampedNewton.step_eq_hessianMatrixFormula`;
* bridge/view: the matrix realization via `hessianMatrix` and `quadraticObjective`, plus the
  inverse-Hessian coordinate formula specialized from the damped-Newton owner at `h = 1`.
-/

/-- A positive-definite Hessian matrix gives the Jacobian nondegeneracy needed to view `xBar` as
an admissible Newton point for the stationarity system `∇ f = 0`. -/
theorem hessian_det_ne_zero_of_posDef (f : E → ℝ) (xBar : E) (hH : (∇² f xBar).PosDef) :
    (fderiv ℝ (∇ f) xBar).det ≠ 0 := by
  change LinearMap.det (fderiv ℝ (∇ f) xBar).toLinearMap ≠ 0
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (fderiv ℝ (∇ f) xBar).toLinearMap]
  simpa [hessianMatrix] using hH.det_pos.ne'

/-- The canonical Newton step for the stationarity system `∇ f = 0` agrees with the textbook
inverse-Hessian formula when the Hessian at `xBar` is positive definite. -/
theorem newtonSystem_step_eq_matrixFormula (f : E → ℝ) (xBar : E)
    (hH : (∇² f xBar).PosDef) :
    NewtonSystem.step (∇ f) ⟨xBar, hessian_det_ne_zero_of_posDef f xBar hH⟩ =
      xBar - ((∇² f xBar)⁻¹).toEuclideanLin (∇ f xBar) := by
  let xN : AdmissiblePoint (∇ f) := ⟨xBar, hessian_det_ne_zero_of_posDef f xBar hH⟩
  calc
    NewtonSystem.step (∇ f) xN = DampedNewton.step f xN 1 := by
      simp [DampedNewton.step]
    _ = xBar - ((∇² f xBar)⁻¹).toEuclideanLin (∇ f xBar) := by
      simpa [xN] using DampedNewton.step_eq_hessianMatrixFormula f xN (1 : ℝ)

/-- Proposition 1.8.2: if the Hessian matrix `∇² f xBar` is positive definite, then the
quadratic Taylor model `φ₂ = secondOrderTaylorModelAt f xBar` is minimized at the canonical
Newton step for the stationarity equation `∇ f = 0`. The source-facing inverse-Hessian formula
for that step is recovered from `DampedNewton.step_eq_hessianMatrixFormula` at `h = 1`; the
matrix quadratic problem is used only as an internal bridge to Lemma 1.8.8. -/
-- Proof sketch: rewrite `secondOrderTaylorModelAt f xBar` as its canonical Euclidean matrix
-- realization and apply the translated quadratic minimization theorem from Lemma 1.8.8.
theorem newtonQuadraticModel_isMinOn (f : E → ℝ) (xBar : E)
    (hH : (∇² f xBar).PosDef) :
    IsMinOn
      (secondOrderTaylorModelAt f xBar)
      Set.univ
      (NewtonSystem.step (∇ f) ⟨xBar, hessian_det_ne_zero_of_posDef f xBar hH⟩) := by
  have hxN_det : (fderiv ℝ (∇ f) xBar).det ≠ 0 :=
    hessian_det_ne_zero_of_posDef f xBar hH
  let xN : AdmissiblePoint (∇ f) := ⟨xBar, hxN_det⟩
  let problem : UnconstrainedQuadraticMinimizationProblem n :=
    { α := f xBar
      a := ∇ f xBar
      A := ∇² f xBar
      posDef := hH }
  have hmodel :
      secondOrderTaylorModelAt f xBar =
        fun x ↦ quadraticObjective (f xBar) (∇ f xBar) (∇² f xBar) (x - xBar) := by
    funext x
    rw [secondOrderTaylorModelAt_apply_hessianMatrix, quadraticObjective]
  have hstep :
      xBar + problem.minimizer = NewtonSystem.step (∇ f) xN := by
    calc
      xBar + problem.minimizer = xBar - ((∇² f xBar)⁻¹).toEuclideanLin (∇ f xBar) := by
        simp [problem, UnconstrainedQuadraticMinimizationProblem.minimizer, sub_eq_add_neg]
      _ = NewtonSystem.step (∇ f) xN := by
        simpa [xN] using (newtonSystem_step_eq_matrixFormula f xBar hH).symm
  have hbridge :
      IsMinOn
        (fun x ↦ quadraticObjective (f xBar) (∇ f xBar) (∇² f xBar) (x - xBar))
        Set.univ
        (NewtonSystem.step (∇ f) xN) := by
    simpa only [problem, UnconstrainedQuadraticMinimizationProblem.coe_apply, hstep] using
      problem.isMinOn_translate xBar
  simpa [xN, hmodel] using hbridge

end

/-! ### Proposition_1_8_2 (from Items/Chap01) -/
open scoped Gradient

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 1.8.2 lies in second-order smooth optimization / Newton quadratic models.

Relevant owner-style declarations sampled before refining:
* `secondOrderTaylorModelAt` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_4_17`
* `hessianMatrix_toEuclideanLin` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_4_16`
* `NewtonSystem.step` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Algorithm_1_7_1`
* `newtonSystem_step_eq_matrixFormula` and `newtonQuadraticModel_isMinOn` in
  `LecturesConvexOptimization_Nesterov_2018/Chap01/Proposition_1_8_2`

Best owner abstraction:
* the source-facing quadratic model `secondOrderTaylorModelAt f xBar`
* the canonical Newton update `NewtonSystem.step (∇ f)` at the admissible point supplied by
  Hessian nondegeneracy

Primitive data:
* the objective `f`
* the base point `xBar`
* the positive-definite Hessian matrix `∇² f xBar`

Derived API:
* the inverse-Hessian coordinate formula for the canonical Newton step
* the minimizer statement for the quadratic Taylor model

Source/core/bridge triage:
* source-facing: the quadratic model and its minimizing Newton iterate
* core/canonical: `secondOrderTaylorModelAt` and `NewtonSystem.step`
* bridge/view: the inverse-Hessian matrix formula

This item is therefore recall-only: the chapter owner already proves the exact minimizer
statement and the source-facing matrix formula, so the local wrapper `newtonStepAt` is removed
instead of being kept as a parallel public owner. -/

/- Proposition 1.8.2 (1): if `∇² f xBar` is positive definite, then the quadratic Taylor model
`secondOrderTaylorModelAt f xBar` is minimized at the canonical Newton step. -/
recall newtonQuadraticModel_isMinOn
    (f : E → ℝ) (xBar : E) (hH : (∇² f xBar).PosDef) :
    IsMinOn
      (secondOrderTaylorModelAt f xBar)
      Set.univ
      (NewtonSystem.step (∇ f) ⟨xBar, _root_.hessian_det_ne_zero_of_posDef f xBar hH⟩)

/- Proposition 1.8.2 (2): the canonical Newton step agrees with the textbook inverse-Hessian
formula `xBar - [∇² f(xBar)]⁻¹ ∇ f(xBar)`. -/
recall _root_.newtonSystem_step_eq_matrixFormula
    (f : E → ℝ) (xBar : E) (hH : (∇² f xBar).PosDef) :
    NewtonSystem.step (∇ f) ⟨xBar, _root_.hessian_det_ne_zero_of_posDef f xBar hH⟩ =
      xBar - ((∇² f xBar)⁻¹).toEuclideanLin (∇ f xBar)

/-! ### Definition_1_8_3 (from Chap01) -/
open Matrix
open scoped ComplexOrder

noncomputable section

variable {n : ℕ}

local notation "E" => Fin n → ℝ
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "PosMat" => {A : Mat // Matrix.PosDef A}
local notation "Euclid" => EuclideanSpace ℝ (Fin n)
local notation "coordEquiv" => EuclideanSpace.equiv (Fin n) ℝ

/- Definition 1.8.3 is a source-facing recall in the positive-definite matrix geometry of `ℝ^n`,
modeled as `Fin n → ℝ`.

Primary domain:
- inner products and norms induced by positive-(semi)definite matrices.

Sampled owner-style declarations:
- `Matrix.toNormedAddCommGroup`, the canonical norm owner attached to a positive-definite matrix;
- `Matrix.toInnerProductSpace`, the canonical inner-product owner attached to a positive
  semidefinite matrix;
- `Matrix.PosDef.posSemidef`, the bridge from the positive-definite hypothesis needed for the norm
  owner to the positive-semidefinite hypothesis needed for the inner-product owner;
- `Matrix.dotProduct_mulVec`, the coordinate formula used in the textbook expansion.

Best owner abstraction:
- the canonical induced structures `Matrix.toNormedAddCommGroup A hA` and
  `Matrix.toInnerProductSpace A hA.posSemidef`.

Primitive data:
- `A : Mat`
- `hA : A.PosDef`

Derived API:
- the source-facing notation `‖x‖[A]` and `⟪x, y⟫_[A]` for
  `A : {A : Mat // A.PosDef}`;
- the textbook coordinate formulas recorded below as thin bridge lemmas.

Source/core/bridge triage:
- source-facing: the induced norm and inner product attached to a positive-definite matrix;
- core/canonical: `Matrix.toNormedAddCommGroup` and `Matrix.toInnerProductSpace`;
- bridge/view: the notation layer `‖x‖[A]`, `⟪x, y⟫_[A]`, and the formula companions
  `inner_eq_dotProduct_mulVec`, `norm_eq_sqrt_dotProduct_mulVec`, implemented through
  abbreviation-level notation bridges.

This file therefore keeps Definition 1.8.3 as direct canonical recall/use of the induced owner
structures, rather than introducing a second public wrapper API for the same norm and inner
product.
-/

recall Matrix.toNormedAddCommGroup
    {n : Type*} {𝕜 : Type*} [Fintype n] [RCLike 𝕜] (M : Matrix n n 𝕜) (hM : M.PosDef) :
    NormedAddCommGroup (n → 𝕜)

recall Matrix.toInnerProductSpace
    {n : Type*} {𝕜 : Type*} [Fintype n] [RCLike 𝕜] (M : Matrix n n 𝕜) (hM : M.PosSemidef) :
    @InnerProductSpace 𝕜 (n → 𝕜) _ (M.toSeminormedAddCommGroup hM)

namespace Matrix
namespace PosDef

/-- The coordinate model `Fin n → ℝ`, equipped with the norm and inner product induced by the
positive-definite matrix owner `A`. This is the bridge carrier used by the weighted Chapter 1
owners. -/
abbrev WeightedSpace (_A : PosMat) := E

instance (A : PosMat) : NormedAddCommGroup (WeightedSpace (n := n) A) :=
  Matrix.toNormedAddCommGroup A.1 A.2

instance (A : PosMat) :
    @InnerProductSpace ℝ (WeightedSpace A) _
      (Matrix.toNormedAddCommGroup A.1 A.2).toSeminormedAddCommGroup :=
  Matrix.toInnerProductSpace A.1 A.2.posSemidef

instance (A : PosMat) : CompleteSpace (WeightedSpace (n := n) A) :=
  FiniteDimensional.complete ℝ (WeightedSpace A)

abbrev weightedInner (A : PosMat) (x y : E) : ℝ :=
  @inner ℝ E (Matrix.toInnerProductSpace A.1 A.2.posSemidef).toInner x y

abbrev weightedNorm (A : PosMat) (x : E) : ℝ :=
  @norm E (Matrix.toNormedAddCommGroup A.1 A.2).toNorm x

end PosDef
end Matrix

namespace MatrixPosDef

scoped notation:70 "⟪" x ", " y "⟫_[" A:arg "]" => Matrix.PosDef.weightedInner A x y
scoped notation:max "‖" x "‖[" A:arg "]" => Matrix.PosDef.weightedNorm A x

end MatrixPosDef

open scoped MatrixPosDef

namespace Matrix
namespace PosDef

/-- For a positive-definite real matrix owner, the weighted inner product is the textbook pairing
`⟪Ax, y⟫`. -/
theorem inner_eq_dotProduct_mulVec (A : PosMat) (x y : E) :
    ⟪x, y⟫_[A] = dotProduct (A.1 *ᵥ x) y := by
  change dotProduct (A.1 *ᵥ y) x = dotProduct (A.1 *ᵥ x) y
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose]
  have hA' : A.1ᴴ = A.1 := by
    simpa using A.2.1.eq
  rw [← conjTranspose_eq_transpose_of_trivial A.1, hA']

/-- For a positive-definite real matrix owner, the weighted norm is the square root of the weighted
quadratic form `⟪Ax, x⟫`. -/
theorem norm_eq_sqrt_dotProduct_mulVec (A : PosMat) (x : E) :
    ‖x‖[A] = Real.sqrt (dotProduct (A.1 *ᵥ x) x) := by
  rw [show ‖x‖[A] = Real.sqrt (⟪x, x⟫_[A]) by
    exact @norm_eq_sqrt_real_inner E
      (Matrix.toNormedAddCommGroup A.1 A.2).toSeminormedAddCommGroup
      (Matrix.toInnerProductSpace A.1 A.2.posSemidef) x]
  rw [inner_eq_dotProduct_mulVec]

/-- Transporting the weighted norm on coordinates through `EuclideanSpace.equiv` rewrites it as
the textbook Euclidean quadratic form `⟪Ax, x⟫`. -/
theorem norm_coordEquiv_eq_sqrt_inner_toEuclideanLin (A : PosMat) (x : Euclid) :
    ‖coordEquiv x‖[A] = Real.sqrt (inner ℝ (A.1.toEuclideanLin x) x) := by
  have hinner :
      inner ℝ (A.1.toEuclideanLin x) x = dotProduct (coordEquiv x) (A.1 *ᵥ coordEquiv x) := by
    simpa only [Matrix.ofLp_toLpLin] using
      (EuclideanSpace.inner_eq_star_dotProduct (A.1.toEuclideanLin x) x)
  calc
    ‖coordEquiv x‖[A] = Real.sqrt (dotProduct (A.1 *ᵥ coordEquiv x) (coordEquiv x)) := by
      simpa using norm_eq_sqrt_dotProduct_mulVec A (coordEquiv x)
    _ = Real.sqrt (inner ℝ (A.1.toEuclideanLin x) x) := by
      rw [hinner, dotProduct_comm]

/-- The identity-matrix weighted norm on coordinates agrees with the Euclidean norm after
transporting by `EuclideanSpace.equiv`. -/
theorem one_norm_coordEquiv_eq (x : Euclid) :
    ‖coordEquiv x‖[⟨(1 : Mat), PosDef.one⟩] = ‖x‖ := by
  calc
    ‖coordEquiv x‖[⟨(1 : Mat), PosDef.one⟩] =
        Real.sqrt (dotProduct ((1 : Mat) *ᵥ coordEquiv x) (coordEquiv x)) := by
      simpa using norm_eq_sqrt_dotProduct_mulVec ⟨(1 : Mat), PosDef.one⟩ (coordEquiv x)
    _ = ‖x‖ := by
      rw [EuclideanSpace.norm_eq x]
      simp [dotProduct, pow_two]

end PosDef
end Matrix

end

/-! ### Definition_1_8_3 (from Items/Chap01) -/
open Matrix
open scoped ComplexOrder

noncomputable section

variable {n : ℕ}

local notation "E" => Fin n → ℝ
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "PosMat" => {A : Mat // Matrix.PosDef A}

/- Definition 1.8.3 is a source-facing recall in the positive-definite matrix geometry of `ℝ^n`,
modeled as `Fin n → ℝ`.

Primary domain:
- inner products and norms induced by positive-(semi)definite matrices.

Sampled owner-style declarations:
- `Matrix.toNormedAddCommGroup`, the canonical norm owner attached to a positive-definite matrix;
- `Matrix.toInnerProductSpace`, the canonical inner-product owner attached to a positive
  semidefinite matrix;
- `Matrix.PosDef.posSemidef`, the bridge from the positive-definite hypothesis needed for the norm
  owner to the positive-semidefinite hypothesis needed for the inner-product owner;
- `Matrix.dotProduct_mulVec`, the coordinate formula used in the textbook expansion.

Best owner abstraction:
- the canonical induced structures `Matrix.toNormedAddCommGroup A hA` and
  `Matrix.toInnerProductSpace A hA.posSemidef`.

Primitive data:
- `A : Mat`
- `hA : A.PosDef`

Derived API:
- the source-facing notation `‖x‖[A]` and `⟪x, y⟫_[A]` for
  `A : PosMat`;
- the textbook coordinate formulas recorded below as thin bridge lemmas.

Source/core/bridge triage:
- source-facing: the induced norm and inner product attached to a positive-definite matrix;
- core/canonical: `Matrix.toNormedAddCommGroup` and `Matrix.toInnerProductSpace`;
- bridge/view: the notation layer `‖x‖[A]`, `⟪x, y⟫_[A]`, and the formula companions
  `inner_eq_dotProduct_mulVec`, `norm_eq_sqrt_dotProduct_mulVec`, implemented through private
  abbreviation-level notation bridges only.

This file therefore keeps Definition 1.8.3 as direct canonical recall/use of the induced owner
structures, rather than introducing a second public wrapper API for the same norm and inner
product.
-/

recall Matrix.toNormedAddCommGroup
    {n : Type*} {𝕜 : Type*} [Fintype n] [RCLike 𝕜] (M : Matrix n n 𝕜) (hM : M.PosDef) :
    NormedAddCommGroup (n → 𝕜)

recall Matrix.toInnerProductSpace
    {n : Type*} {𝕜 : Type*} [Fintype n] [RCLike 𝕜] (M : Matrix n n 𝕜) (hM : M.PosSemidef) :
    @InnerProductSpace 𝕜 (n → 𝕜) _ (M.toSeminormedAddCommGroup hM)

namespace Matrix
namespace PosDef

private abbrev weightedInner (A : PosMat) (x y : E) : ℝ :=
  @inner ℝ E (Matrix.toInnerProductSpace A.1 A.2.posSemidef).toInner x y

private abbrev weightedNorm (A : PosMat) (x : E) : ℝ :=
  @norm E (Matrix.toNormedAddCommGroup A.1 A.2).toNorm x

end PosDef
end Matrix

namespace MatrixPosDef

scoped notation:70 "⟪" x ", " y "⟫_[" A:arg "]" => Matrix.PosDef.weightedInner A x y
scoped notation:max "‖" x "‖[" A:arg "]" => Matrix.PosDef.weightedNorm A x

end MatrixPosDef

open scoped MatrixPosDef

namespace Matrix
namespace PosDef

/-- For a positive-definite real matrix owner, the weighted inner product is the textbook pairing
`⟪Ax, y⟫`. -/
theorem inner_eq_dotProduct_mulVec (A : PosMat) (x y : E) :
    ⟪x, y⟫_[A] = dotProduct (A.1 *ᵥ x) y := by
  change dotProduct (A.1 *ᵥ y) x = dotProduct (A.1 *ᵥ x) y
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose]
  have hA' : A.1ᴴ = A.1 := by
    simpa using A.2.1.eq
  rw [← conjTranspose_eq_transpose_of_trivial A.1, hA']

/-- For a positive-definite real matrix owner, the weighted norm is the square root of the weighted
quadratic form `⟪Ax, x⟫`. -/
theorem norm_eq_sqrt_dotProduct_mulVec (A : PosMat) (x : E) :
    ‖x‖[A] = Real.sqrt (dotProduct (A.1 *ᵥ x) x) := by
  rw [show ‖x‖[A] = Real.sqrt (⟪x, x⟫_[A]) by
    exact @norm_eq_sqrt_real_inner E
      (Matrix.toNormedAddCommGroup A.1 A.2).toSeminormedAddCommGroup
      (Matrix.toInnerProductSpace A.1 A.2.posSemidef) x]
  rw [inner_eq_dotProduct_mulVec]

end PosDef
end Matrix

end

/-! ### Definition_1_8_4 (from Chap01) -/
open Matrix
open scoped Topology Gradient MatrixPosDef

noncomputable section

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "PosMat" => {A : Mat // Matrix.PosDef A}

/- Definition 1.8.4 is source-facing in weighted second-order differential calculus.

Source/core/bridge triage:
- source-facing: the textbook quadratic expansion clause
  `HasWeightedGradientSecondOrderExpansionAt A f g H x`
- core/canonical: the derivative-level pair
  `HasGradientAt f g x ∧ HasFDerivAt (∇ f) ((1 / 2 : ℝ) • (H + H.adjoint)) x`
  on `WeightedSpace A`
- bridge/view: the self-adjoint-average bridge from the textbook quadratic expansion clause to
  the canonical weighted first- and second-order owners

Primary domain:
- second-order differential calculus on finite-dimensional weighted inner-product spaces

Relevant owner-style declarations sampled before refining:
- `Matrix.PosDef.WeightedSpace`
- `HasGradientAt`
- `HasFDerivAt`
- `ContinuousLinearMap.adjoint`
- `IsSelfAdjoint.add_star_self`

Best owner abstraction:
- the weighted-space owner `WeightedSpace A` induced by `A : PosMat`
- the canonical weighted first- and second-order owner pair attached to the weighted self-adjoint
  average of the quadratic witness
  `HasGradientAt f g x ∧ HasFDerivAt (∇ f) ((1 / 2 : ℝ) • (H + H.adjoint)) x`

Primitive data:
- `A : PosMat`
- `f : Matrix.PosDef.WeightedSpace A → ℝ`
- `x : Matrix.PosDef.WeightedSpace A`
- `g : Matrix.PosDef.WeightedSpace A`
- `H : Matrix.PosDef.WeightedSpace A →L[ℝ] Matrix.PosDef.WeightedSpace A`

Derived API:
- the source-facing weighted quadratic expansion clause
  `HasWeightedGradientSecondOrderExpansionAt A f g H x`
- the adjoint-average invariance of that clause
  `HasWeightedGradientSecondOrderExpansionAt.iff_adjointAverage`
- the recovery of the weighted first-order owner from the quadratic expansion
  `HasWeightedGradientSecondOrderExpansionAt.hasGradientAt_of_weighted_second_order`
- the forward bridge from a genuine weighted gradient together with a derivative of the totalized
  gradient to the source-facing quadratic expansion
  `HasWeightedGradientSecondOrderExpansionAt.weighted_second_order_of_hasGradientAt_and_hasFDerivAt_gradient`
- the directional line-restriction consequence recording the quadratic coefficient
  `HasWeightedGradientSecondOrderExpansionAt.line_restriction_has_weighted_second_order_expansion`

The quadratic term `⟪K h, h⟫_[A]` only depends on the weighted self-adjoint part of `K`. The file
therefore keeps the textbook expansion clause as the main source-facing owner and records the
first-order recovery and honest forward/directional companions, while avoiding a false reverse
API for the totalized gradient. -/

local notation "WeightedSpace" => Matrix.PosDef.WeightedSpace

section

variable {A : PosMat}
variable {f : WeightedSpace A → ℝ} {x g : WeightedSpace A}
variable {H : WeightedSpace A →L[ℝ] WeightedSpace A}

/-- The textbook weighted second-order expansion clause with linear witness `g` and quadratic
operator witness `H` at `x`. -/
def HasWeightedGradientSecondOrderExpansionAt
    (A : PosMat) (f : WeightedSpace A → ℝ) (g : WeightedSpace A)
    (H : WeightedSpace A →L[ℝ] WeightedSpace A) (x : WeightedSpace A) : Prop :=
  (fun h ↦
      f (x + h) -
        (f x
          + (⟪g, h⟫_[A] : ℝ)
          + (1 / 2 : ℝ) * (⟪H h, h⟫_[A] : ℝ))) =o[
            𝓝 (0 : WeightedSpace A)]
    fun h ↦ (‖h‖[A] : ℝ) ^ (2 : ℕ)

/- Definition 1.8.4: on the weighted Hilbert space determined by `A`, the source-facing notion is
the weighted quadratic expansion clause `HasWeightedGradientSecondOrderExpansionAt A f g H x`. -/
#check HasWeightedGradientSecondOrderExpansionAt A f g H x

namespace HasWeightedGradientSecondOrderExpansionAt

/-- Helper for Definition 1.8.4: package the totalized weighted gradient as an ordinary weighted
vector field so continuity and derivative hypotheses can be specialized without reopening the
gradient notation. -/
abbrev total_gradient_field (f : WeightedSpace A → ℝ) : WeightedSpace A → WeightedSpace A :=
  fun y : WeightedSpace A ↦ (∇ f y : WeightedSpace A)

/-- Helper for Definition 1.8.4: continuity of the raw weighted gradient on a neighborhood ball
immediately transfers to the packaged total gradient field. -/
lemma total_gradient_field_continuousOn
    {r : ℝ}
    (hcont_nhds : ContinuousOn (∇ f) (Metric.ball x r)) :
    ContinuousOn (total_gradient_field (A := A) f) (Metric.ball x r) := by
  -- Freeze the gradient notation into the packaged vector field before specializing generic
  -- continuity lemmas.
  simpa [total_gradient_field] using hcont_nhds

/-- Helper for Definition 1.8.4: a Fréchet derivative hypothesis for the raw weighted gradient is
the same derivative hypothesis for the packaged total gradient field. -/
lemma total_gradient_field_hasFDerivAt
    (hgrad : HasFDerivAt (∇ f) H x) :
    HasFDerivAt (total_gradient_field (A := A) f) H x := by
  -- The packaged field is definitionally the raw gradient map.
  simpa [total_gradient_field] using hgrad

/-- Helper for Definition 1.8.4: the weighted quadratic form only sees the weighted self-adjoint
average of the operator witness. -/
lemma quadratic_form_adjointAverage_eq
    (h : WeightedSpace A) :
    (⟪(((1 / 2 : ℝ) • (H + H.adjoint)) h), h⟫_[A] : ℝ) = (⟪H h, h⟫_[A] : ℝ) := by
  -- Expand the adjoint average and identify the adjoint contribution with the original quadratic
  -- term by the weighted adjoint identity.
  calc
    (⟪(((1 / 2 : ℝ) • (H + H.adjoint)) h), h⟫_[A] : ℝ)
        = (1 / 2 : ℝ) * ((⟪(H + H.adjoint) h, h⟫_[A] : ℝ)) := by
          simp
    _ = (1 / 2 : ℝ) * ((⟪H h, h⟫_[A] : ℝ) + (⟪H.adjoint h, h⟫_[A] : ℝ)) := by
          simp [inner_add_left]
    _ = (1 / 2 : ℝ) * ((⟪H h, h⟫_[A] : ℝ) + (⟪H h, h⟫_[A] : ℝ)) := by
          rw [show (⟪H.adjoint h, h⟫_[A] : ℝ) = inner ℝ h (H.adjoint h) by
                simpa using real_inner_comm (H.adjoint h) h]
          rw [ContinuousLinearMap.adjoint_inner_right]
    _ = (⟪H h, h⟫_[A] : ℝ) := by
          ring

/-- Helper for Definition 1.8.4: the weighted quadratic term is uniformly bounded by a constant
multiple of `‖h‖[A]^2` near the basepoint. -/
lemma quadratic_term_isBigO_quadratic :
    (fun h : WeightedSpace A ↦ (1 / 2 : ℝ) * (⟪H h, h⟫_[A] : ℝ)) =O[𝓝 (0 : WeightedSpace A)]
      fun h ↦ (‖h‖[A] : ℝ) ^ (2 : ℕ) := by
  -- Control the quadratic term by Cauchy-Schwarz and the operator norm of `H`.
  refine Asymptotics.IsBigO.of_bound ((1 / 2 : ℝ) * ‖H‖) ?_
  filter_upwards [Filter.Eventually.of_forall fun h : WeightedSpace A ↦ ?_] with h
  calc
    ‖(1 / 2 : ℝ) * (⟪H h, h⟫_[A] : ℝ)‖ = (1 / 2 : ℝ) * ‖(⟪H h, h⟫_[A] : ℝ)‖ := by
      rw [norm_mul, Real.norm_of_nonneg (by positivity)]
    _ ≤ (1 / 2 : ℝ) * (‖H h‖ * ‖h‖) := by
      gcongr
      simpa using (norm_inner_le_norm (𝕜 := ℝ) (H h) h)
    _ ≤ (1 / 2 : ℝ) * (‖H‖ * ‖h‖ * ‖h‖) := by
      gcongr
      exact ContinuousLinearMap.le_opNorm H h
    _ = ((1 / 2 : ℝ) * ‖H‖) * ‖(‖h‖[A] : ℝ) ^ (2 : ℕ)‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · ring
      · positivity

/-- Helper for Definition 1.8.4: the weighted quadratic term is little-`o` of the displacement,
so it does not affect the first-order gradient witness. -/
lemma quadratic_term_isLittleO_linear :
    (fun h : WeightedSpace A ↦ (1 / 2 : ℝ) * (⟪H h, h⟫_[A] : ℝ)) =o[𝓝 (0 : WeightedSpace A)]
      fun h ↦ h := by
  -- Factor the quadratic term through the standard `‖h‖^2 = o(‖h‖)` estimate.
  exact quadratic_term_isBigO_quadratic.trans_isLittleO (by
    simpa using
      (Asymptotics.isLittleO_norm_pow_id (E' := WeightedSpace A) (n := 2) (by norm_num)))

/-- Helper for Definition 1.8.4: a weighted second-order expansion already determines the
weighted gradient witness. -/
lemma hasGradientAt_of_weighted_second_order
    (hExp : HasWeightedGradientSecondOrderExpansionAt A f g H x) :
    HasGradientAt f g x := by
  -- Discard the quadratic correction, which is negligible compared with the linear term.
  rw [hasGradientAt_iff_isLittleO_nhds_zero]
  have hMain :
      (fun h : WeightedSpace A ↦
        f (x + h) - (f x + (⟪g, h⟫_[A] : ℝ) + (1 / 2 : ℝ) * (⟪H h, h⟫_[A] : ℝ))) =o[
          𝓝 (0 : WeightedSpace A)] fun h ↦ h :=
    hExp.trans_isLittleO (by
      simpa using
        (Asymptotics.isLittleO_norm_pow_id (E' := WeightedSpace A) (n := 2) (by norm_num)))
  have hSum := hMain.add quadratic_term_isLittleO_linear (A := A) (H := H)
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hSum

/-- Helper for Definition 1.8.4: pairing the linearization remainder of the weighted totalized
gradient with the displacement upgrades the vector little-`o` term to a scalar
`o(‖h‖[A]^2)` remainder. -/
lemma paired_gradient_remainder_isLittleO_quadratic
    (hg : HasGradientAt f g x)
    (hgrad : HasFDerivAt (∇ f) H x) :
    Asymptotics.IsLittleO
      (𝓝 (0 : WeightedSpace A))
      (fun h : WeightedSpace A ↦ (inner ℝ (∇ f (x + h) - g - H h) h : ℝ))
      (fun h : WeightedSpace A ↦ (‖h‖ : ℝ) ^ (2 : ℕ)) := by
  -- Control the scalar pairing by Cauchy-Schwarz and reuse the vector little-`o` estimate.
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hr_bound :
      ∀ᶠ h : WeightedSpace A in 𝓝 (0 : WeightedSpace A), ‖∇ f (x + h) - g - H h‖ ≤ c * ‖h‖ := by
    have hgradO :
        (fun h : WeightedSpace A ↦ ∇ f (x + h) - ∇ f x - H h) =o[
          𝓝 (0 : WeightedSpace A)] fun h ↦ h :=
      (hasFDerivAt_iff_isLittleO_nhds_zero (f := ∇ f) (f' := H) (x := x)).mp hgrad
    rw [Asymptotics.isLittleO_iff] at hgradO
    simpa [hg.gradient] using hgradO hc
  filter_upwards [hr_bound] with h hh
  calc
    ‖inner ℝ (∇ f (x + h) - g - H h) h‖ ≤ ‖∇ f (x + h) - g - H h‖ * ‖h‖ := by
      simpa [Real.norm_eq_abs] using
        (norm_inner_le_norm (𝕜 := ℝ) (∇ f (x + h) - g - H h) h)
    _ ≤ (c * ‖h‖) * ‖h‖ := by
      gcongr
    _ = c * ‖h‖ ^ (2 : ℕ) := by
      ring
    _ = c * ‖‖h‖ ^ (2 : ℕ)‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      positivity

/-- Helper for Definition 1.8.4: every point on a short weighted segment from `x` stays inside the
radius-`r` ball where the local gradient-field hypothesis is available. -/
lemma segment_point_mem_ball
    {r : ℝ} (hr : 0 < r) {h : WeightedSpace A} (hh : ‖h‖ < r) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    x + t • h ∈ Metric.ball x r := by
  -- The segment parameter stays in `[0,1]`, so the displacement norm contracts by at most `t`.
  have hnorm : ‖t • h‖ < r := by
    calc
      ‖t • h‖ = t * ‖h‖ := by
        rw [norm_smul, Real.norm_of_nonneg ht.1]
      _ ≤ 1 * ‖h‖ := by
        gcongr
        exact ht.2
      _ = ‖h‖ := by
        ring
      _ < r := hh
  simpa [Metric.mem_ball, dist_eq_norm] using hnorm

/-- Helper for Definition 1.8.4: along a short weighted segment, the corrected quadratic remainder
has derivative equal to the gradient linearization error paired with the segment direction. -/
lemma segment_quadratic_remainder_hasDerivAt
    {r : ℝ} (hr : 0 < r)
    (hgrad_nhds : ∀ y ∈ Metric.ball x r, HasGradientAt f (∇ f y) y)
    {h : WeightedSpace A} (hh : ‖h‖ < r) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt
      (fun u : ℝ ↦
        f (x + u • h) - f x - u * (⟪g, h⟫_[A] : ℝ) -
          (1 / 2 : ℝ) * u ^ (2 : ℕ) * (⟪H h, h⟫_[A] : ℝ))
      (⟪∇ f (x + t • h) - g - t • H h, h⟫_[A] : ℝ) t := by
  -- Differentiate the affine segment first, then compose it with the local gradient identity.
  have hy : HasGradientAt f (∇ f (x + t • h)) (x + t • h) :=
    hgrad_nhds (x + t • h) (segment_point_mem_ball (A := A) (x := x) hr hh ht)
  have hline : HasDerivAt (fun u : ℝ ↦ x + u • h) h t := by
    simpa [one_smul] using (((hasDerivAt_id t).smul_const h).const_add x)
  have hseg :
      HasDerivAt (fun u : ℝ ↦ f (x + u • h)) ((fderiv ℝ f (x + t • h)) h) t := by
    simpa [Function.comp] using (hy.hasFDerivAt.comp t hline.hasFDerivAt).hasDerivAt
  -- Differentiate the affine and quadratic model terms separately.
  have hlin : HasDerivAt (fun u : ℝ ↦ u * (⟪g, h⟫_[A] : ℝ)) (⟪g, h⟫_[A] : ℝ) t := by
    simpa [one_mul] using (hasDerivAt_id t).mul_const (⟪g, h⟫_[A] : ℝ)
  have hsq : HasDerivAt (fun u : ℝ ↦ u ^ (2 : ℕ)) (2 * t) t := by
    simpa [pow_two, two_mul] using (hasDerivAt_id t).mul (hasDerivAt_id t)
  have hquad :
      HasDerivAt
        (fun u : ℝ ↦ (1 / 2 : ℝ) * u ^ (2 : ℕ) * (⟪H h, h⟫_[A] : ℝ))
        (t * (⟪H h, h⟫_[A] : ℝ)) t := by
    have hconst :
        HasDerivAt
          (fun u : ℝ ↦ ((1 / 2 : ℝ) * (⟪H h, h⟫_[A] : ℝ)) * (u ^ (2 : ℕ)))
          (((1 / 2 : ℝ) * (⟪H h, h⟫_[A] : ℝ)) * (2 * t)) t :=
      hsq.const_mul ((1 / 2 : ℝ) * (⟪H h, h⟫_[A] : ℝ))
    simpa [mul_assoc, mul_left_comm, mul_comm] using hconst
  have hmain :
      HasDerivAt
        (fun u : ℝ ↦
          f (x + u • h) - f x - u * (⟪g, h⟫_[A] : ℝ) -
            (1 / 2 : ℝ) * u ^ (2 : ℕ) * (⟪H h, h⟫_[A] : ℝ))
        (((fderiv ℝ f (x + t • h)) h) - (⟪g, h⟫_[A] : ℝ) - t * (⟪H h, h⟫_[A] : ℝ)) t := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      hseg.sub ((hasDerivAt_const t (f x)).add hlin).sub hquad
  -- Rewrite the Fréchet derivative and the quadratic scalar term into weighted-inner form.
  simpa [hy.fderiv_apply, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
    inner_sub_left, ContinuousLinearMap.map_smul, inner_smul_left, mul_assoc, mul_left_comm,
    mul_comm] using hmain

/-- Helper for Definition 1.8.4: pairing a continuous weighted vector field with a fixed weighted
direction preserves continuity on the same set. -/
lemma weighted_segment_pair_continuousOn
    {s : Set ℝ} {v : ℝ → WeightedSpace A} (hv : ContinuousOn v s) (h : WeightedSpace A) :
    ContinuousOn (fun t : ℝ ↦ (⟪v t, h⟫_[A] : ℝ)) s := by
  -- Route the weighted pairing through the ambient inner-product continuity API.
  intro t ht
  have hconst : ContinuousAt (fun _ : ℝ ↦ h) t := continuousAt_const
  simpa [Matrix.PosDef.weightedInner] using (hv t ht).inner hconst

/-- Helper for Definition 1.8.4: the affine segment map `t ↦ x + t • h` is continuous on
`[0,1]`. -/
lemma segment_affine_map_continuousOn
    (h : WeightedSpace A) :
    ContinuousOn (fun t : ℝ ↦ x + t • h) (Set.Icc (0 : ℝ) 1) := by
  -- The line segment map is affine in the scalar parameter.
  have hseg : Continuous (fun t : ℝ ↦ x + t • h) := by
    exact
      continuous_const.add
        (continuous_id.smul (continuous_const : Continuous fun _ : ℝ ↦ h))
  exact hseg.continuousOn

/-- Helper for Definition 1.8.4: the affine gradient/Hessian model `t ↦ g + t • H h` is
continuous on `[0,1]`. -/
lemma segment_affine_model_continuousOn
    (h : WeightedSpace A) :
    ContinuousOn (fun t : ℝ ↦ g + t • H h) (Set.Icc (0 : ℝ) 1) := by
  -- The affine model depends continuously on the segment parameter.
  have hmodel : Continuous (fun t : ℝ ↦ g + t • H h) := by
    exact
      continuous_const.add
        (continuous_id.smul (continuous_const : Continuous fun _ : ℝ ↦ H h))
  exact hmodel.continuousOn

/-- Helper for Definition 1.8.4: a continuous local weighted vector field stays continuous after
pullback to a short segment and subtraction of the affine model. -/
lemma segment_model_continuousOn_of_vector_field
    {G : WeightedSpace A → WeightedSpace A}
    {r : ℝ} (hr : 0 < r)
    (hcont_nhds : ContinuousOn G (Metric.ball x r))
    {h : WeightedSpace A} (hh : ‖h‖ < r) :
    ContinuousOn (fun t : ℝ ↦ G (x + t • h) - g - t • H h) (Set.Icc (0 : ℝ) 1) := by
  -- Route correction: prove the pullback continuity for a generic vector field before
  -- specializing to the notation-heavy gradient field `∇ f`.
  have hmaps :
      Set.MapsTo (fun t : ℝ ↦ x + t • h) (Set.Icc (0 : ℝ) 1) (Metric.ball x r) := by
    intro t ht
    exact segment_point_mem_ball (A := A) (x := x) hr hh ht
  have hpull :
      ContinuousOn (fun t : ℝ ↦ G (x + t • h)) (Set.Icc (0 : ℝ) 1) := by
    exact hcont_nhds.comp' (segment_affine_map_continuousOn (A := A) (x := x) h) hmaps
  have hneg_model :
      ContinuousOn (fun t : ℝ ↦ -g - t • H h) (Set.Icc (0 : ℝ) 1) := by
    -- Negating the affine model gives the additive correction term in the segment error field.
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (segment_affine_model_continuousOn (A := A) (x := x) (g := g) (H := H) h).neg
  -- Then add the negated affine comparison model to the pulled-back vector field.
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hpull.add hneg_model

/-- Helper for Definition 1.8.4: if the weighted gradient is continuous on a neighborhood ball of
`x`, then its pullback along a short affine segment is continuous at each parameter value in
`[0,1]`. -/
lemma segment_vector_field_continuousAt
    {G : WeightedSpace A → WeightedSpace A}
    {r : ℝ} (hr : 0 < r)
    (hcont_nhds : ContinuousOn G (Metric.ball x r))
    {h : WeightedSpace A} (hh : ‖h‖ < r)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ContinuousAt (fun s : ℝ ↦ G (x + s • h)) t := by
  -- Upgrade the local ball continuity at the segment point to an ordinary `ContinuousAt`.
  have hy : x + t • h ∈ Metric.ball x r :=
    segment_point_mem_ball (A := A) (x := x) hr hh ht
  have hG_at : ContinuousAt G (x + t • h) := by
    exact (hcont_nhds (x + t • h) hy).continuousAt (Metric.isOpen_ball.mem_nhds hy)
  -- Then compose with the affine segment map at the parameter `t`.
  have hseg : ContinuousAt (fun s : ℝ ↦ x + s • h) t := by
    exact
      (continuous_const.add
        (continuous_id.smul (continuous_const : Continuous fun _ : ℝ ↦ h))).continuousAt
  simpa using hG_at.comp t hseg

/-- Helper for Definition 1.8.4: if the weighted gradient is continuous on a neighborhood ball of
`x`, then its pullback along a short affine segment is continuous at each parameter value in
`[0,1]`. -/
lemma segment_raw_gradient_continuousAt
    {r : ℝ} (hr : 0 < r)
    (hcont_nhds : ContinuousOn (∇ f) (Metric.ball x r))
    {h : WeightedSpace A} (hh : ‖h‖ < r)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ContinuousAt (fun s : ℝ ↦ ∇ f (x + s • h)) t := by
  -- Feed the raw gradient into the generic vector-field segment lemma through an explicitly typed
  -- lambda, avoiding the unstable standalone packaging definition.
  change ContinuousAt
    (fun s : ℝ ↦
      (fun y : WeightedSpace A ↦ @gradient ℝ (WeightedSpace A) _ _ _ inferInstance f y)
        (x + s • h)) t
  exact
    segment_vector_field_continuousAt
      (A := A) (x := x)
      (G := fun y : WeightedSpace A ↦ @gradient ℝ (WeightedSpace A) _ _ _ inferInstance f y)
      hr hcont_nhds hh ht

/-- Helper for Definition 1.8.4: the affine-segment gradient error field is continuous on
`[0,1]` once the gradient is continuous on a neighborhood ball of `x`. -/
lemma segment_gradient_model_continuousOn
    {r : ℝ} (hr : 0 < r)
    (hcont_nhds : ContinuousOn (∇ f) (Metric.ball x r))
    {h : WeightedSpace A} (hh : ‖h‖ < r) :
    ContinuousOn (fun t : ℝ ↦ ∇ f (x + t • h) - g - t • H h) (Set.Icc (0 : ℝ) 1) := by
  -- Route correction: use the generic vector-field segment lemma directly on the explicitly typed
  -- raw gradient field.
  change
    ContinuousOn
      (fun t : ℝ ↦
        (fun y : WeightedSpace A ↦ @gradient ℝ (WeightedSpace A) _ _ _ inferInstance f y)
          (x + t • h) - g - t • H h)
      (Set.Icc (0 : ℝ) 1)
  exact
    segment_model_continuousOn_of_vector_field
      (A := A) (x := x) (g := g) (H := H)
      (G := fun y : WeightedSpace A ↦ @gradient ℝ (WeightedSpace A) _ _ _ inferInstance f y)
      hr hcont_nhds hh

/-- Helper for Definition 1.8.4: along a short weighted segment, the gradient linearization error
paired with the segment direction is continuous on `[0,1]`. -/
lemma segment_quadratic_integrand_continuous
    {r : ℝ} (hr : 0 < r)
    (hcont_nhds : ContinuousOn (∇ f) (Metric.ball x r))
    {h : WeightedSpace A} (hh : ‖h‖ < r) :
    ContinuousOn
      (fun t : ℝ ↦ (⟪∇ f (x + t • h) - g - t • H h, h⟫_[A] : ℝ))
      (Set.Icc (0 : ℝ) 1) := by
  -- Pair the continuous segment error field with the fixed direction `h`.
  exact
    weighted_segment_pair_continuousOn
      (segment_gradient_model_continuousOn
        (A := A) (f := f) (x := x) (g := g) (H := H) hr hcont_nhds hh) h

/-- Helper for Definition 1.8.4: the corrected quadratic remainder on a short weighted segment is
the integral of the gradient linearization error along that segment. -/
lemma segment_quadratic_remainder_eq_integral
    {r : ℝ} (hr : 0 < r)
    (hgrad_nhds : ∀ y ∈ Metric.ball x r, HasGradientAt f (∇ f y) y)
    (hcont_nhds : ContinuousOn (∇ f) (Metric.ball x r))
    {h : WeightedSpace A} (hh : ‖h‖ < r) :
    f (x + h) - (f x + (⟪g, h⟫_[A] : ℝ) + (1 / 2 : ℝ) * (⟪H h, h⟫_[A] : ℝ)) =
      ∫ t in 0..1, (⟪∇ f (x + t • h) - g - t • H h, h⟫_[A] : ℝ) := by
  let F : ℝ → ℝ := fun u ↦
    f (x + u • h) - f x - u * (⟪g, h⟫_[A] : ℝ) -
      (1 / 2 : ℝ) * u ^ (2 : ℕ) * (⟪H h, h⟫_[A] : ℝ)
  have hFTC :
      ∫ t in 0..1, (⟪∇ f (x + t • h) - g - t • H h, h⟫_[A] : ℝ) = F 1 - F 0 := by
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := F)
      (f' := fun t : ℝ ↦ (⟪∇ f (x + t • h) - g - t • H h, h⟫_[A] : ℝ))
      (by
        intro t ht
        have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
          simpa [Set.uIcc_of_le zero_le_one] using ht
        simpa [F] using
          segment_quadratic_remainder_hasDerivAt
            (A := A) (f := f) (x := x) (g := g) (H := H) hr hgrad_nhds hh ht')
      ((segment_quadratic_integrand_continuous
        (A := A) (f := f) (x := x) (g := g) (H := H) hr hcont_nhds hh).intervalIntegrable_of_Icc
        zero_le_one)
  have hF0 : F 0 = 0 := by
    simp [F]
  calc
    f (x + h) - (f x + (⟪g, h⟫_[A] : ℝ) + (1 / 2 : ℝ) * (⟪H h, h⟫_[A] : ℝ))
        = F 1 := by
          simp [F]
          ring
    _ = F 1 - F 0 := by rw [hF0, sub_zero]
    _ = ∫ t in 0..1, (⟪∇ f (x + t • h) - g - t • H h, h⟫_[A] : ℝ) := by
          symm
          exact hFTC

/-- Helper for Definition 1.8.4: translating the derivative of the weighted totalized gradient to
the basepoint gives the vector little-`o` remainder in displacement coordinates. -/
lemma gradient_derivative_isLittleO_at_zero
    (hg : HasGradientAt f g x)
    (hgrad : HasFDerivAt (∇ f) H x) :
    (fun k : WeightedSpace A ↦ ∇ f (x + k) - g - H k) =o[𝓝 (0 : WeightedSpace A)]
      fun k : WeightedSpace A ↦ k := by
  -- Rewrite the Fréchet derivative remainder into the translated `k ↦ x + k` model.
  simpa [hg.gradient, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (hasFDerivAt_iff_isLittleO_nhds_zero (f := ∇ f) (f' := H) (x := x)).mp hgrad

/-- Helper for Definition 1.8.4: segment scaling by a parameter in `[0,1]` does not increase the
weighted norm. -/
lemma norm_smul_le_of_mem_Icc
    {h : WeightedSpace A} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖t • h‖ ≤ ‖h‖ := by
  calc
    ‖t • h‖ = t * ‖h‖ := by
      rw [norm_smul, Real.norm_of_nonneg ht.1]
    _ ≤ ‖h‖ := by
      nlinarith [norm_nonneg h, ht.1, ht.2]

/-- Helper for Definition 1.8.4: the derivative remainder of the weighted totalized gradient is
uniformly controlled along scaled segments once the displacement is sufficiently small. -/
lemma littleO_bound_on_scaled_segment
    (hg : HasGradientAt f g x)
    (hgrad : HasFDerivAt (∇ f) H x) :
    ∀ ε > 0,
      ∀ᶠ h : WeightedSpace A in 𝓝 (0 : WeightedSpace A),
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          ‖∇ f (x + t • h) - g - H (t • h)‖ ≤ ε * ‖t • h‖ := by
  -- TODO: re-express the eventual set using an elaboration-stable gradient-field wrapper so the
  -- neighborhood argument on `t • h` does not generate hidden `CompleteSpace` instance side-goals.
  sorry

/-- Helper for Definition 1.8.4: the Fréchet derivative of the weighted totalized gradient gives a
uniform `ε * t * ‖h‖²` bound for the segment integrand once `h` is small. -/
lemma gradient_linearization_on_segment_abs_le
    (hg : HasGradientAt f g x)
    (hgrad : HasFDerivAt (∇ f) H x) :
    ∀ ε > 0,
      ∀ᶠ h : WeightedSpace A in 𝓝 (0 : WeightedSpace A),
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          |(⟪∇ f (x + t • h) - g - t • H h, h⟫_[A] : ℝ)| ≤ ε * t * ‖h‖ ^ (2 : ℕ) := by
  -- TODO: once `littleO_bound_on_scaled_segment` is stabilized, rewrite `H (t • h) = t • H h`
  -- and combine the vector estimate with `norm_inner_le_norm`.
  sorry

/-- Helper for Definition 1.8.4: a genuine local weighted gradient field together with the
Fréchet derivative of that field at the basepoint gives the source-facing weighted quadratic
expansion. -/
lemma weighted_second_order_of_local_gradient_field
    {r : ℝ} (hr : 0 < r)
    (hgrad_nhds : ∀ y ∈ Metric.ball x r, HasGradientAt f (∇ f y) y)
    (hcont_nhds : ContinuousOn (∇ f) (Metric.ball x r))
    (hg : HasGradientAt f g x)
    (hgrad : HasFDerivAt (∇ f) H x) :
    HasWeightedGradientSecondOrderExpansionAt A f g H x := by
  -- TODO: combine the proved FTC remainder identity with the eventual scalar segment estimate from
  -- `gradient_linearization_on_segment_abs_le`, then integrate `t` over `[0,1]`.
  sorry

/-- The auxiliary quadratic expansion only depends on the adjoint average of the operator in the
quadratic term. -/
theorem iff_adjointAverage :
    HasWeightedGradientSecondOrderExpansionAt A f g H x ↔
      HasWeightedGradientSecondOrderExpansionAt A f g ((1 / 2 : ℝ) • (H + H.adjoint)) x := by
  let Hsymm : WeightedSpace A →L[ℝ] WeightedSpace A := ((1 / 2 : ℝ) • (H + H.adjoint))
  -- Replace the quadratic term pointwise by its adjoint-average representative.
  have hquad :
      ∀ h : WeightedSpace A, (⟪Hsymm h, h⟫_[A] : ℝ) = (⟪H h, h⟫_[A] : ℝ) := by
    intro h
    simpa [Hsymm] using quadratic_form_adjointAverage_eq (A := A) (H := H) h
  constructor <;> intro hExp
  · convert hExp using 1
    ext h
    simp [HasWeightedGradientSecondOrderExpansionAt, Hsymm, hquad h]
  · convert hExp using 1
    ext h
    simp [HasWeightedGradientSecondOrderExpansionAt, Hsymm, hquad h]

/-- Helper for Definition 1.8.4: along a fixed weighted line, the quadratic norm
`‖t • d‖[A]^2` is bounded by a constant multiple of `t^2`. -/
lemma line_norm_square_isBigO_square
    (d : WeightedSpace A) :
    (fun t : ℝ ↦ (‖t • d‖[A] : ℝ) ^ (2 : ℕ)) =O[𝓝 (0 : ℝ)] fun t ↦ t ^ (2 : ℕ) := by
  -- Pull the constant direction norm out of the quadratic scaling relation `‖t • d‖ = |t| ‖d‖`.
  refine Asymptotics.IsBigO.of_bound (‖d‖ ^ (2 : ℕ)) ?_
  filter_upwards [Filter.Eventually.of_forall fun t : ℝ ↦ ?_] with t
  calc
    ‖((‖t • d‖[A] : ℝ) ^ (2 : ℕ))‖ = (‖t • d‖[A] : ℝ) ^ (2 : ℕ) := by
      rw [Real.norm_of_nonneg]
      positivity
    _ = (|t| * ‖d‖) ^ (2 : ℕ) := by
      rw [norm_smul, Real.norm_eq_abs]
    _ = ‖d‖ ^ (2 : ℕ) * ‖t ^ (2 : ℕ)‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)]
      ring

/-- Helper for Definition 1.8.4: evaluating the weighted quadratic model on a line rewrites the
source remainder into the scalar line-restriction form. -/
lemma line_model_apply
    (d : WeightedSpace A) (t : ℝ) :
    f (x + t • d) -
        (f x
          + t * (⟪g, d⟫_[A] : ℝ)
          + (1 / 2 : ℝ) * t ^ (2 : ℕ) * (⟪H d, d⟫_[A] : ℝ)) =
      ((fun h : WeightedSpace A ↦
          f (x + h) -
            (f x
              + (⟪g, h⟫_[A] : ℝ)
              + (1 / 2 : ℝ) * (⟪H h, h⟫_[A] : ℝ)))
        (t • d)) := by
  -- Expand the line parameter through the linear and quadratic pieces of the model.
  simp only
  have hg_line : (⟪g, t • d⟫_[A] : ℝ) = t * (⟪g, d⟫_[A] : ℝ) := by
    simpa [Matrix.PosDef.weightedInner] using (real_inner_smul_right g d t)
  have hH_line : (⟪H (t • d), t • d⟫_[A] : ℝ) = t ^ (2 : ℕ) * (⟪H d, d⟫_[A] : ℝ) := by
    rw [ContinuousLinearMap.map_smul]
    rw [show (⟪t • H d, t • d⟫_[A] : ℝ) = t * (⟪t • H d, d⟫_[A] : ℝ) by
      simpa [Matrix.PosDef.weightedInner] using (real_inner_smul_right (t • H d) d t)]
    rw [show (⟪t • H d, d⟫_[A] : ℝ) = t * (⟪H d, d⟫_[A] : ℝ) by
      simpa [Matrix.PosDef.weightedInner] using (real_inner_smul_left d (H d) t)]
    ring
  rw [hg_line, hH_line]
  ring

/-- Helper for Definition 1.8.4: restricting the weighted quadratic expansion to a fixed line
records the textbook quadratic coefficient `⟪H d, d⟫_[A]`. -/
lemma line_restriction_has_weighted_second_order_expansion
    (hExp : HasWeightedGradientSecondOrderExpansionAt A f g H x) :
    ∀ d : WeightedSpace A,
      (fun t : ℝ ↦
        f (x + t • d) -
          (f x
            + t * (⟪g, d⟫_[A] : ℝ)
            + (1 / 2 : ℝ) * t ^ (2 : ℕ) * (⟪H d, d⟫_[A] : ℝ))) =o[𝓝 (0 : ℝ)]
        fun t ↦ t ^ (2 : ℕ) := by
  intro d
  let line : ℝ → WeightedSpace A := fun t ↦ t • d
  -- Compose the source-facing expansion with the affine line `t ↦ t • d`.
  have hline : Filter.Tendsto line (𝓝 (0 : ℝ)) (𝓝 (0 : WeightedSpace A)) := by
    simpa [line] using
      ((continuous_id.smul (continuous_const : Continuous fun _ : ℝ ↦ d)).tendsto (0 : ℝ))
  have hcomp := hExp.comp_tendsto hline
  -- Then replace the line norm by its scalar quadratic representative `t^2`.
  have hmain := hcomp.trans_isBigO (line_norm_square_isBigO_square (A := A) d)
  have hrewrite :
      (fun t : ℝ ↦
        f (x + t • d) -
          (f x
            + t * (⟪g, d⟫_[A] : ℝ)
            + (1 / 2 : ℝ) * t ^ (2 : ℕ) * (⟪H d, d⟫_[A] : ℝ))) =ᶠ[𝓝 (0 : ℝ)]
        ((fun h : WeightedSpace A ↦
          f (x + h) -
            (f x
              + (⟪g, h⟫_[A] : ℝ)
              + (1 / 2 : ℝ) * (⟪H h, h⟫_[A] : ℝ))) ∘ line) := by
    -- Rewrite the linear and quadratic terms on the line using bilinearity and linearity of `H`.
    refine Filter.Eventually.of_forall ?_
    intro t
    simpa [Function.comp_apply, line] using line_model_apply (A := A) (f := f) (x := x)
      (g := g) (H := H) d t
  exact hrewrite.trans_isLittleO hmain

/-- Helper for Definition 1.8.4: packaging the honest local-gradient-field hypotheses as a single
implication gives a direct source-facing wrapper theorem. -/
theorem hasWeightedGradientSecondOrderExpansionAt_of_local_gradient_field
    {r : ℝ} (hr : 0 < r)
    (hgrad_nhds : ∀ y ∈ Metric.ball x r, HasGradientAt f (∇ f y) y)
    (hcont_nhds : ContinuousOn (∇ f) (Metric.ball x r)) :
    ((@HasGradientAt ℝ (WeightedSpace A) inferInstance inferInstance inferInstance inferInstance
        f g x) ∧
      HasFDerivAt (∇ f) H x) →
      HasWeightedGradientSecondOrderExpansionAt A f g H x := by
  -- TODO: once `weighted_second_order_of_local_gradient_field` is completed, unwrap the pair of
  -- hypotheses and apply it directly here.
  sorry

end HasWeightedGradientSecondOrderExpansionAt

end

end

/-! ### Lemma_1_8_5 (from Chap01) -/
open Matrix
open scoped MatrixOrder MatrixPosDef

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Coord" => Fin n → ℝ
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "coordEquiv" => EuclideanSpace.equiv (Fin n) ℝ

/- Lemma 1.8.5 lies in finite-dimensional weighted Euclidean geometry.

Primary domain:
- equivalence of the identity-matrix norm and the weighted norm induced by a positive-definite
  matrix on `ℝⁿ`

Source/core/bridge triage:
- source-facing: the two-sided comparison between the identity owner norm and the weighted norm
  owner on the coordinate model `Coord`
- core/canonical: the two norm owners on `Coord`,
  `toNormedAddCommGroup (1 : Mat) PosDef.one` and `toNormedAddCommGroup A hA`
- bridge/view: `coordEquiv` together with
  `Matrix.PosDef.norm_coordEquiv_eq_sqrt_inner_toEuclideanLin`

Sampled owner-style declarations:
- `toNormedAddCommGroup`
- `Matrix.PosDef.norm_coordEquiv_eq_sqrt_inner_toEuclideanLin`
- `EuclideanSpace.equiv`
- `LinearMap.continuous_of_finiteDimensional`

Best owner abstraction:
- compare the weighted norm owner attached to `A` directly against the identity-matrix norm owner
  on `Coord`

Primitive data:
- `A : Mat`
- `hA : A.PosDef`

Derived API:
- the Euclidean bridge formula
  `‖coordEquiv x‖[⟨A, hA⟩] = Real.sqrt (inner ℝ (A.toEuclideanLin x) x)`
- the quadratic form `inner ℝ (A.toEuclideanLin x) x`

Accordingly, the main public statement stays at the source-facing owner layer on `Coord`, and the
Euclidean `Real.sqrt (inner ...)` formula is kept as a thin companion bridge rather than the main
entry.
-/

/-- Helper for Lemma 1.8.5: an invertible matrix acts by a bi-Lipschitz Euclidean linear map on
`ℝⁿ`. -/
private theorem isUnit_exists_euclidean_bounds (B : Mat) (hBunit : IsUnit B) :
    ∃ c₁ > 0, ∃ c₂ > 0,
      ∀ y : E, c₁ * ‖y‖ ≤ ‖B.toEuclideanLin y‖ ∧ ‖B.toEuclideanLin y‖ ≤ c₂ * ‖y‖ := by
  -- We bound the image from below by injectivity and from above by continuity.
  have hBinj : Function.Injective (B.toEuclideanLin : E → E) := by
    intro x y hxy
    have hcoords : B *ᵥ x.ofLp = B *ᵥ y.ofLp := by
      simpa only [Matrix.ofLp_toLpLin] using congrArg (fun z : E ↦ z.ofLp) hxy
    have hmulVec_inj : Function.Injective B.mulVec := (mulVec_injective_iff_isUnit).2 hBunit
    have hxofy : x.ofLp = y.ofLp := hmulVec_inj hcoords
    exact congrArg (WithLp.toLp 2) hxofy
  obtain ⟨K, hKpos, hanti⟩ :=
    (LinearMap.injective_iff_antilipschitz (B.toEuclideanLin : E →ₗ[ℝ] E)).mp hBinj
  let T : E →L[ℝ] E := (B.toEuclideanLin).toContinuousLinearMap
  obtain ⟨C, hCpos, hC⟩ := T.bound
  have hKpos' : 0 < (K : ℝ) := hKpos
  refine ⟨(K : ℝ)⁻¹, by positivity, C, hCpos, ?_⟩
  intro y
  constructor
  · -- Anti-Lipschitz control of `B` gives the lower comparison constant.
    have hle : ‖y‖ ≤ (K : ℝ) * ‖B.toEuclideanLin y‖ := by
      simpa [dist_eq_norm, map_zero] using hanti.le_mul_dist y 0
    exact (inv_mul_le_iff₀ hKpos').2 hle
  · -- Continuity supplies the upper comparison constant.
    simpa [T] using hC y

/-- Helper for Lemma 1.8.5: if `A = Bᵀ B`, then the `A`-weighted norm equals the Euclidean norm of
`Bx`. -/
private theorem sqrt_inner_eq_euclidean_image_norm
    (A B : Mat) (hAeq : A = Bᴴ * B) (x : E) :
    Real.sqrt (inner ℝ (A.toEuclideanLin x) x) = ‖B.toEuclideanLin x‖ := by
  -- Rewrite the quadratic form in coordinates and collapse it to the Euclidean square norm.
  have hquad : inner ℝ (A.toEuclideanLin x) x = ‖B.toEuclideanLin x‖ ^ 2 := by
    calc
      inner ℝ (A.toEuclideanLin x) x = dotProduct x.ofLp (A *ᵥ x.ofLp) := by
        simpa only [Matrix.ofLp_toLpLin] using
          (EuclideanSpace.inner_eq_star_dotProduct (A.toEuclideanLin x) x)
      _ = dotProduct x.ofLp ((Bᴴ * B) *ᵥ x.ofLp) := by rw [hAeq]
      _ = dotProduct (B *ᵥ x.ofLp) (B *ᵥ x.ofLp) := by
        rw [dotProduct_comm]
        rw [dotProduct_comm, ← mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose]
        simp
      _ = ‖B.toEuclideanLin x‖ ^ 2 := by
        have hraw :=
          EuclideanSpace.inner_eq_star_dotProduct (B.toEuclideanLin x) (B.toEuclideanLin x)
        simp only [Matrix.ofLp_toLpLin] at hraw
        have hnorm : inner ℝ (B.toEuclideanLin x) (B.toEuclideanLin x) =
            ‖B.toEuclideanLin x‖ ^ 2 := by
          simp
        exact hraw.symm.trans hnorm
  rw [hquad, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

/-- Lemma 1.8.5: the weighted norm owner induced by a positive-definite real matrix is equivalent
to the identity-matrix norm owner on `ℝⁿ`. -/
-- Proof sketch: factor `A` as `Bᵀ B`, transport the coordinate owner norms to Euclidean space by
-- `coordEquiv.symm`, and apply the bi-Lipschitz bounds for the Euclidean operator `B`.
theorem posDef_exists_weightedNorm_bounds (A : {A : Mat // A.PosDef}) :
    ∃ c₁ > 0, ∃ c₂ > 0,
      ∀ x : Coord,
        c₁ * ‖x‖[⟨(1 : Mat), PosDef.one⟩] ≤ ‖x‖[A] ∧
        ‖x‖[A] ≤ c₂ * ‖x‖[⟨(1 : Mat), PosDef.one⟩] := by
  have hAstrict : IsStrictlyPositive A.1 := A.2.isStrictlyPositive
  obtain ⟨B, hBunit, hBself, hAeq_mul⟩ :=
    (CStarAlgebra.isStrictlyPositive_iff_exists_isUnit_and_isSelfAdjoint_and_eq_mul_self).mp
      hAstrict
  have hAeq : A.1 = Bᴴ * B := by
    have hBtranspose : Bᵀ = B := by
      simpa using hBself
    calc
      A.1 = B * B := hAeq_mul
      _ = Bᵀ * B := by
        congr 1
        simpa using hBtranspose.symm
  obtain ⟨c₁, hc₁, c₂, hc₂, hbounds⟩ := isUnit_exists_euclidean_bounds B hBunit
  refine ⟨c₁, hc₁, c₂, hc₂, ?_⟩
  intro x
  let y : E := (EuclideanSpace.equiv (Fin n) ℝ).symm x
  have hy_coord : coordEquiv y = x := by
    simpa [y] using (EuclideanSpace.equiv (Fin n) ℝ).apply_symm_apply x
  have hy_id : ‖x‖[⟨(1 : Mat), PosDef.one⟩] = ‖y‖ := by
    calc
      ‖x‖[⟨(1 : Mat), PosDef.one⟩] = ‖coordEquiv y‖[⟨(1 : Mat), PosDef.one⟩] := by
        rw [hy_coord]
      _ = ‖y‖ := Matrix.PosDef.one_norm_coordEquiv_eq y
  have hy_weight : ‖x‖[A] = ‖B.toEuclideanLin y‖ := by
    calc
      ‖x‖[A] = ‖coordEquiv y‖[A] := by
        rw [hy_coord]
      _ = Real.sqrt (inner ℝ (A.1.toEuclideanLin y) y) := by
        exact Matrix.PosDef.norm_coordEquiv_eq_sqrt_inner_toEuclideanLin A y
      _ = ‖B.toEuclideanLin y‖ := by
        exact sqrt_inner_eq_euclidean_image_norm A.1 B hAeq y
  obtain ⟨hlower, hupper⟩ := hbounds y
  constructor
  · calc
      c₁ * ‖x‖[⟨(1 : Mat), PosDef.one⟩] = c₁ * ‖y‖ := by
        rw [hy_id]
      _ ≤ ‖B.toEuclideanLin y‖ := hlower
      _ = ‖x‖[A] := hy_weight.symm
  · calc
      ‖x‖[A] = ‖B.toEuclideanLin y‖ := hy_weight
      _ ≤ c₂ * ‖y‖ := hupper
      _ = c₂ * ‖x‖[⟨(1 : Mat), PosDef.one⟩] := by
        rw [hy_id]

/-- Lemma 1.8.5 companion: transporting the weighted norm owner through `EuclideanSpace.equiv`
rewrites the owner comparison as the textbook bound
`c₁ ‖x‖ ≤ √⟪Ax, x⟫ ≤ c₂ ‖x‖`. -/
-- Proof sketch: apply the owner theorem to `coordEquiv x` and rewrite the weighted owner norm by
-- `Matrix.PosDef.norm_coordEquiv_eq_sqrt_inner_toEuclideanLin`.
theorem posDef_exists_sqrt_inner_bounds (A : Mat) (hA : A.PosDef) :
    ∃ c₁ > 0, ∃ c₂ > 0,
      ∀ x : E,
        c₁ * ‖x‖ ≤ Real.sqrt (inner ℝ (A.toEuclideanLin x) x) ∧
          Real.sqrt (inner ℝ (A.toEuclideanLin x) x) ≤ c₂ * ‖x‖ := by
  obtain ⟨c₁, hc₁, c₂, hc₂, hcoord⟩ := posDef_exists_weightedNorm_bounds ⟨A, hA⟩
  refine ⟨c₁, hc₁, c₂, hc₂, ?_⟩
  intro x
  simpa [Matrix.PosDef.one_norm_coordEquiv_eq x,
    Matrix.PosDef.norm_coordEquiv_eq_sqrt_inner_toEuclideanLin ⟨A, hA⟩ x] using
    hcoord (coordEquiv x)

/-- Lemma 1.8.5 companion: equivalently, the weighted quadratic form `⟪Ax, x⟫` of a
positive-definite real matrix is bounded above and below by positive multiples of the Euclidean
square norm. -/
-- Proof sketch: apply `posDef_exists_sqrt_inner_bounds` and square the two inequalities.
theorem posDef_exists_quadraticForm_bounds (A : Mat) (hA : A.PosDef) :
    ∃ m > 0, ∃ M > 0,
      ∀ x : E,
        m * ‖x‖ ^ 2 ≤ inner ℝ (A.toEuclideanLin x) x ∧
          inner ℝ (A.toEuclideanLin x) x ≤ M * ‖x‖ ^ 2 := by
  obtain ⟨c₁, hc₁, c₂, hc₂, hbounds⟩ := posDef_exists_sqrt_inner_bounds A hA
  refine ⟨c₁ ^ 2, by positivity, c₂ ^ 2, by positivity, ?_⟩
  intro x
  obtain ⟨hlower, hupper⟩ := hbounds x
  -- The quadratic form is nonnegative because `A` is positive semidefinite.
  have hq_nonneg : 0 ≤ inner ℝ (A.toEuclideanLin x) x := by
    have hcoords : 0 ≤ dotProduct x.ofLp (A *ᵥ x.ofLp) := by
      simpa [dotProduct_comm] using hA.posSemidef.dotProduct_mulVec_nonneg x.ofLp
    have hraw := EuclideanSpace.inner_eq_star_dotProduct (A.toEuclideanLin x) x
    simp only [Matrix.ofLp_toLpLin] at hraw
    simpa [hraw, dotProduct_comm] using hcoords
  have hleft_nonneg : 0 ≤ c₁ * ‖x‖ := by
    positivity
  have hright_nonneg : 0 ≤ c₂ * ‖x‖ := by
    positivity
  -- Squaring the lower norm bound produces the lower quadratic-form bound.
  have hlower_sq : (c₁ * ‖x‖) ^ 2 ≤ inner ℝ (A.toEuclideanLin x) x := by
    have habs : |c₁ * ‖x‖| ≤ |Real.sqrt (inner ℝ (A.toEuclideanLin x) x)| := by
      simpa [abs_of_nonneg hleft_nonneg, abs_of_nonneg (Real.sqrt_nonneg _)] using hlower
    have hsquare : (c₁ * ‖x‖) ^ 2 ≤ (Real.sqrt (inner ℝ (A.toEuclideanLin x) x)) ^ 2 :=
      (sq_le_sq).2 habs
    simpa [Real.sq_sqrt hq_nonneg] using hsquare
  -- Squaring the upper norm bound produces the upper quadratic-form bound.
  have hupper_sq : inner ℝ (A.toEuclideanLin x) x ≤ (c₂ * ‖x‖) ^ 2 := by
    have habs : |Real.sqrt (inner ℝ (A.toEuclideanLin x) x)| ≤ |c₂ * ‖x‖| := by
      simpa [abs_of_nonneg hright_nonneg, abs_of_nonneg (Real.sqrt_nonneg _)] using hupper
    have hsquare : (Real.sqrt (inner ℝ (A.toEuclideanLin x) x)) ^ 2 ≤ (c₂ * ‖x‖) ^ 2 :=
      (sq_le_sq).2 habs
    simpa [Real.sq_sqrt hq_nonneg] using hsquare
  constructor
  · simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hlower_sq
  · simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hupper_sq
