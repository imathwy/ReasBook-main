import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Definition_4_1_3
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Definition_4_2_12
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Definition_4_3_4

-- Declarations for this item will be appended below by the statement pipeline.

open LinearMap (BilinForm)
open LinearMap.BilinForm
open scoped Gradient ConstrainedArgmin BInducedNorm

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 4.3.6 lies in the bilinear-form-induced norm / cubic-Newton-step domain on complete
real inner-product spaces.

Sampled owner-style declarations:
* `LinearMap.BilinForm.primalSeminorm` in `Definition_4_3_4`, the canonical owner of the
  `B`-induced norm `‖·‖[B]`;
* `secondOrderTaylorModelAt` in `Definition_4_1_3`, the canonical owner of the quadratic Taylor
  part of the local model;
* `CubicRegularizationMapping` in `Definition_4_2_12`, the earlier ambient-norm cubic-step owner,
  which becomes the specific comparison owner once the `B`-norm agrees with the ambient norm;
* `IsMinOn` and `argmin[Set.univ]`, the canonical global-minimizer owners on the ambient space.

Best owner abstraction:
* source-facing: the `B`-dependent cubic Newton model and the chosen step map `T_M`;
* core/canonical: `secondOrderTaylorModelAt f x` together with the `B`-induced norm
  `‖·‖[B]`;
* bridge/view: the canonical whole-space argmin membership of the chosen step values, and the
  specialization bridge to `CubicRegularizationMapping` when `B.primalSeminorm = normSeminorm`.

Primitive data:
* the bilinear form `B`;
* the objective `f`;
* the regularization parameter `M`;
* the chosen step map `T_M`.

Derived API:
* the displayed cubic Newton model with cubic term measured in the `B`-norm;
* the whole-space minimizing property of `T_M x`;
* the residual `r_M(x) = ‖T_M(x) - x‖[B]`.

Section 4.3 uses the geometry induced by `B`, so the source-facing owner cannot be collapsed to
the earlier ambient-inner-product owner `CubicRegularizationMapping`. This file therefore keeps
the `B`-dependent step layer as the public owner and derives its API directly from the canonical
Taylor-model and `B`-norm owners, while exposing a thin `toCubicRegularizationMapping` bridge for
the ambient-norm specialization. -/

/-- The cubic Newton model from Definition 4.3.6: the second-order Taylor model of `f` at `x`,
with the constant term `f x` removed and the cubic penalty measured in the `B`-induced norm. -/
def cubicNewtonModel
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef]
    (f : E → ℝ) (M : ℝ) (x : E) : E → ℝ :=
  fun T ↦ secondOrderTaylorModelAt f x T - f x + (M / 6 : ℝ) * ‖T - x‖[B] ^ (3 : ℕ)

/-- Evaluating `cubicNewtonModel B f M x` recovers the displayed cubic Newton model formula from
Definition 4.3.6. -/
theorem cubicNewtonModel_apply
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef]
    (f : E → ℝ) (M : ℝ) (x T : E) :
    cubicNewtonModel B f M x T =
      inner ℝ (∇ f x) (T - x) +
        (1 / 2 : ℝ) * inner ℝ (hessian f x (T - x)) (T - x) +
          (M / 6 : ℝ) * ‖T - x‖[B] ^ (3 : ℕ) := by
  simp [cubicNewtonModel, secondOrderTaylorModelAt_apply]
  ring

/-- If the `B`-induced seminorm owner is the ambient norm seminorm, then the `B`-dependent cubic
Newton model is exactly the earlier chapter cubic-regularization model shifted by the harmless
constant `-f x`. -/
theorem cubicNewtonModel_eq_cubicRegularizationQuadraticApproximation_sub
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef]
    (hNorm : B.primalSeminorm Fact.out = normSeminorm ℝ E)
    (f : E → ℝ) (M : ℝ) (x : E) :
    cubicNewtonModel B f M x =
      fun y ↦ cubicRegularizationQuadraticApproximation f M x y - f x := by
  funext y
  have hB : ‖y - x‖[B] = ‖y - x‖ := by
    simpa using
      congrArg (fun p : Seminorm ℝ E ↦ p (y - x)) hNorm
  rw [cubicNewtonModel_apply, cubicRegularizationQuadraticApproximation_apply, hB]
  simp [sub_eq_add_neg]
  ring

/-- Under the ambient-norm specialization `B.primalSeminorm = normSeminorm`, minimizing the
`B`-dependent cubic Newton model is equivalent to minimizing the earlier chapter cubic model. -/
theorem isMinOn_cubicNewtonModel_iff
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef]
    (hNorm : B.primalSeminorm Fact.out = normSeminorm ℝ E)
    (f : E → ℝ) (M : ℝ) (x y : E) :
    IsMinOn (cubicNewtonModel B f M x) Set.univ y ↔
      IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ y := by
  rw [cubicNewtonModel_eq_cubicRegularizationQuadraticApproximation_sub B hNorm f M x]
  constructor
  · intro hy
    rw [isMinOn_iff] at hy ⊢
    intro z hz
    have hz' := hy z hz
    linarith
  · intro hy
    rw [isMinOn_iff] at hy ⊢
    intro z hz
    have hz' := hy z hz
    linarith

/-- Definition 4.3.6: a cubic Newton step for the `B`-induced geometry is a map `T_M : E → E`
such that, for every base point `x`, the value `T_M x` globally minimizes the `B`-dependent cubic
Newton model centered at `x`. -/
structure CubicNewtonStep
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef]
    (f : E → ℝ) (M : ℝ) where
  /-- The chosen cubic Newton step map `T_M`. -/
  toFun : E → E
  /-- For each base point `x`, the step `T_M x` globally minimizes the `B`-dependent cubic Newton
  model centered at `x`. -/
  isMinOn (x : E) :
    IsMinOn (cubicNewtonModel B f M x) Set.univ (toFun x)

namespace CubicNewtonStep

variable {B : BilinForm ℝ E} [Fact B.toQuadraticMap.PosDef] {f : E → ℝ} {M : ℝ}

/-- A cubic Newton step acts on a base point by evaluation of its chosen map `T_M`. -/
instance : CoeFun (CubicNewtonStep B f M) (fun _ ↦ E → E) where
  coe step := step.toFun

/-- Evaluating a cubic Newton step at `x` gives a global minimizer of the `B`-dependent cubic
Newton model centered at `x`. -/
theorem isMinOn_apply
    (step : CubicNewtonStep B f M) (x : E) :
    IsMinOn (cubicNewtonModel B f M x) Set.univ (step x) :=
  step.isMinOn x

/-- Evaluating a cubic Newton step at `x` gives a point of the canonical whole-space argmin set
of the `B`-dependent cubic Newton model centered at `x`. -/
theorem mem_argmin_apply
    (step : CubicNewtonStep B f M) (x : E) :
    step x ∈ argmin[Set.univ] (cubicNewtonModel B f M x) := by
  exact mem_constrainedArgmin_iff.mpr ⟨by simp, step.isMinOn_apply x⟩

/-- The cubic Newton point `T_M(x)` satisfies the canonical first-order optimality condition for
the `B`-dependent cubic Newton model centered at `x`. -/
theorem firstOrderOptimalityCondition
    (step : CubicNewtonStep B f M) (x : E) :
    fderiv ℝ (cubicNewtonModel B f M x) (step x) = 0 := by
  simpa using IsLocalMin.fderiv_eq_zero ((step.isMinOn_apply x).isLocalMin (by simp))

/-- The residual function `r_M(x) = ‖T_M(x) - x‖[B]` attached to a cubic Newton step. -/
def residual (step : CubicNewtonStep B f M) : E → ℝ :=
  fun x ↦ ‖step x - x‖[B]

/-- If the `B`-induced norm agrees with the ambient norm, a cubic Newton step specializes to the
earlier chapter cubic-regularization owner with the same chosen step map. -/
def toCubicRegularizationMapping
    (step : CubicNewtonStep B f M)
    (hNorm : B.primalSeminorm Fact.out = normSeminorm ℝ E) :
    CubicRegularizationMapping f M where
  toFun := step
  isMinOn x := (isMinOn_cubicNewtonModel_iff B hNorm f M x (step x)).1 (step.isMinOn_apply x)

/-- The specialization bridge to `CubicRegularizationMapping` keeps the same step values. -/
@[simp] theorem toCubicRegularizationMapping_apply
    (step : CubicNewtonStep B f M)
    (hNorm : B.primalSeminorm Fact.out = normSeminorm ℝ E)
    (x : E) :
    step.toCubicRegularizationMapping hNorm x = step x :=
  rfl

end CubicNewtonStep

scoped[CubicNewtonStepNotation] notation:max "r[" step:arg "]" =>
  CubicNewtonStep.residual step

scoped[CubicNewtonStepNotation] notation:max "r[" step:arg "](" x:arg ")" =>
  CubicNewtonStep.residual step x

namespace CubicNewtonStep

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {B : BilinForm ℝ E} [Fact B.toQuadraticMap.PosDef] {f : E → ℝ} {M : ℝ}

open scoped CubicNewtonStepNotation

/-- Evaluating `r[step](x)` recovers the textbook quantity `r_M(x) = ‖T_M(x) - x‖[B]`. -/
@[simp] theorem residual_apply
    (step : CubicNewtonStep B f M) (x : E) :
    r[step](x) = ‖step x - x‖[B] :=
  rfl

end CubicNewtonStep
