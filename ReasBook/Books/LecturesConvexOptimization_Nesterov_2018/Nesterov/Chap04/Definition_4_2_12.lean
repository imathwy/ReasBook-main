import LecturesConvexOptimization_Nesterov_2018.Chap01.Definition_1_4_16
import LecturesConvexOptimization_Nesterov_2018.Chap04.Definition_4_1_3
import LecturesConvexOptimization_Nesterov_2018.Chap04.Text_4_2_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient
open scoped ConstrainedArgmin
open scoped CubicRegularizationResidual
open scoped CubicRegularizationModelNotation

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 4.2.12 lies in the cubic-regularization / unconstrained minimizer domain on
complete real inner-product spaces.

Sampled owner-style declarations:
* `cubicRegularizationQuadraticApproximation` in `Definition_4_1_3`, the chapter owner of the
  cubic model `y ↦ f₂(x; y) + (M / 6) ‖y - x‖³`;
* `IsMinOn` in mathlib, the canonical global-minimizer owner on the ambient space;
* `argmin[Set.univ]` in `Chap01/Definition_1_3_3`, the set-valued constrained-argmin bridge built
  from feasibility and `IsMinOn`;
* `hessian` in `Chap01/Definition_1_4_16`, the intrinsic Hessian operator used in the displayed
  stationarity equation;
* `CubicNewtonEstimatingSequence.x_isMin` in `Definition_4_2_14`, a nearby source-facing owner
  that also stores chosen whole-space minimizers through `IsMinOn`.

Source/core/bridge triage:
* source-facing: the cubic regularization mapping `T_M : E → E`;
* core/canonical: the chosen-minimizer owner
  `IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ (T_M x)`;
* bridge/view: membership in `argmin[Set.univ] (cubicRegularizationQuadraticApproximation f M x)`
  and the first-order optimality equation for the value `T_M x`.

Primitive data:
* the objective `f`;
* the regularization parameter `M`;
* the chosen map `T_M`.

Derived API:
* the canonical whole-space minimizer relation for `T_M x`;
* membership of `T_M x` in the cubic-model argmin set;
* the stationarity equation under the primitive self-adjointness condition on `hessian f x`,
  and hence under the canonical `C²` bridge
  `hessian_isSelfAdjoint_of_contDiffAt`
  `∇ f(x) + ∇² f(x)(T_M(x) - x) + (M / 2) ‖T_M(x) - x‖ (T_M(x) - x) = 0`.

Positivity of `M` is not primitive data of the owner here: it matters only in separate existence /
coercivity results for the cubic model, not in the definition of a chosen minimizer map once the
argmin property is already supplied.

This file therefore keeps the source-facing owner as a chosen map together with its canonical
whole-space minimizer property, while reusing `argmin[Set.univ]` only as the derived set-valued
bridge exposed elsewhere in the chapter. -/

/- Definition 4.2.12: a cubic regularization mapping for `f` with parameter `M` is a map
`T_M : E → E` such that, for every base point `x`, the value `T_M x` globally minimizes the cubic
model
`cubicRegularizationQuadraticApproximation f M x = (y ↦ f₂(x; y) + (M / 6) ‖y - x‖^3)`. -/
structure CubicRegularizationMapping (f : E → ℝ) (M : ℝ) where
  /-- The cubic regularization map `T_M`. -/
  toFun : E → E
  /-- For each base point `x`, `T_M x` globally minimizes the cubic model centered at `x`. -/
  isMinOn (x : E) :
    IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ (toFun x)

namespace CubicRegularizationMapping

variable {f : E → ℝ} {M : ℝ}

/-- A cubic regularization mapping acts on a base point by evaluation of its underlying map. -/
instance : CoeFun (CubicRegularizationMapping f M) (fun _ ↦ E → E) where
  coe T := T.toFun

-- Proof sketch: this is exactly the `isMinOn` field of the structure.
/-- Evaluating a cubic regularization mapping at `x` gives a global minimizer of
`cubicRegularizationQuadraticApproximation f M x`. -/
theorem isMinOn_apply
    (T : CubicRegularizationMapping f M) (x : E) :
    IsMinOn (m[f; M](x)) Set.univ (T x) :=
  T.isMinOn x

-- Proof sketch: combine `isMinOn_apply` with `mem_constrainedArgmin_iff`, using that the feasible
-- set is `Set.univ`.
/-- Evaluating a cubic regularization mapping at `x` gives a point of the canonical whole-space
argmin set of the cubic model centered at `x`. -/
theorem mem_argmin_apply
    (T : CubicRegularizationMapping f M) (x : E) :
    T x ∈ argmin[Set.univ] (m[f; M](x)) := by
  exact mem_constrainedArgmin_iff.mpr ⟨by simp, T.isMinOn_apply x⟩

/-- The residual function `r_M` attached to a cubic regularization mapping. -/
def residual (T : CubicRegularizationMapping f M) : E → ℝ :=
  fun x ↦ r[T x] x

/-- Evaluating `T.residual` recovers the textbook formula `r_M(x) = ‖T_M(x) - x‖`. -/
@[simp] theorem residual_apply
    (T : CubicRegularizationMapping f M) (x : E) :
    T.residual x = ‖T x - x‖ := by
  simp [residual, norm_sub_rev]

end CubicRegularizationMapping

-- Proof sketch: apply the first-order optimality condition for a global minimizer of
-- `cubicRegularizationQuadraticApproximation f M x`; when `hessian f x` is self-adjoint, the
-- derivative of the quadratic term is `hessian f x (y - x)`, while the cubic term contributes
-- `((M / 2) * ‖y - x‖) • (y - x)`.
/-- If `hessian f x` is self-adjoint, then a global minimizer of the cubic model centered at `x`
satisfies the textbook stationarity equation. -/
theorem cubicRegularization_firstOrderOptimalityCondition_of_isMinOn_of_isSelfAdjoint
    {x y : E}
    (hH : IsSelfAdjoint (hessian f x))
    (hy : IsMinOn (m[f; M](x)) Set.univ y) :
    ∇ f x + hessian f x (y - x) + ((M / 2 : ℝ) * ‖y - x‖) • (y - x) = 0 := sorry

-- Proof sketch: first obtain self-adjointness of `hessian f x` from
-- `hessian_isSelfAdjoint_of_contDiffAt`, then apply the self-adjoint owner theorem above.
/-- If `f` is `C²` at `x`, then a global minimizer of the cubic model centered at `x` satisfies
the textbook stationarity equation. -/
theorem cubicRegularization_firstOrderOptimalityCondition_of_isMinOn
    {x y : E}
    (hf : ContDiffAt ℝ 2 f x)
    (hy : IsMinOn (m[f; M](x)) Set.univ y) :
    ∇ f x + hessian f x (y - x) + ((M / 2 : ℝ) * ‖y - x‖) • (y - x) = 0 := by
  exact cubicRegularization_firstOrderOptimalityCondition_of_isMinOn_of_isSelfAdjoint
    (hessian_isSelfAdjoint_of_contDiffAt f x hf) hy

/-- If `f` is `C²` at `x`, then any point of `argmin[Set.univ] (m[f; M](x))` satisfies the
textbook stationarity equation for the cubic model centered at `x`. -/
theorem cubicRegularization_firstOrderOptimalityCondition_of_mem_argmin
    {x y : E}
    (hf : ContDiffAt ℝ 2 f x)
    (hy : y ∈ argmin[Set.univ] (m[f; M](x))) :
    ∇ f x + hessian f x (y - x) + ((M / 2 : ℝ) * ‖y - x‖) • (y - x) = 0 := by
  exact cubicRegularization_firstOrderOptimalityCondition_of_isMinOn
    hf (mem_constrainedArgmin_iff.mp hy).2

namespace CubicRegularizationMapping

-- Proof sketch: combine `T.isMinOn_apply x` with the `C²` stationarity theorem
-- `cubicRegularization_firstOrderOptimalityCondition_of_isMinOn`.
/-- If `f` is `C²` at `x`, then the cubic-regularization point `T x` satisfies the textbook
stationarity equation for the cubic model centered at `x`. -/
theorem firstOrderOptimalityCondition
    (T : CubicRegularizationMapping f M) (x : E) (hf : ContDiffAt ℝ 2 f x) :
    ∇ f x + hessian f x (T x - x) + ((M / 2 : ℝ) * ‖T x - x‖) • (T x - x) = 0 :=
  cubicRegularization_firstOrderOptimalityCondition_of_isMinOn hf (T.isMinOn_apply x)

end CubicRegularizationMapping
