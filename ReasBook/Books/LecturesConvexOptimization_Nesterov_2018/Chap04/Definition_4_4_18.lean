import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap04.Definition_4_4_4
import LecturesConvexOptimization_Nesterov_2018.Chap04.Definition_4_4_11
import LecturesConvexOptimization_Nesterov_2018.Chap04.Proposition_4_4_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Metric
open scoped InnerProduct
open scoped ModifiedGaussNewtonLocalModelNotation

universe u v

/- Definition 4.4.18 lies in the modified Gauss--Newton optimal-value / strong-dual norm-duality
domain.

Sampled owner-style declarations:
* `modifiedGaussNewtonOptimalValueAt` in `Proposition_4_4_6`, the chapter owner for the
  whole-space quadratic-regularized optimal value;
* `modifiedGaussNewtonLocalModel` in `Definition_4_4_11`, the chapter owner for the affine
  residual model;
* `quadraticallyRegularizedObjective` in `Chap01/Definition_1_4_17`, the project owner for the
  centered quadratic penalty inside that optimal-value owner;
* `dual_norm_eq_sSup_closedUnitBall` in `Definition_4_4_4`, the chapter bridge expressing the
  strong-dual norm as a support function of the closed unit ball;
* `ContinuousLinearMap.comp` in mathlib, the canonical owner for precomposing a strong-dual
  functional with a continuous linear map;
* `InnerProductSpace.toDual` in mathlib, the Chapter 4 bridge from Hilbert-space vectors to the
  intrinsic strong dual.

Best owner abstraction:
* core/canonical: `modifiedGaussNewtonOptimalValueAt (ψ[F; norm; J]) x`

Source/core/bridge triage:
* source-facing: the specialized auxiliary value `f_M(x)` for the norm merit and its dual-ball
  formula;
* core/canonical: the Chapter 4 optimal-value owner above;
* bridge/view: the step-variable expansion, the strong-dual closed-ball objective, and the
  Hilbert-space `toDual` specialization.

Primitive data:
* a residual map `F`;
* a Jacobian family `J`;
* a base point `x`.

Derived API:
* the step-variable `sInf` expansion of the canonical owner;
* the positive-parameter dual objective over the closed unit ball in the strong dual;
* the `toDual` specialization recovering the textbook adjoint formula on Hilbert-space vectors.

This refinement deletes the duplicate local `ℝ`-valued infimum owner and reuses the Chapter 4
canonical owner directly. The file now keeps only the norm-specific bridge API. -/

variable {E₁ : Type u} {E₂ : Type v}

section AuxiliaryValue

variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

variable (F : E₁ → E₂) (J : E₁ → E₁ →L[ℝ] E₂) (x : E₁)

/- Definition 4.4.18: the specialized auxiliary value `f_M(x)` for the merit `u ↦ ‖u‖` is the
canonical Chapter 4 optimal-value owner specialized to the norm local model. -/
set_option linter.hashCommand false in
#check (modifiedGaussNewtonOptimalValueAt (ψ[F; norm; J]) x : ℝ → EReal)

/-- Unfolding the canonical norm-specialized optimal-value owner recovers the textbook infimum of
the quadratic-regularized linearized residual objective over all steps `h`. -/
theorem modifiedGaussNewtonOptimalValueAt_norm_eq_sInf_range
    (F : E₁ → E₂)
    (J : E₁ → E₁ →L[ℝ] E₂)
    (x : E₁) (M : ℝ) :
    modifiedGaussNewtonOptimalValueAt (ψ[F; norm; J]) x M =
      sInf (Set.range fun h ↦
        (‖F x + J x h‖ + (M / 2 : ℝ) * ‖h‖ ^ (2 : ℕ) : EReal)) := sorry

end AuxiliaryValue

section DualObjective

variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/-- The intrinsic strong-dual objective corresponding to the norm auxiliary problem at a positive
regularization parameter `M`. -/
def modifiedGaussNewtonNormDualObjective
    (F : E₁ → E₂)
    (J : E₁ → E₁ →L[ℝ] E₂)
    (M : NNRealˣ) (x : E₁) : StrongDual ℝ E₂ → ℝ :=
  fun s ↦ s (F x) -
    (1 / (2 * (M : ℝ)) : ℝ) * ‖s.comp (J x)‖ ^ (2 : ℕ)

/-- Evaluating the intrinsic strong-dual objective gives the canonical precomposition formula. -/
@[simp] theorem modifiedGaussNewtonNormDualObjective_apply
    (F : E₁ → E₂)
    (J : E₁ → E₁ →L[ℝ] E₂)
    (M : NNRealˣ) (x : E₁) (s : StrongDual ℝ E₂) :
    modifiedGaussNewtonNormDualObjective F J M x s =
      s (F x) -
        (1 / (2 * (M : ℝ)) : ℝ) * ‖s.comp (J x)‖ ^ (2 : ℕ) := by
  rfl

/-- For positive `M`, the canonical norm-specialized auxiliary value equals the supremum of the
intrinsic strong-dual objective over the closed unit ball of the residual strong dual. -/
theorem modifiedGaussNewtonOptimalValueAt_norm_eq_sSup_dualObjective
    (F : E₁ → E₂)
    (J : E₁ → E₁ →L[ℝ] E₂)
    (x : E₁) (M : NNRealˣ) :
    modifiedGaussNewtonOptimalValueAt (ψ[F; norm; J]) x (M : ℝ) =
      sSup ((((↑) : ℝ → EReal) ∘ modifiedGaussNewtonNormDualObjective F J M x) ''
          closedBall (0 : StrongDual ℝ E₂) 1) :=
  sorry

end DualObjective

section DualBridge

variable [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
variable [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]

/-- Under the Riesz identification, the intrinsic strong-dual objective specializes to the
textbook Hilbert-space formula with the adjoint of `J x`. -/
@[simp] theorem modifiedGaussNewtonNormDualObjective_toDual
    (F : E₁ → E₂)
    (J : E₁ → E₁ →L[ℝ] E₂)
    (M : NNRealˣ) (x : E₁) (s : E₂) :
    modifiedGaussNewtonNormDualObjective F J M x (InnerProductSpace.toDual ℝ E₂ s) =
      inner ℝ s (F x) -
        (1 / (2 * (M : ℝ)) : ℝ) * ‖(J x).adjoint s‖ ^ (2 : ℕ) := by
  simp [modifiedGaussNewtonNormDualObjective,
    show (InnerProductSpace.toDual ℝ E₂ s).comp (J x) =
        InnerProductSpace.toDual ℝ E₁ ((J x).adjoint s) by
    ext y
    simp [ContinuousLinearMap.adjoint_inner_left]]

end DualBridge

end
