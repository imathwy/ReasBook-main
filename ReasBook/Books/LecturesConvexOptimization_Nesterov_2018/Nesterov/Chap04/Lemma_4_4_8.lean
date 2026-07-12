import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap04.Definition_4_2_9
import LecturesConvexOptimization_Nesterov_2018.Chap04.Definition_4_4_11
import LecturesConvexOptimization_Nesterov_2018.Chap04.Proposition_4_4_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open LinearMap (BilinForm)
open LinearMap.BilinForm
open Set
open scoped BInducedNorm
open scoped ModifiedGaussNewtonLocalModelNotation

universe u v

/- Lemma 4.4.8 lies in the weighted modified Gauss--Newton optimal-value domain.

Sampled owner-style declarations:
* `PrimalSpace` in `Definition_4_2_9`, the chapter owner for the intrinsic `B`-weighted carrier;
* `modifiedGaussNewtonLocalModel` in `Definition_4_4_11`, the chapter owner for the affine
  residual model;
* `modifiedGaussNewtonOptimalValueAt` and `modifiedGaussNewtonOptimalValue` in
  `Proposition_4_4_6`, the chapter owners for whole-space modified Gauss--Newton optimal values.

Source/core/bridge triage:
* source-facing: the weighted textbook formulas written with `‖·‖[B₁]` and `‖·‖[B₂]`;
* core/canonical: `modifiedGaussNewtonOptimalValueAt (ψ[F; norm; J]) x` and
  `modifiedGaussNewtonOptimalValue (ψ[F; norm; J]) x` on `PrimalSpace B₁` and `PrimalSpace B₂`;
* bridge/view: the step-variable `sInf` expansion, the `‖·‖[B]` rewrites, and the final
  positive-`τ` infimum formula.

This file therefore keeps only thin weighted bridge lemmas. The duplicate local owners for the
auxiliary objective and its optimal value are deleted in favor of direct reuse of the Chapter 4
canonical owner. -/

section AuxiliaryValue

variable {E₁ : Type u} {E₂ : Type v}
variable [AddCommGroup E₁] [Module ℝ E₁]
variable [AddCommGroup E₂] [Module ℝ E₂]
variable (B₁ : BilinForm ℝ E₁) [Fact B₁.toQuadraticMap.PosDef]
variable (B₂ : BilinForm ℝ E₂) [Fact B₂.toQuadraticMap.PosDef]
variable (F : PrimalSpace B₁ → PrimalSpace B₂)
variable (J : PrimalSpace B₁ → PrimalSpace B₁ →L[ℝ] PrimalSpace B₂)
variable (x : PrimalSpace B₁)

/- The weighted auxiliary value in Lemma 4.4.8 is the existing Chapter 4 optimal-value owner
specialized to the local model `ψ[F; norm; J]` on the intrinsic weighted carriers. -/
set_option linter.hashCommand false in
#check (modifiedGaussNewtonOptimalValueAt (ψ[F; norm; J]) x : ℝ → EReal)

set_option linter.hashCommand false in
#check (modifiedGaussNewtonOptimalValue (ψ[F; norm; J]) x : NNRealˣ → ℝ)

/-- Unfolding the canonical weighted optimal-value owner gives the step-variable infimum over the
intrinsic weighted carrier `PrimalSpace B₁`. -/
theorem modifiedGaussNewtonOptimalValueAt_weighted_eq_sInf_range
    (M : ℝ) :
    modifiedGaussNewtonOptimalValueAt (ψ[F; norm; J]) x M =
      sInf (range fun h : PrimalSpace B₁ ↦
        (‖F x + J x h‖ + (M / 2 : ℝ) * ‖h‖ ^ (2 : ℕ) : EReal)) := sorry

/-- Rewriting the intrinsic ambient norms back into the explicit textbook `B`-induced norms
recovers the weighted formula stated in the source text. -/
theorem modifiedGaussNewtonOptimalValueAt_weighted_eq_sInf_range_bInducedNorm
    (M : ℝ) :
    modifiedGaussNewtonOptimalValueAt (ψ[F; norm; J]) x M =
      sInf (range fun h : PrimalSpace B₁ ↦
        (‖F x + J x h‖[B₂] + (M / 2 : ℝ) * ‖h‖[B₁] ^ (2 : ℕ) : EReal)) := by
  simpa only [LinearMap.BilinForm.primalSpace_norm_eq_bInducedNorm] using
    modifiedGaussNewtonOptimalValueAt_weighted_eq_sInf_range B₁ B₂ F J x M

/-- In the positive-regularization regime, the source-facing weighted auxiliary value is still the
existing Chapter 4 positive owner `modifiedGaussNewtonOptimalValue (ψ[F; norm; J]) x`. This
companion theorem rewrites that owner into the textbook `B`-induced step-variable infimum. -/
theorem modifiedGaussNewtonOptimalValue_weighted_eq_sInf_range_bInducedNorm
    (M : NNRealˣ) :
    modifiedGaussNewtonOptimalValue (ψ[F; norm; J]) x M =
      sInf (range fun h : PrimalSpace B₁ ↦
        ‖F x + J x h‖[B₂] + (((M : ℝ) / 2 : ℝ) * ‖h‖[B₁] ^ (2 : ℕ))) := sorry

-- Proof sketch: use `√a = inf_{τ > 0} ((τ / 2) + a / (2τ))` with
-- `a = ‖F x + J x h‖[B₂]^2`, then exchange the two infima on the intrinsic weighted carrier.
/-- Lemma 4.4.8: for positive regularization, the canonical weighted optimal-value owner equals
the infimum of the reduced positive-`τ` objective written in the explicit `B`-induced norms. -/
theorem modifiedGaussNewtonWeightedAuxiliaryValue_eq_sInf_weightedTauObjective
    (M : NNRealˣ) :
    modifiedGaussNewtonOptimalValue (ψ[F; norm; J]) x M =
      sInf (range fun τ : NNRealˣ ↦
        ((τ : ℝ) / 2 : ℝ) +
          sInf (range fun h : PrimalSpace B₁ ↦
            (1 / (2 * (τ : ℝ)) : ℝ) * ‖F x + J x h‖[B₂] ^ (2 : ℕ) +
              (((M : ℝ) / 2 : ℝ) * ‖h‖[B₁] ^ (2 : ℕ)))) := sorry

end AuxiliaryValue

end
