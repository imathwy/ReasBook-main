import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_3_2
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_4_6_5
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_4_7_4
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.RealProdL2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

attribute [local instance] Chap05RealProdL2.instSeminormedAddCommGroupRealProd
attribute [local instance] Chap05RealProdL2.instNormedAddCommGroupRealProd
attribute [local instance] Chap05RealProdL2.instNormedSpaceRealProd
attribute [local instance] Chap05RealProdL2.instInnerProductSpaceRealProd
attribute [local instance] Chap05RealProdL2.instCompleteSpaceRealProd
attribute [local instance] Chap05RealProdL2.instSeminormedAddCommGroupRealProdProd
attribute [local instance] Chap05RealProdL2.instNormedAddCommGroupRealProdProd
attribute [local instance] Chap05RealProdL2.instNormedSpaceRealProdProd
attribute [local instance] Chap05RealProdL2.instInnerProductSpaceRealProdProd
attribute [local instance] Chap05RealProdL2.instCompleteSpaceRealProdProd

open scoped PowerConePlus

/- Theorem 5.4.7.4 lies in the Chapter 5 power-cone / cone-composition barrier domain.

Sampled owner declarations:
* `coneCompositionBarrier` from `Definition_5_4_6_5`, the generic composed-barrier owner;
* `power_cone_plus` from `Definition_5_4_7_4`, the source-facing one-sided power-cone owner;
* `qTwoPlus_sublevelLogBarrier_apply` from `Definition_5_4_7_5`, the recalled planar logarithmic
  barrier specialization used as the outer barrier factor;
* `coneCompositionBarrier_isSelfConcordantBarrierOnWith` from `Theorem_5_4_6_13`, the canonical
  composed-barrier owner theorem specialized here to the power-cone data;
* `power_cone_barrier` and `power_cone_barrier_is_four_self_concordant_barrier` from
  `Theorem_5_4_7_3`, the sibling source-facing barrier owner and theorem on the symmetric power
  cone.

Source/core/bridge triage:
* source-facing: the barrier owner `power_cone_plus_barrier α` and the resulting theorem on
  `interior (K_[α]⁺)` for the textbook function `Ψ_P^+((x₁, x₂), z)`;
* core/canonical: the generic owner theorem
  `coneCompositionBarrier_isSelfConcordantBarrierOnWith`;
* bridge/view: the pointwise identity between `power_cone_plus_barrier α` and the textbook
  logarithmic formula.

Primitive data:
* `powerConeBarrier`;
* `sublevelLogBarrier (fun yz ↦ yz.2 - yz.1) 0`;
* `powerConeGeometricMean α`;
* the source-facing cone owner `K_[α]⁺`.

Derived API:
* the source-facing barrier owner `power_cone_plus_barrier α`;
* the pointwise evaluation formula below;
* the resulting `3`-self-concordant barrier statement directly on
  `interior (K_[α]⁺)`.

This refinement keeps the source-facing cone owner `K_[α]⁺` as the public surface,
introduces the matching source-facing barrier owner `power_cone_plus_barrier α`, and keeps the
pointwise formula as the thin companion bridge to the canonical `coneCompositionBarrier`
specialization. -/

/-- The logarithmic barrier `Ψ_P^+` for the one-sided power cone `K_α^+`, presented as the
source-facing specialization of the chapter's canonical cone-composition barrier owner. -/
def power_cone_plus_barrier (α : ℝ) : ((ℝ × ℝ) × ℝ) → ℝ :=
  coneCompositionBarrier
    powerConeBarrier
    (sublevelLogBarrier (fun yz : ℝ × ℝ ↦ yz.2 - yz.1) 0)
    (powerConeGeometricMean α)
    1

-- Proof sketch: evaluate `power_cone_plus_barrier α` at `((x₁, x₂), z)` using the upstream
-- pointwise formulas for `powerConeBarrier`, `sublevelLogBarrier`, and `powerConeGeometricMean`.
/-- Evaluating `power_cone_plus_barrier α` at `((x₁, x₂), z)` gives the textbook formula
`-log (x₁^α x₂^(1 - α) - z) - log x₁ - log x₂`. -/
theorem power_cone_plus_barrier_apply (α x₁ x₂ z : ℝ) :
    power_cone_plus_barrier α ((x₁, x₂), z) =
      -Real.log (Real.rpow x₁ α * Real.rpow x₂ (1 - α) - z) -
        Real.log x₁ - Real.log x₂ := by
  rw [power_cone_plus_barrier, coneCompositionBarrier_apply,
    qTwoPlus_sublevelLogBarrier_apply, powerConeBarrier_apply, powerConeGeometricMean_apply]
  have hβ : (((1 : NNReal) : ℝ) ^ (3 : ℕ)) = 1 := by
    norm_num
  rw [hβ]
  ring

-- Proof sketch: instantiate the general cone-composition barrier theorem with
-- `Q₁ = powerConeQ1`, `K = ConvexCone.positive ℝ ℝ`, `ξ = powerConeGeometricMean α`,
-- `Q₂ = {(y, z) | z ≤ y}`, `Φ = sublevelLogBarrier (fun yz ↦ yz.2 - yz.1) 0`, and
-- `F = powerConeBarrier`. The compatibility hypothesis is provided by
-- `powerConeGeometricMean_isOneCompatibleWith_powerConeBarrier`, the barrier parameters are `1`
-- for `sublevelLogBarrier (fun yz ↦ yz.2 - yz.1) 0` and `2` for `powerConeBarrier`, and the
-- resulting source-facing owner `power_cone_plus_barrier α` has total parameter `3`. The bridge
-- lemma `power_cone_plus_barrier_apply` rewrites that owner to the textbook raw-triple
-- logarithmic formula, so the public theorem is stated directly on `interior (K_[α]⁺)`.
/-- Theorem 5.4.7.4: for `0 < α < 1`, the function
`Ψ_P^+((x₁, x₂), z) = -log (x₁^α x₂^(1 - α) - z) - log x₁ - log x₂` is a
`3`-self-concordant barrier for the one-sided power cone `K_α^+`. -/
theorem power_cone_plus_barrier_is_three_self_concordant_barrier
    {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    IsSelfConcordantBarrierOnWith
      (interior (K_[α]⁺))
      (3 : NNReal)
      (power_cone_plus_barrier α) := sorry
