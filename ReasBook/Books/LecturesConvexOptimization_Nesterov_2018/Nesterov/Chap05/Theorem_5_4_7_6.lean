import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_3_2
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_4_6_2
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_4_6_5
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_4_7_8
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_4_7_9
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_4_8_5
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.RealProdL2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped EntropyEpigraph

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

/-
Theorem 5.4.7.6 lies in the Chapter 5 entropy-epigraph / cone-composition barrier domain.

Sampled owner declarations:
* `entropyEpigraphCone` from `Definition_5_4_7_8`, the source-facing feasible-set owner;
* `entropyEpigraphRelativeEntropy` and
  `entropyEpigraphQ2_sublevelLogBarrier_apply` from `Definition_5_4_7_9`, the entropy-specific
  map and outer logarithmic barrier factor;
* `coneCompositionBarrier` from `Definition_5_4_6_5`, the canonical composed-barrier owner;
* `IsBetaCompatibleWith` from `Definition_5_4_6_2`, the chapter owner for the compatibility
  hypothesis used in clause `(1)`;
* `Chap05RealProdL2` from `RealProdL2`, the chapter owner bridge realizing the raw coordinate
  product types with the Euclidean `L²` ambient structure required by the barrier owners.

Source/core/bridge triage:
* source-facing: `entropyEpigraphConeBarrier` and the four theorem clauses below;
* core/canonical: `coneCompositionBarrier`, `IsBetaCompatibleWith`, and
  `IsSelfConcordantBarrierOnWith`;
* bridge/view: `Chap05RealProdL2`, `entropyEpigraphConeBarrier_apply`, and the
  slice-identification theorems.

Primitive data:
* the orthant barrier `powerConeBarrier`;
* the entropy-specific map `ξ`;
* the half-space barrier factor `sublevelLogBarrier (fun yz ↦ -yz.1 - yz.2) 0`.

Derived API:
* the source-facing barrier owner `entropyEpigraphConeBarrier`;
* the pointwise textbook evaluation formula;
* the compatibility, barrier, and slice theorems.

The owner-level refinement here is to reuse the chapter's canonical composed-barrier owner
directly, instead of storing a parallel explicit raw formula as primitive data. -/

/-- The logarithmic barrier `ψ_E` for the entropy-epigraph cone, presented as the source-facing
specialization of the chapter's canonical cone-composition barrier owner. -/
def entropyEpigraphConeBarrier : ((ℝ × ℝ) × ℝ) → ℝ :=
  coneCompositionBarrier
    powerConeBarrier
    (sublevelLogBarrier (fun yz : ℝ × ℝ ↦ -yz.1 - yz.2) 0)
    ξ
    1

-- Proof sketch: evaluate the source-facing owner through the canonical `coneCompositionBarrier`
-- specialization and the upstream pointwise formulas for its three factors.
/-- Evaluating `entropyEpigraphConeBarrier` at `((x₁, x₂), z)` gives the textbook formula
`-\log (z - x^(1) \log (x^(1) / x^(2))) - \log x^(1) - \log x^(2)`. -/
theorem entropyEpigraphConeBarrier_apply (x₁ x₂ z : ℝ) :
    entropyEpigraphConeBarrier ((x₁, x₂), z) =
      -Real.log (z - x₁ * Real.log (x₁ / x₂)) - Real.log x₁ - Real.log x₂ := by
  rw [entropyEpigraphConeBarrier, coneCompositionBarrier_apply,
    entropyEpigraphQ2_sublevelLogBarrier_apply, powerConeBarrier_apply,
    entropyEpigraphRelativeEntropy_apply]
  norm_num
  have harg : -(x₁ * Real.log (x₁ / x₂)) + z = z - x₁ * Real.log (x₁ / x₂) := by ring
  rw [harg]
  ring

-- Proof sketch: compute the second and third directional derivatives of
-- `entropyEpigraphRelativeEntropy`, identify `hessianLocalNorm powerConeBarrier x h` with
-- the Euclidean norm of the scaled direction, and use Cauchy--Schwarz to obtain the coefficient
-- bound required in `IsBetaCompatibleWith` for `β = 1`.
/-- Theorem 5.4.7.6 (1): the relative-entropy map
`ξ(x) = -x^(1) \log (x^(1) / x^(2))` is `1`-compatible with the orthant barrier
`F(x) = -\log x^(1) - \log x^(2)` relative to the scalar cone `ℝ_+`. -/
theorem entropyEpigraphRelativeEntropy_isOneCompatibleWith_powerConeBarrier :
    IsBetaCompatibleWith powerConeQ1 (ConvexCone.positive ℝ ℝ)
      powerConeBarrier (1 : NNReal) ξ := sorry

-- Proof sketch: apply the general cone-composition barrier theorem to
-- `Q₁ = powerConeQ1`, `K = ConvexCone.positive ℝ ℝ`, the entropy-specific map `ξ`,
-- the half-space `Q₂`, `Φ = sublevelLogBarrier (fun yz : ℝ × ℝ ↦ -yz.1 - yz.2) 0`, and
-- `F = powerConeBarrier`. Clause `(1)` supplies the compatibility hypothesis, the barrier
-- parameters are `2` and `1`, and the composed barrier simplifies to `entropyEpigraphConeBarrier`.
/-- Theorem 5.4.7.6 (2): the function
`ψ_E((x^(1), x^(2)), z) = -\log (z - x^(1) \log (x^(1) / x^(2))) - \log x^(1) - \log x^(2)` is
a `3`-self-concordant barrier for the entropy-epigraph cone `\mathcal Q`. -/
theorem entropyEpigraphConeBarrier_is_three_self_concordant_barrier :
    IsSelfConcordantBarrierOnWith (interior entropyEpigraphCone) (3 : NNReal)
      entropyEpigraphConeBarrier := sorry

-- Proof sketch: unfold `entropyEpigraphCone` at the point `((1, x₂), z)`, rewrite the defining
-- inequality using `1 * (Real.log 1 - Real.log x₂) = -Real.log x₂`, and keep the positivity of
-- `x₂` explicit because Lean's totalized `Real.log` hides the textbook domain restriction.
/-- Theorem 5.4.7.6 (3): on the affine slice `x^(1) = 1`, the entropy-epigraph cone is exactly
the chapter constrained epigraph of `x^(2) ↦ -\log x^(2)` on `(0, ∞)`, with the positivity
condition on `x^(2)` made explicit. -/
theorem entropyEpigraphCone_unitSlice_eq_logEpigraph :
    {yz : ℝ × ℝ | ((1, yz.1), yz.2) ∈ entropyEpigraphCone} =
      constrainedEpigraph (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ (-Real.log x : WithTop ℝ)) := sorry

-- Proof sketch: start from the description in clause `(3)` and exponentiate the inequality
-- `z ≥ -log x₂`; since `Real.exp (-z)` is always positive, this is equivalent to
-- `x₂ ≥ Real.exp (-z)`.
/-- Theorem 5.4.7.6 (4): on the affine slice `x^(1) = 1`, the entropy-epigraph cone is
equivalently described by the inequality `x^(2) ≥ e^{-z}`. -/
theorem entropyEpigraphCone_unitSlice_eq_expEpigraph :
    {yz : ℝ × ℝ | ((1, yz.1), yz.2) ∈ entropyEpigraphCone} =
      {yz : ℝ × ℝ | yz.1 ≥ Real.exp (-yz.2)} := sorry
