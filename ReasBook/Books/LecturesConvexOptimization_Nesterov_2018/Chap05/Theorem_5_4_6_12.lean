import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_1_1
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_4_6_2
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_4_6_5
import LecturesConvexOptimization_Nesterov_2018.Chap05.Theorem_5_4_6_10
import LecturesConvexOptimization_Nesterov_2018.Chap05.Theorem_5_4_6_11

noncomputable section

open ProperCone
open scoped Gradient HessianLocalNorm

universe u v w

variable {E₁ : Type u} {E₂ : Type v} {E₃ : Type w}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]
  [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]
  [InnerProductSpace ℝ (E₂ × E₃)] [CompleteSpace (E₂ × E₃)]

/- Theorem 5.4.6.12 lies in the subsection's fixed-`z` slice self-concordance domain.

Sampled owner declarations:
* `coneCompositionBarrier` from `Definition_5_4_6_5`, the source-facing barrier owner on
  `E₁ × E₃`;
* `compositionPotential_thirdDirectionalDerivative_le_selfConcordant_sigma_bound` from
  `Theorem_5_4_6_10`, the subsection owner upper bound for the composition-potential slice;
* `coneCompositionBarrier_slice_secondDirectionalDerivative_ge_sigmaSum_add_betaSq_sigmaThree`
  from `Theorem_5_4_6_11`, the slice-level second-derivative owner for the same barrier slice;
* `IsBetaCompatibleWith` from `Definition_5_4_6_2`, the compatibility owner supplying the hidden
  `β ≥ 1`, `C³`, and barrier inputs used by the slice estimates;
* `IsStandardSelfConcordantOn` from `Definition_5_1_1`, the chapter owner for the standard
  self-concordance hypothesis on `Φ`.

Source/core/bridge triage:
* source-facing: the fixed-`z` slice
  `x' ↦ coneCompositionBarrier F Φ ξ β (x', z)`;
* core/canonical: `thirdDirectionalDerivative` and `secondDirectionalDerivative`;
* bridge/view: the `D₃` upper bound from `Theorem_5_4_6_10`, the `D₂` lower bound from
  `Theorem_5_4_6_11`, and the compatibility-owner projections used to recover their hidden local
  hypotheses.

Primitive data:
* `F`, `Φ`, `ξ`, `β`, `x`, `z`, `h`;
* standard self-concordance of `Φ` on `interior Q₂` at `(ξ x, z)`;
* the lifted-direction local-norm bound and the dual-cone gradient hypothesis;
* the compatibility owner `IsBetaCompatibleWith Q₁ K F β ξ`.

Derived API:
* the slice self-concordance inequality
  `D₃ ≤ 2 D₂^(3/2)` for `x' ↦ coneCompositionBarrier F Φ ξ β (x', z)`.

This theorem should therefore sit directly on the existing `coneCompositionBarrier` slice owner
and depend on the slice-level `D₂` theorem from `5.4.6.11`, rather than reaching back to the
earlier sigma decomposition theorem and reassembling the barrier slice data locally. -/

section

variable (F : E₁ → ℝ) (Φ : E₂ × E₃ → ℝ) (ξ : E₁ → E₂) (β : NNReal)
  (x : E₁) (z : E₃) (h : E₁)

local notation "Ψ" => fun x' : E₁ ↦ coneCompositionBarrier F Φ ξ β (x', z)

-- Proof sketch: combine the third-derivative sigma bound from
-- `compositionPotential_thirdDirectionalDerivative_le_selfConcordant_sigma_bound` with the
-- second-derivative lower bound coming from
-- `coneCompositionBarrier_slice_secondDirectionalDerivative_ge_sigmaSum_add_betaSq_sigmaThree`
-- together with the barrier and regularity data packaged by `hξ_compat`, then apply the scalar
-- inequality
-- `t * (3 * s - t^2) ≤ 2 * s^(3/2)` to the resulting `σ₁`, `σ₂`, `σ₃` expression.
/-- Theorem 5.4.6.12: assume `Φ` is standard self-concordant at `(ξ x, z)`, `ξ` is
`β`-compatible with the barrier `F` on `Q₁`, and the local hypotheses used in
Theorem 5.4.6.10 hold for the slice `x' ↦ compositionPotential Φ ξ (x', z)`. The hidden
`β ≥ 1`, `C³`, and barrier inputs needed for the slice second-derivative estimate come from the
compatibility owner `hξ_compat`. Then the slice
`Ψ(x') = coneCompositionBarrier F Φ ξ β (x', z)` satisfies the third-derivative inequality
`D₃ ≤ 2 D₂^(3/2)` at `x` in direction `h`. -/
theorem coneCompositionBarrier_slice_selfConcordant_bound
    {Q₁ : Set E₁} {Q₂ : Set (E₂ × E₃)} {K : ConvexCone ℝ E₂}
    (hΦ : IsStandardSelfConcordantOn (interior Q₂) Φ)
    (hyz : (ξ x, z) ∈ interior Q₂)
    (hneg_liftedDirectionDerivative_le_sigmaTwo :
      ‖-compositionSecondLiftedDirectionDerivative ξ x h‖[Φ; (ξ x, z)] ≤
        compositionPotentialSigmaTwo Φ ξ x z h)
    (hξ_compat : IsBetaCompatibleWith Q₁ K F β ξ)
    (hx : x ∈ interior Q₁)
    (hneg_yGradient_mem_innerDual :
      -∇ (fun y : E₂ ↦ Φ (y, z)) (ξ x) ∈ innerDual (K : Set E₂)) :
    thirdDirectionalDerivative Ψ x h ≤
      2 * (Real.sqrt (secondDirectionalDerivative Ψ x h)) ^ (3 : ℕ) := sorry

end
