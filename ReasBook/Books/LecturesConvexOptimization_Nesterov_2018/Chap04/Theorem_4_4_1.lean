import Mathlib
import Nesterov.Chap04.Algorithm_4_4_1
import Nesterov.Chap04.Lemma_4_4_2
import Nesterov.Chap04.Lemma_4_4_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators LocalModelNotation Manifold
open scoped ModifiedGaussNewtonLocalModelNotation
open scoped ModifiedGaussNewtonLocalDecreaseNotation
open scoped ModifiedGaussNewtonQuadraticChiNotation
open scoped ModifiedGaussNewtonStep.ModifiedGaussNewtonStepWholeSpaceNotation

universe u v

variable {E₁ : Type u} {E₂ : Type v}
variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/- Theorem 4.4.1 lies in the modified Gauss--Newton trajectory / infinite-series domain.

Sampled owner declarations:
* `ModifiedGaussNewtonMethod` in `Algorithm_4_4_1`, the chapter owner for the iterate and
  regularization sequences;
* `ModifiedGaussNewtonStep.residualAtUniv` in `Definition_4_4_12`, the canonical whole-space
  residual view attached to a chosen modified Gauss--Newton step;
* `localModelDecreaseAt` in `Definition_4_4_13`, the canonical local-decrease owner specialized
  here through the finite-domain bridge from `Lemma_4_4_3`;
* `χ` in `Lemma_4_4_3`, the source-facing quadratic cutoff entering the textbook lower bounds;
* `cubicRegularization_residual_cube_summable_and_tsum_le` in `Theorem_4_1_1`, the nearby chapter
  pattern for expressing nonnegative infinite-tail bounds via `Summable` together with a `tsum`
  inequality.

Source/core/bridge triage:
* source-facing: Theorem 4.4.1 for the residual-square and chi-weighted tail estimates along a
  modified Gauss--Newton trajectory;
* core/canonical: `ModifiedGaussNewtonMethod` together with the step residual owner
  `ModifiedGaussNewtonStep.residualAtUniv` and the local-decrease owner
  `localModelDecreaseAt`;
* bridge/view: comparison of the varying regularization sequence `M_k` with the fixed parameter
  `2L`, yielding fixed-parameter tail bounds from the trajectory-owned varying tails.

Primitive data:
* a modified Gauss--Newton method `method`;
* a lower bound `fStar ≤ f z` for the merit reformulation;
* a fixed comparison step at regularization `2L`;
* the radius parameter `r` used in the local-decrease lower bound.

Derived API:
* summability of the nonnegative residual-square and chi-weighted tails;
* gap bounds on the corresponding infinite sums;
* summability and comparison bounds for the fixed-parameter tails derived from the varying ones.

The owner abstraction is therefore still the chapter trajectory object `ModifiedGaussNewtonMethod`.
The refinement here is on the derived series API: the nonnegative tails are stated on a
semantics-preserving `Summable` + `tsum` surface instead of as bare real `tsum` inequalities.
-/

local notation "SmoothMap" =>
  C^⊤⟮𝓘(ℝ, E₁), E₁; 𝓘(ℝ, E₂), E₂⟯

section

variable
    (problem : SmoothMap)
    (φ : E₂ → ℝ) [IsSharpMeritFunction φ]
    (L0 L : ℝ) (x0 : E₁)

local notation "f" => meritFunctionReformulation problem φ
local notation "ψ" => ψ[problem; φ; (fderiv ℝ problem)]

namespace ModifiedGaussNewtonMethod

-- Proof sketch: sum the one-step decrease inequalities
-- `f(x_i) - f(x_{i+1}) ≥ (M_i / 2) r_{M_i}(x_i)^2`, first derived once from
-- `method.step_value_le_modelValue`, `method.step_modelValue_le_merit`, and Lemma 4.4.2, along
-- the tail starting at
-- `k`, telescope the partial sums, and bound the remaining iterate values below by `fStar` via
-- `hf_lower`. Since the residual-square terms are nonnegative, the bounded partial sums give both
-- summability of the tail and the asserted `tsum` bound.
theorem meritFunction_sub_succ_ge_half_mul_residual_sq
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0)
    (k : ℕ) :
    f (method k) - f (method (k + 1)) ≥
      (method.regularization k / 2 : ℝ) *
        (r[(method.step k)] (method k)) ^ (2 : ℕ) := sorry

/-- Theorem 4.4.1 (1): the residual-square tail starting at `x_k` is summable, and the merit gap
at iterate `x_k` dominates its weighted sum `(L₀ / 2) ∑_{i=k}^∞ r_{Mᵢ}(xᵢ)^2`. -/
theorem gap_ge_residualSqTail
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0)
    {fStar : ℝ}
    (hf_lower : ∀ z : E₁, fStar ≤ f z)
    (k : ℕ) :
    Summable (fun i ↦ (r[(method.step (k + i))] (method (k + i))) ^ (2 : ℕ)) ∧
      f (method k) - fStar ≥
        (L0 / 2 : ℝ) *
          ∑' i, (r[(method.step (k + i))] (method (k + i))) ^ (2 : ℕ) := sorry

-- Proof sketch: use `method.regularization (k + i) ≤ 2L` termwise to compare the varying
-- regularization residuals with the fixed-parameter residuals. If the varying tail is summable,
-- termwise comparison yields summability of the fixed-parameter tail together with the tail
-- inequality.
/-- Theorem 4.4.1 (2): if the varying-parameter residual-square tail is summable, then the
comparison tail computed with the fixed parameter `2L` is also summable and is bounded by it. -/
theorem residualSqTail_ge_residualSqTailAt_two_mul_L
    (step2L : ModifiedGaussNewtonStep ψ Set.univ (2 * L))
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0)
    (k : ℕ)
    (hvarying :
      Summable (fun i ↦ (r[(method.step (k + i))] (method (k + i))) ^ (2 : ℕ))) :
    Summable (fun i ↦ (r[step2L] (method (k + i))) ^ (2 : ℕ)) ∧
      (L0 / 2 : ℝ) *
          ∑' i, (r[(method.step (k + i))] (method (k + i))) ^ (2 : ℕ) ≥
        (L0 / 2 : ℝ) *
          ∑' i, (r[step2L] (method (k + i))) ^ (2 : ℕ) := sorry

-- Proof sketch: sum the one-step decrease inequalities
-- `f(x_i) - f(x_{i+1}) ≥ r^2 M_i χ(Δ[problem; φ; r](x_i) / (M_i r^2))`, first derived once from
-- `method.step_value_le_modelValue`, `method.step_modelValue_le_merit`, and Lemma 4.4.3, along
-- the tail
-- starting at `k`, telescope the partial sums, and bound the remaining limit below by `fStar`
-- via `hf_lower`. The chi-weighted terms are nonnegative, so the same argument yields
-- summability of the tail together with the `tsum` inequality.
theorem meritFunction_sub_succ_ge_chiWeighted
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0)
    (k : ℕ) (r : NNReal) :
    f (method k) - f (method (k + 1)) ≥
      method.regularization k * (r : ℝ) ^ (2 : ℕ) *
        χ (Δ[problem; φ; r]((method k)) /
          (method.regularization k * (r : ℝ) ^ (2 : ℕ))) := sorry

/-- Theorem 4.4.1 (3): for every radius `r`, the chi-weighted tail
`∑_{i=k}^∞ Mᵢ χ(Δ_r(xᵢ) / (Mᵢ r²))` is summable, and the merit gap at iterate `x_k` dominates the
weighted sum `r² ∑_{i=k}^∞ Mᵢ χ(Δ_r(xᵢ) / (Mᵢ r²))`. -/
theorem gap_ge_chiWeightedTail
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0)
    {fStar : ℝ}
    (hf_lower : ∀ z : E₁, fStar ≤ f z)
    (k : ℕ) (r : NNReal) :
    Summable
        (fun i ↦
          method.regularization (k + i) *
            χ (Δ[problem; φ; r]((method (k + i))) /
              (method.regularization (k + i) * (r : ℝ) ^ (2 : ℕ)))) ∧
      f (method k) - fStar ≥
        (r : ℝ) ^ (2 : ℕ) *
          ∑' i,
            (method.regularization (k + i) *
              χ (Δ[problem; φ; r]((method (k + i))) /
                (method.regularization (k + i) * (r : ℝ) ^ (2 : ℕ)))) := sorry

-- Proof sketch: apply the antitonicity of
-- `M ↦ M χ(Δ[problem; φ; r](x_i) / (M r^2))` together with
-- `method.regularization (k + i) ≤ 2L` termwise,
-- then compare the resulting weighted tails. If the varying weighted tail is summable, the same
-- termwise comparison gives summability of the fixed-parameter weighted chi-tail and the asserted
-- bound.
/-- Theorem 4.4.1 (4): if the weighted chi-tail for the varying regularization parameters is
summable, then the comparison weighted chi-tail at the fixed parameter `2L` is summable and is
bounded by the varying-parameter tail. -/
theorem chiWeightedTail_ge_chiWeightedTailAt_two_mul_L
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0)
    (k : ℕ) (r : NNReal)
    (hvarying :
      Summable
        (fun i ↦
          method.regularization (k + i) *
            χ (Δ[problem; φ; r]((method (k + i))) /
              (method.regularization (k + i) * (r : ℝ) ^ (2 : ℕ))))) :
    Summable
        (fun i ↦
          (2 * L) *
            χ (Δ[problem; φ; r]((method (k + i))) /
              ((2 * L) * (r : ℝ) ^ (2 : ℕ)))) ∧
      (r : ℝ) ^ (2 : ℕ) *
          ∑' i,
            (method.regularization (k + i) *
              χ (Δ[problem; φ; r]((method (k + i))) /
                (method.regularization (k + i) * (r : ℝ) ^ (2 : ℕ)))) ≥
        (2 * L) * (r : ℝ) ^ (2 : ℕ) *
          ∑' i,
            χ (Δ[problem; φ; r]((method (k + i))) /
              ((2 * L) * (r : ℝ) ^ (2 : ℕ))) := sorry

end ModifiedGaussNewtonMethod

end
