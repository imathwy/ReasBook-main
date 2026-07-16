import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Definition_4_4_8
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Definition_4_4_9
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Definition_4_4_10
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Definition_4_4_11
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Definition_4_4_12
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Definition_4_4_13

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped LocalModelNotation Manifold
open scoped ModifiedGaussNewtonLocalModelNotation
open scoped ModifiedGaussNewtonStep.ModifiedGaussNewtonStepWholeSpaceNotation

universe u v

variable {E₁ : Type u} {E₂ : Type v}
variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

local notation "SmoothMap" =>
  C^⊤⟮𝓘(ℝ, E₁), E₁; 𝓘(ℝ, E₂), E₂⟯

section

variable (problem : SmoothMap) (φ : E₂ → ℝ) [IsSharpMeritFunction φ]

local notation "f" => meritFunctionReformulation problem φ
local notation "ψ" => ψ[problem; φ; (fderiv ℝ problem)]

/-- The modified Gauss--Newton local model is finite on every closed trust-region ball, so the
source-facing local-model decrease `Δ_r(x)` is defined at every point. -/
theorem modifiedGaussNewtonLocalModel_mem_finiteDomain
    (problem : SmoothMap) (φ : E₂ → ℝ) [IsSharpMeritFunction φ]
    (r : NNReal) (x : E₁) :
    x ∈ localModelFiniteDomain (ψ[problem; φ; (fderiv ℝ problem)]) r :=
  mem_localModelFiniteDomain_of_bddBelow (ψ[problem; φ; (fderiv ℝ problem)]) r x
    (bddBelow_image_closedBall_of_nonneg (ψ[problem; φ; (fderiv ℝ problem)]) r
      (fun x y ↦
        show 0 ≤ φ (problem x + fderiv ℝ problem x (y - x)) from
          IsMeritFunction.nonneg _)
      x)

/-- The scalar cutoff function `χ` from the quadratic-regularization lower bound, given by
`χ(t) = t - 1 / 2` for `t ≥ 1` and `χ(t) = t² / 2` for `t < 1`. -/
def modifiedGaussNewtonQuadraticChi (t : ℝ) : ℝ :=
  if 1 ≤ t then t - 1 / 2 else (1 / 2 : ℝ) * t ^ (2 : ℕ)

namespace ModifiedGaussNewtonQuadraticChiNotation

scoped notation:max "χ" => modifiedGaussNewtonQuadraticChi

end ModifiedGaussNewtonQuadraticChiNotation

open scoped ModifiedGaussNewtonQuadraticChiNotation

-- Proof sketch: unfold `modifiedGaussNewtonQuadraticChi` and use the branch condition `t < 1`
-- to select the quadratic branch of the `if`.
/-- Below the threshold `t = 1`, the cutoff function `χ` is equal to `t² / 2`. -/
theorem modifiedGaussNewtonQuadraticChi_of_lt_one {t : ℝ} (ht : t < 1) :
    χ t = (1 / 2 : ℝ) * t ^ (2 : ℕ) := by
  simp [modifiedGaussNewtonQuadraticChi, if_neg (not_le_of_gt ht)]

-- Proof sketch: unfold `modifiedGaussNewtonQuadraticChi` and use the branch condition `1 ≤ t`
-- to select the affine branch of the `if`.
/-- Above the threshold `t = 1`, the cutoff function `χ` is equal to `t - 1 / 2`. -/
theorem modifiedGaussNewtonQuadraticChi_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    χ t = t - 1 / 2 := by
  simp [modifiedGaussNewtonQuadraticChi, if_pos ht]

/-- The modified Gauss--Newton specialization of the canonical local-model decrease `Δ_r(x)`,
obtained by supplying the finite-domain proof coming from the nonnegativity of the sharp merit
function on each closed trust-region ball. The source-facing notation is
`Δ[problem; φ; r](x)`. -/
abbrev modifiedGaussNewtonLocalDecrease
    (problem : SmoothMap) (φ : E₂ → ℝ) [IsSharpMeritFunction φ]
    (r : NNReal) (x : E₁) : ℝ :=
  localModelDecreaseAt
    (meritFunctionReformulation problem φ)
    (ψ[problem; φ; (fderiv ℝ problem)])
    r x
    (modifiedGaussNewtonLocalModel_mem_finiteDomain problem φ r x)

namespace ModifiedGaussNewtonLocalDecreaseNotation

/- Source-facing Lean notation for the textbook modified Gauss--Newton local decrease `Δ_r(x)`. -/
scoped notation:max "Δ[" problem:arg "; " φ:arg "; " r:arg "](" x:arg ")" =>
  modifiedGaussNewtonLocalDecrease problem φ r x

end ModifiedGaussNewtonLocalDecreaseNotation

open scoped ModifiedGaussNewtonLocalDecreaseNotation

-- Proof sketch: compare the quadratic-regularized model value at the minimizer `step x` with the
-- one-dimensional path `y = x + τ (y₀ - x)` for a point `y₀` in the radius-`r` ball that nearly
-- attains the local-model infimum; convexity of the sharp merit function gives
-- `ψ(x; x + τ (y₀ - x)) ≤ f(x) - τ Δ_r(x)`, and maximizing the resulting scalar quadratic over
-- `τ ∈ [0, 1]` yields the factor `M r² χ(Δ_r(x) / (M r²))`.
/-- Lemma 4.4.3: for a smooth nonlinear equation problem `problem`, a sharp merit function `φ`,
and a modified Gauss--Newton step with positive regularization parameter `M`, the model gap
`δ_M(x)` is bounded below by `M r² χ(Δ_r(x) / (M r²))` for every `x` and every radius `r`. -/
theorem modifiedGaussNewton_modelGap_ge_localModelDecrease_chi
    (M : ℝ)
    (hM : 0 < M)
    (step :
      ModifiedGaussNewtonStep
        ψ
        Set.univ M)
    (x : E₁) (r : NNReal) :
    δ[step; f](x) ≥
      M * (r : ℝ) ^ (2 : ℕ) *
        χ (Δ[problem; φ; r](x) /
          (M * (r : ℝ) ^ (2 : ℕ))) := sorry

-- Proof sketch: write the right-hand side as a scalar function of `M > 0`, split into the
-- regimes `Δ_r(x) / (M r²) ≥ 1` and `Δ_r(x) / (M r²) < 1`, and check directly in each branch
-- that increasing `M` decreases the value.
/-- For fixed `problem`, `φ`, `x`, and radius `r`, the right-hand side of the lower
bound in `modifiedGaussNewton_modelGap_ge_localModelDecrease_chi` is decreasing as a function of
the regularization parameter `M > 0`. -/
theorem modifiedGaussNewton_lowerBound_rhs_antitoneOn
    (x : E₁) (r : NNReal) :
    AntitoneOn
      (fun M : ℝ ↦
        M * (r : ℝ) ^ (2 : ℕ) *
          χ (Δ[problem; φ; r](x) /
            (M * (r : ℝ) ^ (2 : ℕ))))
      (Set.Ioi (0 : ℝ)) := sorry

end
