import Mathlib
import ProbabilityTheory_Klenke_2020.Chap25.ContinuousLocalMartingaleIto
import ProbabilityTheory_Klenke_2020.Chap25.Definition_25_23
import ProbabilityTheory_Klenke_2020.Chap25.Theorem_25_17

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

local notation "TimeFiltration" => Filtration NNReal mΩ
local notation "Process" => NNReal → Ω → ℝ

variable {ℱ : TimeFiltration}

namespace IsBrownianLocalItoIntegral

/-- Any Brownian local Itô realization is a continuous local martingale. -/
theorem isContinuousLocalMartingale
    {W σ M : Process}
    (hM : IsBrownianLocalItoIntegral ℱ μ W σ M) :
    IsContinuousLocalMartingale ℱ μ M := by
  sorry

/-- The canonical square variation of a Brownian local Itô realization is absolutely continuous. -/
theorem hasAbsolutelyContinuousSquareVariation
    {W σ M : Process}
    (hM : IsBrownianLocalItoIntegral ℱ μ W σ M) :
    HasAbsolutelyContinuousSquareVariation M hM.isContinuousLocalMartingale := by
  sorry

end IsBrownianLocalItoIntegral

namespace IsGeneralizedDiffusion

/-- The canonical martingale part of a generalized diffusion has absolutely continuous square
variation, derived from its Brownian local Itô realization. -/
theorem martingalePart_hasAbsolutelyContinuousSquareVariation
    {W σ b X : Process}
    (hX : IsGeneralizedDiffusion ℱ μ W σ b X) :
    HasAbsolutelyContinuousSquareVariation
      (X - driftIntegralProcess b)
      hX.brownianLocalItoIntegral.isContinuousLocalMartingale := by
  simpa using hX.brownianLocalItoIntegral.hasAbsolutelyContinuousSquareVariation

end IsGeneralizedDiffusion

/-- Brownian-to-martingale bridge for Theorem 25.24: once the martingale part `M` is given by the
canonical Brownian owner `IsBrownianLocalItoIntegral`, its bracket witness stays internal and any
Brownian realization of `∫_0^t H_s σ_s dW_s` determines the canonical martingale Itô relation
`∫_0^t H_s dM_s`. -/
theorem stochasticIntegralTransform_martingalePart_isContinuousLocalMartingaleItoIntegral
    {W σ H M N : Process}
    (hM : IsBrownianLocalItoIntegral ℱ μ W σ M)
    (hN : IsBrownianLocalItoIntegral ℱ μ W (fun t ω ↦ H t ω * σ t ω) N) :
    IsContinuousLocalMartingaleItoIntegral hM.hasAbsolutelyContinuousSquareVariation H N := by
  sorry

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
set_option linter.unusedVariables false in
/-- Theorem 25.24 (1) in canonical project-facing form: if `X` is a generalized diffusion with
diffusion coefficient `σ` and drift `b`, and if `H` is progressively measurable with
`∫₀ᵀ H_s² σ_s² ds < ∞` and `∫₀ᵀ |H_s b_s| ds < ∞` almost surely on each finite interval, then the
canonical martingale part `X - ∫_0^. b_s ds` supplies the bracket data needed to construct a
process `N` realizing the martingale Itô integral `∫_0^t H_s dM_s`, and the transformed process
`Y_t := N_t + ∫_0^t H_s b_s ds` is again a generalized diffusion with diffusion coefficient `Hσ`
and drift `Hb`. The Brownian realization of `N`, and the facts that `N` is a continuous local
martingale with square variation `t ↦ ∫_0^t H_s^2 d⟨M⟩_s`, are recovered afterwards from the two
owner predicates `IsGeneralizedDiffusion` and `IsContinuousLocalMartingaleItoIntegral`. -/
theorem stochasticIntegralTransform_hasGeneralizedDiffusionDecomposition
    {W σ b H X : Process}
    (hX : IsGeneralizedDiffusion ℱ μ W σ b X)
    (hH_prog : ProgMeasurable ℱ H)
    (hHσ : ∀ T : NNReal, ∀ᵐ ω ∂μ,
      IntegrableOn (fun s : ℝ ↦ (H s.toNNReal ω * σ s.toNNReal ω) ^ 2)
        (Set.Icc (0 : ℝ) (T : ℝ)))
    (hHb : ∀ T : NNReal, ∀ᵐ ω ∂μ,
      IntegrableOn (fun s : ℝ ↦ |H s.toNNReal ω * b s.toNNReal ω|)
        (Set.Icc (0 : ℝ) (T : ℝ)))
    :
    ∃ N : Process,
      IsContinuousLocalMartingaleItoIntegral
        hX.martingalePart_hasAbsolutelyContinuousSquareVariation
        H
        N ∧
        IsGeneralizedDiffusion
          ℱ
          μ
          W
          (fun t ω ↦ H t ω * σ t ω)
          (fun t ω ↦ H t ω * b t ω)
          (N + driftIntegralProcess (fun t ω ↦ H t ω * b t ω)) := by
  sorry

/- Theorem 25.24 (2) and (3) are owner-level consequences of the canonical predicate
`IsContinuousLocalMartingaleItoIntegral`: any such stochastic integral is again a continuous
local martingale, and its square variation is `bracketDensityIntegralUpTo hMbr H`. In the
refined theorem surface above, those consequences are intentionally left to the namespace API of
`IsContinuousLocalMartingaleItoIntegral` rather than being repackaged as extra existential
payload. -/

end ProbabilityTheory
