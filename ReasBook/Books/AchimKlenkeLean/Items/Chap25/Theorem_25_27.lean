import Mathlib
import AchimKlenkeLean.Items.Chap21.Corollary_21_76
import AchimKlenkeLean.Items.Chap25.ContinuousLocalMartingaleIto
import AchimKlenkeLean.Items.Chap25.Definition_25_23
import AchimKlenkeLean.Items.Chap25.Theorem_25_24

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

local notation "TimeFiltration" => Filtration NNReal mΩ
local notation "Process" => NNReal → Ω → ℝ

variable {ℱ : TimeFiltration}

/-- Theorem 25.27: if `Y` is a generalized diffusion with Brownian driver `W`, diffusion
coefficient `σ`, and drift `b`, and if `N` realizes the canonical martingale Itô integral
`∫_0^t F' (Y_s) dM_s` for the centered martingale part
`M := Y - ∫_0^. b_s ds`, then Itô's formula holds as an equality of modifications:
`F (Y_t) - F (Y_0)` agrees with the sum of the stochastic term `N_t` and the drift term
`∫_0^t (F' (Y_s) b_s + 1/2 F'' (Y_s) σ_s^2) ds` at every deterministic time almost surely. The
Brownian realization data of `M` remains internal to `hY : IsGeneralizedDiffusion ...`; the public
API keeps `hY` as the source-facing owner input and asks only for the stochastic-integral
realization `hN`, phrased against the canonical bracket witness derived from `hY`. -/
theorem generalizedDiffusion_ito_formula
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    {W σ b Y N : Process}
    (hY : IsGeneralizedDiffusion ℱ μ W σ b Y)
    (hN :
      IsContinuousLocalMartingaleItoIntegral
        hY.martingalePart_hasAbsolutelyContinuousSquareVariation
        (fun t ω ↦ deriv F (Y t ω))
        N) :
    AreModifications μ
      (fun t ω ↦ F (Y t ω) - F (Y 0 ω))
      (fun t ω ↦
        N t ω +
          ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            deriv F (Y s.toNNReal ω) * b s.toNNReal ω +
              ((1 : ℝ) / 2) *
                iteratedDeriv 2 F (Y s.toNNReal ω) * (σ s.toNNReal ω) ^ 2) := sorry

set_option linter.unusedVariables false in
/-- The fixed-time almost-sure form of Theorem 25.27. -/
theorem generalizedDiffusion_ito_formula_ae_eq
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    {W σ b Y N : Process}
    (hY : IsGeneralizedDiffusion ℱ μ W σ b Y)
    (hN :
      IsContinuousLocalMartingaleItoIntegral
        hY.martingalePart_hasAbsolutelyContinuousSquareVariation
        (fun t ω ↦ deriv F (Y t ω))
        N)
    (t : NNReal) :
    (fun ω ↦ F (Y t ω) - F (Y 0 ω))
      =ᵐ[μ]
        (fun ω ↦
          N t ω +
            ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
              deriv F (Y s.toNNReal ω) * b s.toNNReal ω +
                ((1 : ℝ) / 2) *
                  iteratedDeriv 2 F (Y s.toNNReal ω) * (σ s.toNNReal ω) ^ 2) :=
  generalizedDiffusion_ito_formula F hF hY hN t

end ProbabilityTheory
