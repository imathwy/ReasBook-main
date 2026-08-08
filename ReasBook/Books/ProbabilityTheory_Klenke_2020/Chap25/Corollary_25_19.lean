import Mathlib
import ProbabilityTheory_Klenke_2020.Chap25.Definition_25_14
import ProbabilityTheory_Klenke_2020.Chap25.Definition_25_16
import ProbabilityTheory_Klenke_2020.Chap25.Theorem_25_4
import ProbabilityTheory_Klenke_2020.Chap25.Theorem_25_18
import ProbabilityTheory_Klenke_2020.Chap21.Theorem_21_70
import ProbabilityTheory_Klenke_2020.Chap21.Corollary_21_76

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

local notation "TimeFiltration" => Filtration NNReal mΩ
local notation "Process" => NNReal → Ω → ℝ

variable {ℱ : TimeFiltration}

-- Proof sketch: combine the continuous realization supplied by `IsBrownianLocalItoIntegral` with
-- Theorem 25.17 and then apply Theorem 25.18 to identify `secondMomentCompensator H` as the
-- square variation process of `M`.
/-- Corollary 25.19: if `H ∈ 𝓔_loc`, then any realization of the Itô integral
`M_t = ∫_0^t H_s dW_s` is a continuous local martingale whose square variation process is
`⟨M⟩_t = ∫_0^t H_s^2 ds`. -/
theorem brownianLocalItoIntegral_isContinuousLocalMartingale_and_has_squareVariation
    {W H M : Process}
    (hM : IsBrownianLocalItoIntegral ℱ μ W H M) :
    IsContinuousLocalMartingale ℱ μ M ∧
      IsContinuousSquareVariationProcess ℱ μ M (secondMomentCompensator H) := sorry

end ProbabilityTheory
