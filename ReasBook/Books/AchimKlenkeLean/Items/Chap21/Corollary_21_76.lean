import Mathlib
import AchimKlenkeLean.Items.Chap09.Definition_9_7
import AchimKlenkeLean.Items.Chap21.Theorem_21_70

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
local notation "TimeFiltration" => Filtration NNReal mΩ

variable {ℱ : TimeFiltration}

-- Proof sketch: apply the square-variation theory to the canonical bracket process `⟨M⟩[hM]`;
-- the integrability of `M 0 ^ 2` and of the bracket
-- marginals upgrades the local-martingale identity for `M² - ⟨M⟩` to a genuine martingale and
-- yields `L²`-integrability of every time marginal of `M`.
/-- Owner-level form of Corollary 21.76: if a continuous local martingale has square-integrable
initial value and integrable canonical bracket marginals, then it is a square-integrable
martingale. -/
theorem square_integrable_martingale_of_integrable_bracket
    {M : NNReal → Ω → ℝ} (hM : IsContinuousLocalMartingale ℱ μ M)
    (_hM0_sq : MemLp (M 0) 2 μ)
    (_hbracket_int : IsIntegrableProcess (⟨M⟩[hM]) μ) :
    Martingale M ℱ μ ∧ IsSquareIntegrableProcess M μ := sorry

-- Proof sketch: since `Mlocc ℱ μ` is the set-level view of the owner
-- `IsContinuousLocalMartingale ℱ μ`, apply
-- `square_integrable_martingale_of_integrable_bracket` directly to `hM` and its canonical bracket
-- `⟨M⟩[hM]`.
/-- Corollary 21.76 in the textbook notation `M ∈ 𝓜_{loc,c}`. This is the thin bridge from the
set-level view `Mlocc ℱ μ` to the owner theorem
`square_integrable_martingale_of_integrable_bracket`. -/
theorem square_integrable_martingale_of_mem_Mlocc_of_integrable_bracket
    {M : NNReal → Ω → ℝ} (hM : M ∈ Mlocc ℱ μ)
    (_hM0_sq : MemLp (M 0) 2 μ)
    (_hbracket_int : IsIntegrableProcess (⟨M⟩[hM]) μ) :
    Martingale M ℱ μ ∧ IsSquareIntegrableProcess M μ :=
  square_integrable_martingale_of_integrable_bracket hM _hM0_sq _hbracket_int

end ProbabilityTheory
