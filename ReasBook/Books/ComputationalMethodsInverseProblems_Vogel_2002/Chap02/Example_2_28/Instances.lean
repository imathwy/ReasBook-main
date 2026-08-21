module

public import Mathlib.MeasureTheory.Function.LpOrder

public section

open MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

namespace MeasureTheory.Lp

variable {p : ENNReal}

/-- Real `Lᵖ(Ω, μ)` spaces inherit ordered scalar monotonicity from the pointwise order on
representatives. -/
instance instPosSMulMonoReal (μ : Measure Ω) : PosSMulMono ℝ (Lp ℝ p μ) where
  smul_le_smul_of_nonneg_left a ha f g hfg := by
    rw [← Lp.coeFn_le] at hfg ⊢
    filter_upwards [Lp.coeFn_smul a f, Lp.coeFn_smul a g, hfg] with x hfa hga hfgx
    rw [hfa, hga]
    simpa [Pi.smul_apply] using smul_le_smul_of_nonneg_left hfgx ha

end MeasureTheory.Lp
