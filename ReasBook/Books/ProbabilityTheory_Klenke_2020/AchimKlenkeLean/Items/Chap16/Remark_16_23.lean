import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap16.Theorem_16_17
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap16.Theorem_16_22

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

noncomputable section

namespace MeasureTheory.ProbabilityMeasure

/-- The scalar `I(a)` used in the textbook closed forms for stable characteristic exponents. -/
noncomputable def stableIntegralI (a : ℝ) : ℝ :=
  Real.Gamma a

-- Proof sketch: unfold `stableIntegralI`; this auxiliary scalar is defined to be the Gamma factor
-- used in the closed-form stable-exponent formula.
/-- The auxiliary scalar `stableIntegralI` is the real Gamma factor `Γ(a)`. -/
theorem stableIntegralI_def (a : ℝ) :
    stableIntegralI a = Real.Gamma a := sorry

-- Proof sketch: insert the stable Lévy density from `(16.19)` into the canonical-owner
-- Lévy--Khintchine formula, use the drift relation from Theorem 16.22 when `α ≠ 1`, and then
-- rewrite the resulting exponent in the textbook piecewise form `(16.20)`.
/-- Remark 16.23: if an infinitely divisible probability law on `ℝ` has canonical triple
`(0, b, ν)` with `ν = stableLevyMeasure α c⁻ c⁺`, then its log-characteristic function is the
piecewise stable exponent from `(16.20)`. -/
theorem stableLevyMeasure_logCharacteristicFunction_eq
    (μ : ProbabilityMeasure ℝ) (α cMinus cPlus b : ℝ)
    (hμ : IsInfinitelyDivisible μ)
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (hcMinus : 0 ≤ cMinus) (hcPlus : 0 ≤ cPlus)
    (hcoeff : 0 < cMinus + cPlus)
    (htriple :
      HasLevyKhinchinRepresentation μ
        { sigma2 := 0, b := b, ν := stableLevyMeasure α cMinus cPlus })
    (hb :
      α ≠ 1 →
        b =
          (cPlus - cMinus) * stableIntegralI (-α) * Real.sin (Real.pi * α / 2))
    (t : ℝ) :
    Complex.log (charFun (μ : Measure ℝ) t) =
      if α = 1 then
        (((-|t| * (cPlus + cMinus) * (Real.pi / 2) : ℝ) : ℂ)) +
          ((((-|t| * (cPlus + cMinus) * Real.sign t * (cPlus - cMinus) *
                Real.log |t| : ℝ) : ℂ)) * Complex.I)
      else
        (((|t| ^ α * stableIntegralI (-α) * ((cPlus + cMinus) *
              Real.cos (Real.pi * α / 2)) : ℝ) : ℂ)) +
          ((((|t| ^ α * stableIntegralI (-α) * ((cPlus - cMinus) *
                Real.sin (Real.pi * α / 2)) : ℝ) : ℂ)) * Complex.I) := sorry

end MeasureTheory.ProbabilityMeasure
