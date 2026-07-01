import Mathlib
import AchimKlenkeLean.Items.Chap21.Definition_21_8
import AchimKlenkeLean.Items.Chap21.Definition_21_58

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/- Corollary 21.65 is a `source-facing` process-level consequence in the Brownian-motion API.
Its core/canonical owner is `IsBrownianMotion`; the pathwise dyadic-bracket predicate
`HasQuadraticCovariationAlong` is only the `bridge/view` used in the almost-sure conclusion.
The primitive data are the two Brownian processes and independence of their process paths. -/

-- Proof sketch: the processes `((W + Wtilde) / √2)` and `((W - Wtilde) / √2)` are again Brownian
-- motions when `W` and `Wtilde` are independent. Remark 21.61 gives their square brackets as the
-- identity path, and polarization then yields vanishing mixed covariation.
/-- Corollary 21.65: if `W` and `Wtilde` are independent Brownian motions, then almost every pair
of sample paths has vanishing dyadic quadratic covariation; equivalently, `⟪W, Wtilde⟫_T = 0` for
every `T ≥ 0`. -/
theorem covariation_ae_eq_zero_of_indep_brownian
    {μ : Measure Ω} {W Wtilde : NNReal → Ω → ℝ}
    (hW : IsBrownianMotion μ W)
    (hWtilde : IsBrownianMotion μ Wtilde)
    (hindep :
      IndepFun (fun ω ↦ fun t : NNReal ↦ W t ω) (fun ω ↦ fun t : NNReal ↦ Wtilde t ω) μ) :
    ∀ᵐ ω ∂μ,
      ∀ hWω : Continuous (processPath W ω),
        ∀ hWtildeω : Continuous (processPath Wtilde ω),
          HasQuadraticCovariationAlong
            ⟨processPath W ω, hWω⟩
            ⟨processPath Wtilde ω, hWtildeω⟩
            0 := sorry

end ProbabilityTheory
