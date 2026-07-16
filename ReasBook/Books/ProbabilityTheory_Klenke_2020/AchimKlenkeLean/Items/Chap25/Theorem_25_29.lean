import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap25.Theorem_25_17
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap25.ContinuousLocalMartingaleIto

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

local notation "TimeFiltration" => Filtration NNReal mΩ
local notation "Process" => NNReal → Ω → ℝ

variable {ℱ : TimeFiltration}

-- Proof sketch: enlarge the probability space by adding an independent Brownian motion, divide the
-- martingale increments by the square-root bracket density on the set where that density is
-- positive, fill in the zero-density set with the independent Brownian motion, and then apply the
-- bracket characterization of Brownian motion to the constructed process.
/-- Theorem 25.29: if `M` is a continuous local martingale with `M 0 = 0` and absolutely
continuous square variation, then on a suitable extension of the underlying probability space
there exists a Brownian motion `W` such that the pulled-back martingale is realized as the Brownian
local Itô integral with coefficient `sqrt (d⟨M⟩ / dt)`. The extension is encoded by an auxiliary
space, a probability law, a measure-preserving projection to the original space, a filtration, and
a Brownian motion on the extension; local square integrability of the pulled-back coefficient is
kept internal to the canonical predicate `IsBrownianLocalItoIntegral`. -/
theorem exists_brownian_representation_extension
    {M : Process} (hM : IsContinuousLocalMartingale ℱ μ M) (hM0 : M 0 = 0)
    (hbr : HasAbsolutelyContinuousSquareVariation M hM) :
    ∃ (Ω' : Type u) (mΩ' : MeasurableSpace Ω') (law : ProbabilityMeasure Ω')
      (lift : Ω' → Ω)
      (filtration : Filtration NNReal mΩ')
      (brownian : NNReal → Ω' → ℝ),
      MeasurePreserving lift (law : Measure Ω') μ ∧
        IsBrownianLocalItoIntegral filtration (law : Measure Ω') brownian
          (pullbackProcess lift (squareVariationDensityRoot hbr))
          (pullbackProcess lift M) := sorry

/-- Theorem 25.29 in canonical project-facing form: when `M 0 = 0`, the Brownian extension
representation gives the owner-level stochastic-integral relation saying that `M` realizes
`∫ 1 dM`. Since `M` already starts from `0`, the centered driver appearing in
`IsContinuousLocalMartingaleItoIntegral` is just `M` itself. -/
theorem continuousLocalMartingale_self_isContinuousLocalMartingaleItoIntegral
    {M : Process} (hM : IsContinuousLocalMartingale ℱ μ M) (hM0 : M 0 = 0)
    (hbr : HasAbsolutelyContinuousSquareVariation M hM) :
    IsContinuousLocalMartingaleItoIntegral hbr 1 M := sorry

end ProbabilityTheory
