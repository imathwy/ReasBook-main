import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_18
import ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_30

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

namespace ProbabilityTheory

/-- The Brownian path space carries its Borel `σ`-algebra. -/
local instance brownianPathSpaceMeasurableSpace : MeasurableSpace BrownianPathSpace :=
  borel BrownianPathSpace

local notation "W" => fun t (ω : BrownianPathSpace) ↦ ω t

/-- Every path in `BrownianPathSpace` is continuous, so the coordinate process has almost surely
continuous sample paths under any law on path space. -/
theorem hasAlmostSurelyContinuousPaths_brownianPathCoordinateProcess
    (μ : Measure BrownianPathSpace) :
    HasAlmostSurelyContinuousPaths μ W := by
  filter_upwards with ω
  simpa [HasAlmostSurelyContinuousPaths, processPath] using ω.continuous

/-- Translating the coordinate process by a constant preserves almost sure continuity of paths. -/
theorem hasAlmostSurelyContinuousPaths_shiftedBrownianPathCoordinateProcess
    (μ : Measure BrownianPathSpace) (x : ℝ) :
    HasAlmostSurelyContinuousPaths μ (fun t ω ↦ W t ω - x) := by
  filter_upwards with ω
  simpa [HasAlmostSurelyContinuousPaths, processPath] using ω.continuous.sub continuous_const

/-- Remark 21.34: on `C([0, ∞), ℝ)`, translating the canonical coordinate process by its starting
point is an owner-level bridge inside `IsBrownianMotionStartedAt`: the coordinate process is
Brownian motion started at `x` exactly when the shifted coordinate process is Brownian motion
started at `0`. -/
theorem isBrownianMotionStartedAt_brownianPathCoordinateProcess_iff_shifted
    (μ : Measure BrownianPathSpace) (x : ℝ) :
    IsBrownianMotionStartedAt μ W x ↔
      IsBrownianMotionStartedAt μ (fun t ω ↦ W t ω - x) 0 := sorry

end ProbabilityTheory
