import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped MeasureTheory

universe u

namespace MeasureTheory

variable {Ω : Type u} {mΩ : MeasurableSpace Ω}

namespace Filtration

/-- Definition 21.22: A filtration on `ℝ≥0` satisfies the usual conditions if it is right
continuous in the canonical mathlib sense `Filtration.IsRightContinuous` and if the initial
`σ`-algebra `ℱ 0` is `μ`-complete, equivalently if the trimmed measure `μ.trim (ℱ.le 0)` is
complete. -/
class UsualConditions (ℱ : Filtration NNReal mΩ) (μ : Measure Ω) : Prop extends
    ℱ.IsRightContinuous, Measure.IsComplete (μ.trim (ℱ.le 0))

/-- Under the usual conditions, each time-`t` σ-algebra in the filtration is `μ`-complete. -/
instance (ℱ : Filtration NNReal mΩ) (μ : Measure Ω) [UsualConditions ℱ μ] (t : NNReal) :
    Measure.IsComplete (μ.trim (ℱ.le t)) := sorry

end Filtration

end MeasureTheory
