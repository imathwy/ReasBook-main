

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Remark_21_23 (from Items/Chap21) -/
open MeasureTheory
open scoped MeasureTheory

universe u

namespace MeasureTheory

variable {Ω : Type u} {mΩ : MeasurableSpace Ω}

namespace Filtration

local notation:arg ℱ "^+*[" μ "]" => completed_right_continuous_filtration μ ℱ

/- Remark 21.23 is a `bridge/view`: the source says the completed right-continuous filtration
satisfies the usual conditions, and the chapter owner abstraction for that property is
`Filtration.UsualConditions`. Package the existing theorem
`completed_right_continuous_filtration_usual_conditions` for `ℱ^+*[μ]` into the owner instance
instead of
restating its fields locally. -/
instance completed_right_continuous_filtration_usualConditions
    (μ : Measure Ω) (ℱ : Filtration NNReal mΩ) :
    UsualConditions (ℱ^+*[μ]) μ.completion := by
  exact completed_right_continuous_filtration_usual_conditions μ ℱ

end Filtration

end MeasureTheory
