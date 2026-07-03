import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition I.3-extra-5: `AddCircle.homeomorphCircle'` is the canonical identification of
`Real.Angle = ℝ / (2 * π)ℤ` with the complex unit circle `Circle`; under this identification, the
inverse sends a unit complex number to its argument class modulo `2 * π`. -/
recall AddCircle.homeomorphCircle'

/- `Circle.exp_arg` states that sending a point of the unit circle to its argument class modulo
`2 * π` and then exponentiating returns the original point. -/
#check Circle.exp_arg

/- `Real.Angle.arg_toCircle` states that taking the point of the unit circle corresponding to an
angle class and then taking its argument class returns the original class modulo `2 * π`. -/
#check Real.Angle.arg_toCircle
