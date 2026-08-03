module

import Mathlib.Data.Real.Basic

/- Definition 4.4 (1). A real number `x` is positive when `0 < x` and negative
when `x < 0`. -/
#check (fun x : ℝ ↦ 0 < x)
#check (fun x : ℝ ↦ x < 0)

/- Definition 4.4 (2). The positive reals are `Set.Ioi (0 : ℝ)`, and the
nonnegative reals are `Set.Ici (0 : ℝ)`. -/
#check (Set.Ioi (0 : ℝ) : Set ℝ)
#check (Set.Ici (0 : ℝ) : Set ℝ)

/- Definition 4.4 (3). The canonical owner of the operations and laws in
properties (1)-(5) is `Field`. -/
#check Field

/- Definition 4.4 (4). Modern mathlib represents an ordered field `K` by the
simultaneous assumptions `[Field K]`, `[LinearOrder K]`, and
`[IsStrictOrderedRing K]`. -/
#check Field
#check LinearOrder
#check IsStrictOrderedRing
