module

import Mathlib.Order.Interval.Set.Defs

/-
Definition 14.4. For `a` in an ordered type, the rays determined by `a` are
`Set.Ioi a = {x | a < x}`, `Set.Iio a = {x | x < a}`,
`Set.Ici a = {x | a ≤ x}`, and `Set.Iic a = {x | x ≤ a}`. The first two are
called open rays, and the last two are called closed rays.
-/
#check Set.Ioi
#check Set.Iio
#check Set.Ici
#check Set.Iic
#check Set.mem_Ioi
#check Set.mem_Iio
#check Set.mem_Ici
#check Set.mem_Iic
