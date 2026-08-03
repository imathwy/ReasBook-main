module

import Mathlib.Order.Interval.Set.Defs

/-
Definition 10.3. For a well-ordered type `X` and `α : X`, the section of `X`
by `α` is the strict initial interval `Set.Iio α = {x | x < α}`.
-/
#check Set.Iio
#check Set.mem_Iio
