module

import Mathlib.Order.Interval.Set.Defs

/-
Definition 14.2. For `a < b` in a simply ordered set, the four intervals
determined by `a` and `b` are `Set.Ioo a b = {x | a < x ∧ x < b}`,
`Set.Ioc a b = {x | a < x ∧ x ≤ b}`, `Set.Ico a b = {x | a ≤ x ∧ x < b}`,
and `Set.Icc a b = {x | a ≤ x ∧ x ≤ b}`. They are respectively called open,
half-open, half-open, and closed intervals.
-/
#check Set.Ioo
#check Set.Ioc
#check Set.Ico
#check Set.Icc
#check Set.mem_Ioo
#check Set.mem_Ioc
#check Set.mem_Ico
#check Set.mem_Icc
