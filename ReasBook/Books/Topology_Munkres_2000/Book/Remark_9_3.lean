module

import Mathlib.Data.PNat.Basic
import Mathlib.Order.Bounds.Basic

/- Remark 9.3. For `h : ℕ+ → C`, the set `Set.Iio i` consists of the positive
indices before `i`. Thus `Set.univ \ h '' Set.Iio i` is the set of values of
`C` unused before `i`, and `IsLeast.unique` shows that its least element—and
hence the prescribed value `h i`—is unique. -/
#check (IsLeast.unique :
  ∀ {C : Set ℕ+} {i : ℕ+} {h : ℕ+ → C} {x y : C},
    IsLeast (Set.univ \ h '' Set.Iio i) x →
      IsLeast (Set.univ \ h '' Set.Iio i) y → x = y)
