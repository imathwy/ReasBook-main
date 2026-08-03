module

public import Mathlib.Algebra.Order.Interval.Set.SuccPred
public import Mathlib.Data.PNat.Order

public section

/- The section `S_{n}` consists of the positive integers less than `n`. -/
notation "S_{" n "}" => Set.Iio n

/- The notation `{1,…,n}` denotes the positive integers at most `n`. -/
notation "{1,…," n "}" => Set.Iic n

