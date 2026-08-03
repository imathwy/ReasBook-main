module

public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Interval.Set.OrdConnected

/-- Exercise 16.7: The answer is no: in `ℝ`, a proper order-convex subset need
not be one of the four bounded intervals with distinct endpoints or one of the
four rays. -/
public theorem properOrdConnectedNotAlwaysIntervalOrRay :
    ¬ ∀ Y : Set ℝ, Y ⊂ Set.univ → Y.OrdConnected →
      ((∃ a b : ℝ, a < b ∧ Y = Set.Ioo a b) ∨
        (∃ a b : ℝ, a < b ∧ Y = Set.Ioc a b) ∨
        (∃ a b : ℝ, a < b ∧ Y = Set.Ico a b) ∨
        (∃ a b : ℝ, a < b ∧ Y = Set.Icc a b) ∨
        (∃ a : ℝ, Y = Set.Ioi a) ∨
        (∃ a : ℝ, Y = Set.Iio a) ∨
        (∃ a : ℝ, Y = Set.Ici a) ∨
        (∃ a : ℝ, Y = Set.Iic a)) := sorry
