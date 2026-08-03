module

public import Mathlib.Data.Int.SuccPred

public section

/-- Proposition 4.4: there is no integer strictly between `n` and `n + 1`. -/
theorem Int.not_exists_between_add_one (n : ℤ) :
    ¬ ∃ a : ℤ, n < a ∧ a < n + 1 := by
  rintro ⟨a, hna, han⟩
  exact (not_lt_of_ge (Int.lt_add_one_iff.mp han)) hna
