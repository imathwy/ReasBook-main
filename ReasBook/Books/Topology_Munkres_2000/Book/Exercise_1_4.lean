module

public import Mathlib.Data.Real.Basic

public section

/-- Exercise 1.4 (1): The negation of every member of `A` having its square in `B`. -/
theorem notForallSquareMem_iff (A B : Set ℝ) :
    (¬ ∀ a, a ∈ A → a ^ 2 ∈ B) ↔ ∃ a, a ∈ A ∧ a ^ 2 ∉ B := by
  simp

/-- Exercise 1.4 (2): The negation of some member of `A` having its square in `B`. -/
theorem notExistsSquareMem_iff (A B : Set ℝ) :
    (¬ ∃ a, a ∈ A ∧ a ^ 2 ∈ B) ↔ ∀ a, a ∈ A → a ^ 2 ∉ B := by
  simp

/-- Exercise 1.4 (3): The negation of every member of `A` having its square outside `B`. -/
theorem notForallSquareNotMem_iff (A B : Set ℝ) :
    (¬ ∀ a, a ∈ A → a ^ 2 ∉ B) ↔ ∃ a, a ∈ A ∧ a ^ 2 ∈ B := by
  simp

/-- Exercise 1.4 (4): The negation of some nonmember of `A` having its square in `B`. -/
theorem notExistsOutsideSquareMem_iff (A B : Set ℝ) :
    (¬ ∃ a, a ∉ A ∧ a ^ 2 ∈ B) ↔ ∀ a, a ∉ A → a ^ 2 ∉ B := by
  simp
