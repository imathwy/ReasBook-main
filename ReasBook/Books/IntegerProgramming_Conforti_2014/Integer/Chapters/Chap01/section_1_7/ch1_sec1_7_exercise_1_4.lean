import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tool `lean_leansearch` was not available in this environment; the statement
-- shape below follows the local Chapter 1 integer-programming precedent.

/-- Feasible nonnegative integer points for the pure integer program from Exercise 1.4. -/
def exercise_1_4_feasible (x1 x2 : Nat) : Prop :=
  x2 ≤ x1 ∧ 6 * x1 + 2 * x2 ≤ 21

/-- Objective function for the pure integer program from Exercise 1.4. -/
def exercise_1_4_objective (x1 x2 : Nat) : Nat :=
  2 * x1 + x2

/-- Exercise 1.4 (1): every feasible nonnegative integer point has objective value at most `7`. -/
theorem exercise_1_4_objective_le_seven {x1 x2 : Nat}
    (hfeas : exercise_1_4_feasible x1 x2) :
    exercise_1_4_objective x1 x2 ≤ 7 := sorry

/-- Exercise 1.4 (2): the point `(3, 1)` is feasible for the given pure integer program. -/
theorem exercise_1_4_optimal_point_feasible :
    exercise_1_4_feasible 3 1 := sorry

/-- Exercise 1.4 (3): the feasible point `(3, 1)` attains objective value `7`. -/
theorem exercise_1_4_optimal_point_objective :
    exercise_1_4_objective 3 1 = 7 := sorry
