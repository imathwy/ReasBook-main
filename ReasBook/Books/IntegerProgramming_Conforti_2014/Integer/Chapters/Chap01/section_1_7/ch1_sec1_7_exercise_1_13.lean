import Mathlib

-- Semantic recall note: no `lean_leansearch` tool was available in this session.
-- Declarations for this item will be appended below by the statement pipeline.

/-- The first integer set from Exercise 1.13, viewed inside `ℝ × ℝ`. -/
def exercise_1_13_first_set : Set (ℝ × ℝ) :=
  { p | ∃ m n : ℤ,
      0 ≤ m ∧
      0 ≤ n ∧
      m + n ≤ 2 ∧
      m - n ≤ 1 ∧
      n - m ≤ 1 ∧
      p = ((m : ℝ), (n : ℝ)) }

/-- The second mixed-integer set from Exercise 1.13, viewed inside `ℝ × ℝ`. -/
def exercise_1_13_second_set : Set (ℝ × ℝ) :=
  { p | ∃ m : ℤ,
      0 ≤ m ∧
      (m : ℝ) + p.2 ≥ (8 : ℝ) / 5 ∧
      m ≤ 2 ∧
      0 ≤ p.2 ∧
      p.1 = m ∧
      p.2 ≤ 2 }

/-- Exercise 1.13 (1): the convex hull of the first listed integer set is the unit square. -/
theorem exercise_1_13_first_convex_hull :
    convexHull ℝ exercise_1_13_first_set =
      { p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 } := sorry

/-- Exercise 1.13 (2): the convex hull of the second listed mixed-integer
set is the polygon cut out by its facet inequalities. -/
theorem exercise_1_13_second_convex_hull :
    convexHull ℝ exercise_1_13_second_set =
      { p |
          0 ≤ p.1 ∧
          p.1 ≤ 2 ∧
          0 ≤ p.2 ∧
          p.2 ≤ 2 ∧
          p.1 + p.2 ≥ (8 : ℝ) / 5 ∧
          3 * p.1 + 5 * p.2 ≥ (6 : ℝ) } := sorry
