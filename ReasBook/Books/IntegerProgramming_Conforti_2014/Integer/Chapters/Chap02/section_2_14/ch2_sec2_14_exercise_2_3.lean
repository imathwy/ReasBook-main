import Mathlib

open scoped BigOperators

-- Semantic search tooling was unavailable in this session, so this file uses the
-- standard explicit unit-weight knapsack construction.

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/-- A finite index set is a cover for the 0,1 knapsack inequality `∑ i, a i * x i ≤ b`
when its weight sum exceeds the capacity `b`. -/
def IsKnapsackCover {α : Type u} (weights : α → ℕ) (capacity : ℕ) (C : Finset α) : Prop :=
  capacity < ∑ i ∈ C, weights i

/-- A cover is minimal when deleting any chosen index destroys the cover property. -/
def IsMinimalKnapsackCover {α : Type u} [DecidableEq α] (weights : α → ℕ) (capacity : ℕ)
    (C : Finset α) : Prop :=
  IsKnapsackCover weights capacity C ∧
    ∀ i ∈ C, ∑ j ∈ C.erase i, weights j ≤ capacity

/-- The family used for Exercise 2.3 assigns unit weight to each of the `2m` variables. -/
def exercise_2_3_unit_weight_knapsack_weights (m : ℕ) : Fin (2 * m) → ℕ :=
  fun _ => 1

/-- The family used for Exercise 2.3 has capacity `m - 1`. -/
def exercise_2_3_unit_weight_knapsack_capacity (m : ℕ) : ℕ :=
  m - 1

/-- Exercise 2.3. For the 0,1 knapsack set with `n = 2m` unit-weight variables and
capacity `m - 1`, the minimal covers are exactly the subsets of cardinality `m`. -/
theorem exercise_2_3_unit_weight_knapsack_minimal_cover_iff_card
    (m : ℕ) (C : Finset (Fin (2 * m))) :
    IsMinimalKnapsackCover
        (exercise_2_3_unit_weight_knapsack_weights m)
        (exercise_2_3_unit_weight_knapsack_capacity m)
        C ↔
      C.card = m := sorry

/-- The explicit family above has `Nat.choose (2 * m) m` minimal covers, which is
exponential in the number `n = 2m` of variables. -/
theorem exercise_2_3_unit_weight_knapsack_minimal_covers_card
    (m : ℕ) :
    Fintype.card
      {C : Finset (Fin (2 * m)) //
        IsMinimalKnapsackCover
          (exercise_2_3_unit_weight_knapsack_weights m)
          (exercise_2_3_unit_weight_knapsack_capacity m)
          C} =
      Nat.choose (2 * m) m := sorry
