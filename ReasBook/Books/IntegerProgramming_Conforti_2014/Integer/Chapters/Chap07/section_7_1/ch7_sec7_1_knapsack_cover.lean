import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Basic

section KnapsackCover

variable {n : ℕ}

/-- A finite index set is a cover for the `0,1` knapsack inequality
`∑ i, weights i * x i ≤ capacity` when its weight sum exceeds `capacity`. -/
class IsKnapsackCover
    (weights : Fin n → ℕ) (capacity : ℕ) (C : Finset (Fin n)) : Prop where
  /-- The weight sum on `C` is larger than the knapsack capacity. -/
  sum_gt_capacity : capacity < C.sum weights

/-- Proofs of `IsKnapsackCover weights capacity C` are subsingletons because this is a
proposition. -/
instance isKnapsackCover_subsingleton
    (weights : Fin n → ℕ) (capacity : ℕ) (C : Finset (Fin n)) :
    Subsingleton (IsKnapsackCover weights capacity C) :=
  inferInstance

/-- `IsKnapsackCover weights capacity C` unfolds to the strict overweight inequality on `C`. -/
theorem isKnapsackCover_iff
    (weights : Fin n → ℕ) (capacity : ℕ) (C : Finset (Fin n)) :
    IsKnapsackCover weights capacity C ↔ capacity < C.sum weights := sorry

/-- A cover is minimal when deleting any chosen index destroys the cover property. -/
class IsMinimalKnapsackCover
    (weights : Fin n → ℕ) (capacity : ℕ) (C : Finset (Fin n)) : Prop
    extends IsKnapsackCover weights capacity C where
  /-- Removing any index from a minimal cover makes the remaining set feasible. -/
  erase_sum_le : ∀ i ∈ C, (C.erase i).sum weights ≤ capacity

/-- An `IsMinimalKnapsackCover` hypothesis canonically gives the underlying cover. -/
instance isMinimalKnapsackCover_to_isKnapsackCover
    (weights : Fin n → ℕ) (capacity : ℕ) (C : Finset (Fin n))
    (h : IsMinimalKnapsackCover weights capacity C) :
    IsKnapsackCover weights capacity C :=
  inferInstance

/-- Proofs of `IsMinimalKnapsackCover weights capacity C` are subsingletons because this is a
proposition. -/
instance isMinimalKnapsackCover_subsingleton
    (weights : Fin n → ℕ) (capacity : ℕ) (C : Finset (Fin n)) :
    Subsingleton (IsMinimalKnapsackCover weights capacity C) :=
  inferInstance

/-- `IsMinimalKnapsackCover weights capacity C` means that `C` is a cover and becomes feasible
after deleting any chosen index. -/
theorem isMinimalKnapsackCover_iff
    (weights : Fin n → ℕ) (capacity : ℕ) (C : Finset (Fin n)) :
    IsMinimalKnapsackCover weights capacity C ↔
      IsKnapsackCover weights capacity C ∧
        ∀ i ∈ C, (C.erase i).sum weights ≤ capacity := sorry

/-- The right-hand side of the cover inequality attached to `C`. -/
def cover_inequality_rhs (C : Finset (Fin n)) : ℝ :=
  (C.card : ℝ) - 1

/-- `cover_inequality_rhs C` unfolds to `|C| - 1`. -/
theorem cover_inequality_rhs_eq
    (C : Finset (Fin n)) :
    cover_inequality_rhs C = (C.card : ℝ) - 1 := sorry

end KnapsackCover
