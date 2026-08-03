module

public import Topology_Munkres_2000.Book.Definition_4_6

public section

namespace Real

/-- Proposition 4.3 (1): The set of positive integers is inductive. -/
theorem isInductive_positiveIntegers : IsInductive ℤ₊ := by
  rw [isInductive_iff]
  constructor
  · rw [mem_positiveIntegers_iff]
    intro A h_inductive
    exact (isInductive_iff A).mp h_inductive |>.1
  · intro x hx
    rw [mem_positiveIntegers_iff] at hx ⊢
    intro A h_inductive
    exact (isInductive_iff A).mp h_inductive |>.2 x (hx A h_inductive)

/-- Proposition 4.3 (2): An inductive set of positive integers is the entire set of positive
integers. -/
theorem eq_positiveIntegers_of_subset_of_isInductive (A : Set ℝ)
    (h_subset : A ⊆ ℤ₊) (h_inductive : IsInductive A) : A = ℤ₊ := by
  apply Set.Subset.antisymm h_subset
  intro x hx
  exact (mem_positiveIntegers_iff x).mp hx A h_inductive

end Real
