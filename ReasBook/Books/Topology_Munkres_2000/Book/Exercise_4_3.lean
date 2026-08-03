module

public import Topology_Munkres_2000.Book.Proposition_4_3

public section

namespace Real

/-- Exercise 4.3 (1): The intersection of an arbitrary collection of inductive subsets of
`ℝ` is inductive. -/
theorem isInductive_sInter (𝒜 : Set (Set ℝ))
    (h𝒜 : ∀ A ∈ 𝒜, IsInductive A) : IsInductive (⋂₀ 𝒜) := by
  rw [isInductive_iff]
  constructor
  · rw [Set.mem_sInter]
    intro A hA
    exact (isInductive_iff A).mp (h𝒜 A hA) |>.1
  · intro x hx
    rw [Set.mem_sInter] at hx ⊢
    intro A hA
    exact (isInductive_iff A).mp (h𝒜 A hA) |>.2 x (hx A hA)

-- Exercise 4.3 (2): The set of positive integers is inductive.
#check isInductive_positiveIntegers

-- Exercise 4.3 (3): An inductive set of positive integers is the entire set of positive integers.
#check eq_positiveIntegers_of_subset_of_isInductive

end Real
