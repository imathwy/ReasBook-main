module

public import Topology_Munkres_2000.Book.Definition_4_6.PositiveIntegers

public section

namespace Real

/-- Definition 4.6: The intersection-defined positive integers are exactly the real casts of
positive naturals. -/
theorem positiveIntegers_eq_range_pnatCast :
    ℤ₊ = Set.range (fun n : ℕ+ ↦ (n : ℝ)) := by
  -- One inclusion specializes intersection membership to the inductive cast range.
  apply Set.Subset.antisymm
  · intro x hx
    exact (mem_positiveIntegers_iff x).mp hx _ isInductive_range_pnatCast
  · intro x hx
    obtain ⟨n, rfl⟩ := hx
    -- The reverse inclusion uses positive-natural induction in every inductive set.
    rw [mem_positiveIntegers_iff]
    intro A hA
    exact pnatCast_mem_of_isInductive hA n

end Real
