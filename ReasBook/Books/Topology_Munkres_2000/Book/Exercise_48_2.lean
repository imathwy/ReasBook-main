module

public import Mathlib.Topology.Instances.Real.Lemmas

import Topology_Munkres_2000.Book.Example_48_1
import Mathlib.Topology.Instances.Irrational

public section

open Set

/-- Exercise 48.2: There is a countable cover of `ℝ` by subsets with empty interior. -/
theorem exists_real_cover_interior_eq_empty :
    ∃ A : ℕ → Set ℝ, (⋃ n, A n) = Set.univ ∧ ∀ n, interior (A n) = ∅ := by
  let A : ℕ → Set ℝ := fun n ↦ if n = 0 then {x | Irrational x} else range (fun q : ℚ ↦ q)
  refine ⟨A, ?_, ?_⟩
  · apply top_unique
    intro x _
    by_cases hx : Irrational x
    · exact mem_iUnion.2 ⟨0, by simp [A, hx]⟩
    · obtain ⟨q, rfl⟩ := exists_rat_of_not_irrational hx
      exact mem_iUnion.2 ⟨1, by simp [A]⟩
  · intro n
    by_cases hn : n = 0
    · subst n
      rw [show A 0 = {x | Irrational x} by simp [A], interior_eq_empty_iff_dense_compl]
      rw [show {x : ℝ | Irrational x}ᶜ = range (fun q : ℚ ↦ (q : ℝ)) by
        ext x
        simp [Irrational]]
      exact Rat.denseRange_cast
    · simpa [A, hn] using interior_ratCastRange_eq_empty
