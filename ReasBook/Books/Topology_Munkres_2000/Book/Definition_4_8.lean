module

public import Topology_Munkres_2000.Book.Definition_4_6
import Mathlib.Algebra.Order.Archimedean.Real.Basic

public section

/- Definition 4.8. The Archimedean ordering property of `ℝ`. -/
#check Real.instArchimedean
#check (exists_nat_gt : ∀ x : ℝ, ∃ n : ℕ, x < n)

namespace Real

/-- Definition 4.8. The positive integers are unbounded above in `ℝ`. -/
theorem not_bddAbove_positiveIntegers : ¬ BddAbove ℤ₊ := by
  rw [positiveIntegers_eq_range_pnatCast, not_bddAbove_iff]
  intro x
  obtain ⟨n, hn⟩ := exists_nat_gt x
  let m : ℕ+ := ⟨n + 1, Nat.succ_pos n⟩
  refine ⟨m, ⟨m, rfl⟩, hn.trans_le ?_⟩
  exact_mod_cast Nat.le_succ n

end Real
