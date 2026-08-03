module

public import Mathlib.Data.PNat.Basic
public import Mathlib.Data.Real.Basic

public section

/-- The subspace of `ℝ` consisting of `0` and the reciprocals of positive integers. -/
@[expose] def reciprocalSequenceSubspace : Set ℝ :=
  insert 0 (Set.range fun n : ℕ+ ↦ 1 / (n : ℝ))

/-- Membership in `reciprocalSequenceSubspace` means being `0` or the reciprocal of a
positive integer. -/
theorem mem_reciprocalSequenceSubspace (x : ℝ) :
    x ∈ reciprocalSequenceSubspace ↔ x = 0 ∨ ∃ n : ℕ+, x = 1 / (n : ℝ) := by
  -- Unfolding the subspace gives exactly the insert-and-range membership condition.
  rw [reciprocalSequenceSubspace, Set.mem_insert_iff, Set.mem_range]
  constructor
  · rintro (rfl | ⟨n, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨n, rfl⟩
  · rintro (rfl | ⟨n, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨n, rfl⟩

/-- The positive-integer presentation of `reciprocalSequenceSubspace` agrees with the
shifted natural-number sequence presentation. -/
theorem reciprocalSequenceSubspace_eq_insert_range_nat :
    reciprocalSequenceSubspace = insert 0 (Set.range fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) := by
  -- Reindex positive naturals by their natural-number predecessors.
  rw [reciprocalSequenceSubspace]
  congr 1
  ext x
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨n.natPred, ?_⟩
    have denominator_eq : (n.natPred : ℝ) + 1 = (n : ℝ) := by
      exact_mod_cast PNat.natPred_add_one n
    exact congrArg (fun denominator : ℝ ↦ 1 / denominator) denominator_eq
  · rintro ⟨n, rfl⟩
    refine ⟨n.succPNat, ?_⟩
    simp only [Nat.succPNat_coe, Nat.cast_succ]
