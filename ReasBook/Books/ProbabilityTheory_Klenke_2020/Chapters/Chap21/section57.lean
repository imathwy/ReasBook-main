

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_21_57 (from Items/Chap21) -/
noncomputable section

/-- The dyadic partition sequence on `[0, ∞)`, whose `n`-th row consists of the times
`k 2^{-n}`. -/
def dyadicPartitionSequence (n k : ℕ) : NNReal :=
  (k : NNReal) / (2 : NNReal) ^ n

/-- A nonnegative time belongs to the `n`-th dyadic partition exactly when it is a multiple of the
mesh size `2^{-n}` with a natural-number coefficient. -/
theorem mem_partitionPointSet_dyadicPartitionSequence_iff {n : ℕ} {t : NNReal} :
    t ∈ partitionPointSet dyadicPartitionSequence n ↔
      ∃ k : ℕ, t = (k : NNReal) / (2 : NNReal) ^ n := by
  change t ∈ Set.range (dyadicPartitionSequence n) ↔
    ∃ k : ℕ, t = (k : NNReal) / (2 : NNReal) ^ n
  simp [dyadicPartitionSequence, eq_comm]

/-- Example 21.57: the dyadic partitions form an admissible partition sequence in the sense of
Definition 21.56. -/
instance instIsAdmissiblePartitionSequenceDyadicPartitionSequence :
    IsAdmissiblePartitionSequence dyadicPartitionSequence where
  zero_eq n := by
    simp [dyadicPartitionSequence]
  strictMono n := by
    refine strictMono_nat_of_lt_succ fun k ↦ ?_
    have hpow : 0 < (2 : NNReal) ^ n := by
      positivity
    have hk : (k : NNReal) < ((k + 1 : ℕ) : NNReal) := by
      exact_mod_cast Nat.lt_succ_self k
    rw [dyadicPartitionSequence, dyadicPartitionSequence]
    exact (div_lt_div_iff_of_pos_right hpow).2 hk
  nested n := by
    intro t ht
    rcases (Set.mem_range.mp <| by simpa [partitionPointSet] using ht) with ⟨k, rfl⟩
    change dyadicPartitionSequence n k ∈ Set.range (dyadicPartitionSequence (n + 1))
    refine ⟨2 * k, ?_⟩
    simp [dyadicPartitionSequence, pow_succ, mul_assoc, mul_comm, div_eq_mul_inv]
  tendsto_atTop n := by
    simpa [dyadicPartitionSequence, div_eq_mul_inv] using
      (tendsto_natCast_atTop_atTop.atTop_mul_const
        (show 0 < ((2 : NNReal) ^ n)⁻¹ by positivity))
  mesh_tendsto_zero := by
    sorry

/-- Example 21.57 supplies the chapter's standard dyadic instance of
`IsAdmissiblePartitionSequence`. -/
theorem dyadicPartitionSequence_isAdmissiblePartitionSequence :
    IsAdmissiblePartitionSequence dyadicPartitionSequence :=
  inferInstance
