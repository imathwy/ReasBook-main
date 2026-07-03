import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_21_56 (from Items/Chap21) -/
open Filter
open scoped ENNReal Topology

noncomputable section

variable (P : ℕ → ℕ → NNReal)

/-- The point set of the `n`-th time partition associated with the sequence `P`. -/
def partitionPointSet (n : ℕ) : Set NNReal :=
  Set.range (P n)

/-- The mesh size of the `n`-th partition, written as the supremum of the successive gaps in the
ordered partition row. We value it in `ℝ≥0∞` so that unbounded rows retain their correct infinite
mesh size. -/
def partitionMesh (n : ℕ) : ℝ≥0∞ :=
  ⨆ k : ℕ, edist (P n k) (P n (k + 1))

/-- The truncated partition `P^n_{S,T} = P^n ∩ [S, T)`. -/
def partitionSlice (n : ℕ) (S T : NNReal) : Set NNReal :=
  partitionPointSet P n ∩ Set.Ico S T

/-- The initial truncation `P^n_T = P^n ∩ [0, T)`. -/
def partitionInitialSegment (n : ℕ) (T : NNReal) : Set NNReal :=
  partitionSlice P n 0 T

/-- If `t = P n k`, then `partitionNextPointUpTo P n k T` is the truncated successor
`P n (k + 1) ∧ T`. -/
def partitionNextPointUpTo (n k : ℕ) (T : NNReal) : NNReal :=
  min (P n (k + 1)) T

/-- Definition 21.56: a sequence `P n k` of nonnegative times is an admissible partition sequence
when each row starts at `0` and is strictly increasing, the associated point sets are nested, each
row tends to `∞`, and the mesh size tends to `0` as `n → ∞`. -/
class IsAdmissiblePartitionSequence (P : ℕ → ℕ → NNReal) : Prop where
  /-- Every partition starts at the initial time `0`. -/
  zero_eq : ∀ n : ℕ, P n 0 = 0
  /-- For each `n`, the partition times form a strictly increasing sequence. -/
  strictMono : ∀ n : ℕ, StrictMono (P n)
  /-- The partitions are increasing with respect to refinement. -/
  nested : ∀ n : ℕ, partitionPointSet P n ⊆ partitionPointSet P (n + 1)
  /-- Each partition sequence is unbounded above, equivalently `sup P^n = ∞`. -/
  tendsto_atTop : ∀ n : ℕ, Tendsto (P n) atTop atTop
  /-- The mesh size of the partitions converges to `0` in `ℝ≥0∞`. -/
  mesh_tendsto_zero : Tendsto (fun n : ℕ ↦ partitionMesh P n) atTop (𝓝 0)

variable [hP : IsAdmissiblePartitionSequence P]

/-- In an admissible partition sequence, each fixed row is strictly increasing. -/
instance instStrictMono_of_isAdmissiblePartitionSequence (n : ℕ) :
    StrictMono (P n) :=
  hP.strictMono n

-- Proof sketch: use the `tendsto_atTop` field of `IsAdmissiblePartitionSequence` for the fixed
-- row `n` and threshold `T`.
/-- Every admissible partition row eventually reaches any prescribed time horizon `T`. -/
theorem exists_partition_index_le_time (n : ℕ) (T : NNReal) :
    ∃ k : ℕ, T ≤ P n k := sorry

/-- The first index in the `n`-th partition row whose time is at least `T`. -/
def partitionBoundIndex (n : ℕ) (T : NNReal) : ℕ :=
  Nat.find <| exists_partition_index_le_time P n T

/-- The chosen partition bound index indeed reaches or passes the time horizon `T`. -/
theorem le_partitionBoundIndex_time (n : ℕ) (T : NNReal) :
    T ≤ P n (partitionBoundIndex P n T) :=
  Nat.find_spec <| exists_partition_index_le_time P n T
