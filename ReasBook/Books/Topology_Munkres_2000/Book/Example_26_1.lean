module

public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Sets.OpenCover

public section

/-- The integer-indexed family of open intervals `(n, n + 2)` in `ℝ`. -/
def integerIntervalCover (n : ℤ) : TopologicalSpace.Opens ℝ :=
  ⟨Set.Ioo (n : ℝ) ((n : ℝ) + 2), isOpen_Ioo⟩

/-- Membership in `integerIntervalCover n` is the pair of inequalities
`n < x < n + 2`. -/
theorem mem_integerIntervalCover (n : ℤ) (x : ℝ) :
    x ∈ integerIntervalCover n ↔ (n : ℝ) < x ∧ x < (n : ℝ) + 2 := Iff.rfl

/-- The intervals in `integerIntervalCover` cover `ℝ`. -/
theorem integerIntervalCover_isOpenCover :
    TopologicalSpace.IsOpenCover integerIntervalCover := by
  -- Choose the interval indexed one below the floor of each real number.
  refine TopologicalSpace.IsOpenCover.of_sets (fun _ ↦ isOpen_Ioo) ?_
  ext x
  simp only [Set.mem_iUnion, Set.mem_Ioo, Set.mem_univ, iff_true]
  refine ⟨⌊x⌋ - 1, ?_⟩
  constructor
  · have hfloor : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
    simp only [Int.cast_sub, Int.cast_one]
    linarith
  · have hnext : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one x
    simp only [Int.cast_sub, Int.cast_one]
    linarith

/-- Helper for Example 26.1: every finite family of the integer intervals misses a real point. -/
lemma finiteIntegerIntervalSubfamilyMissesPoint (s : Finset ℤ) :
    ∃ x : ℝ, ∀ n ∈ s, x ∉ integerIntervalCover n := by
  -- An upper bound for the finite index set yields an escape point two units farther right.
  obtain ⟨M, hM⟩ := Finset.exists_le s
  refine ⟨(M : ℝ) + 2, ?_⟩
  intro n hn hmem
  rw [mem_integerIntervalCover] at hmem
  have hcast : (n : ℝ) ≤ (M : ℝ) := Int.cast_le.mpr (hM n hn)
  linarith

/-- No finite subfamily of `integerIntervalCover` covers `ℝ`. -/
theorem integerIntervalCover_noFiniteSubcover (s : Finset ℤ) :
    ¬ TopologicalSpace.IsOpenCover (fun n : s ↦ integerIntervalCover n) := by
  -- A purported cover must contain the finite-family escape point, giving a contradiction.
  intro hcover
  obtain ⟨x, hx⟩ := finiteIntegerIntervalSubfamilyMissesPoint s
  obtain ⟨n, hn⟩ := hcover.exists_mem x
  exact hx n.1 n.2 hn

/-- Example 26.1: The real line `ℝ` is not compact. -/
theorem realLineNotCompact : ¬ CompactSpace ℝ := by
  -- The standard topology on `ℝ` has the canonical noncompactness instance.
  exact not_compactSpace_iff.mpr inferInstance
