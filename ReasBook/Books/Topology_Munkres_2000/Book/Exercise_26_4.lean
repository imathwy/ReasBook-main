module

public import Mathlib.Topology.Instances.Rat
public import Mathlib.Topology.Instances.RatLemmas
public import Mathlib.Topology.MetricSpace.Bounded

public section

universe u

/- Exercise 26.4 (1): Every compact subset of a metric space is bounded. -/
#check (IsCompact.isBounded :
  ∀ {X : Type u} [MetricSpace X] {K : Set X}, IsCompact K → Bornology.IsBounded K)

/- Exercise 26.4 (2): Every compact subset of a metric space is closed. -/
#check (IsCompact.isClosed :
  ∀ {X : Type u} [MetricSpace X] {K : Set X}, IsCompact K → IsClosed K)

/- Exercise 26.4 (3): The rational unit interval is closed. -/
#check (isClosed_Icc : IsClosed (Set.Icc (0 : ℚ) 1))

/- Exercise 26.4 (4): The rational unit interval is bounded. -/
#check (Rat.totallyBounded_Icc (0 : ℚ) 1).isBounded

/-- Exercise 26.4 (5): The rational unit interval is not compact. -/
theorem ratUnitIntervalNotCompact :
    ¬ IsCompact (Set.Icc (0 : ℚ) 1) := by
  -- Compact subsets of `ℚ` have empty interior.
  intro hcompact
  have hinterior : interior (Set.Icc (0 : ℚ) 1) = ∅ :=
    Rat.interior_compact_eq_empty hcompact
  -- The interval interior is the nonempty open interval containing `1 / 2`.
  rw [interior_Icc] at hinterior
  have hmidpoint : (1 / 2 : ℚ) ∈ Set.Ioo 0 1 := by
    norm_num
  rw [hinterior] at hmidpoint
  simp at hmidpoint
