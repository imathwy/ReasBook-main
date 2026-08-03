module

public import Mathlib.Data.Real.Basic
public import Topology_Munkres_2000.Book.Example_3_4.Fibers

public section

/-- The coordinate-sum map on the real plane. -/
def coordinateSum (p : ℝ × ℝ) : ℝ :=
  p.1 + p.2

/-- The line of slope `-1` on which the coordinate sum is `c`. -/
def negSlopeLine (c : ℝ) : Set (ℝ × ℝ) :=
  {p | coordinateSum p = c}

/-- The collection of all lines in the real plane parallel to `y = -x`. -/
def negSlopeLines : Set (Set (ℝ × ℝ)) :=
  Set.range negSlopeLine

/-- The equivalence relation on the real plane given by equal coordinate sums. -/
def coordinateSumSetoid : Setoid (ℝ × ℝ) :=
  Setoid.ker coordinateSum

/-- Two points are related by `coordinateSumSetoid` exactly when their coordinate sums agree. -/
theorem coordinateSumSetoid_rel_iff (p q : ℝ × ℝ) :
    coordinateSumSetoid p q ↔ p.1 + p.2 = q.1 + q.2 :=
  Setoid.ker_def

/-- Example 3.5 (1): The collection of lines parallel to `y = -x` partitions the real plane. -/
theorem negSlopeLinesPartition :
    Setoid.IsPartition negSlopeLines := by
  refine ⟨?_, fun p ↦ ?_⟩
  · rintro ⟨c, hc⟩
    have hp : (c, 0) ∈ negSlopeLine c := by
      simp [negSlopeLine, coordinateSum]
    rw [hc] at hp
    exact hp
  · refine ⟨negSlopeLine (coordinateSum p), ⟨⟨coordinateSum p, rfl⟩, rfl⟩, ?_⟩
    rintro s ⟨⟨c, rfl⟩, hp⟩
    congr
    exact hp.symm

/-- Example 3.5 (2): This partition is the collection of classes for equality of coordinate sums. -/
theorem coordinateSumSetoid_classes :
    coordinateSumSetoid.classes = negSlopeLines :=
  Setoid.classes_ker_eq_fibers coordinateSum fun c ↦ ⟨(c, 0), by simp [coordinateSum]⟩
