module

public import Topology_Munkres_2000.Book.Example_24_7.SineCurve
public import Mathlib.Analysis.Convex.Segment

public section

open Set

namespace TopologistsSineCurve

/-- Helper for Definition 61.4: the three-segment broken line adjoining the endpoints of the
topologist's sine curve. -/
def brokenLine : Set (ℝ × ℝ) :=
  segment ℝ (0, -1) (0, -2) ∪
    segment ℝ (0, -2) (1, -2) ∪
      segment ℝ (1, -2) (1, Real.sin 1)

/-- Definition 61.4. The closed topologist's sine curve as a subset of the plane. -/
def closedCarrier : Set (ℝ × ℝ) :=
  carrier ∪ brokenLine

/-- Helper for Definition 61.4: membership in the added broken line is membership in one of its
three segments. -/
theorem mem_brokenLine_iff (p : ℝ × ℝ) :
    p ∈ brokenLine ↔
      p ∈ segment ℝ (0, -1) (0, -2) ∨
        p ∈ segment ℝ (0, -2) (1, -2) ∨
          p ∈ segment ℝ (1, -2) (1, Real.sin 1) := by
  -- Unfold the broken line and associate union membership as three alternatives.
  simp only [brokenLine, Set.mem_union, or_assoc]

/-- Helper for Definition 61.4: membership in the closed curve is membership in the sine curve or
its added broken line. -/
theorem mem_closedCarrier_iff (p : ℝ × ℝ) :
    p ∈ closedCarrier ↔ p ∈ carrier ∨ p ∈ brokenLine := by
  -- Unfold the closed carrier to expose its two defining pieces.
  simp only [closedCarrier, Set.mem_union]

end TopologistsSineCurve
