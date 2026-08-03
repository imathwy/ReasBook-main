module

public import Mathlib.Topology.Instances.Real.Lemmas

public section

namespace RealPlane

/-- The horizontal axis in the real plane. -/
def xAxis : Set (ℝ × ℝ) :=
  {p | p.2 = 0}

/-- Membership in the horizontal axis is equality of the second coordinate to zero. -/
theorem mem_xAxis_iff (p : ℝ × ℝ) :
    p ∈ xAxis ↔ p.2 = 0 := by
  -- Unfold the named axis once in its owner module to expose its defining equation.
  rfl

end RealPlane
