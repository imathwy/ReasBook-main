module

public import Mathlib.Topology.Instances.Real.Lemmas

public section

namespace ReciprocalHyperbola

/-- The reciprocal hyperbola in `ℝ × ℝ`. -/
def set : Set (ℝ × ℝ) := {point | point.1 * point.2 = 1}

/-- Helper for Example 22.2: membership in the reciprocal hyperbola is characterized by
the product of the coordinates being one. -/
theorem mem_set (point : ℝ × ℝ) : point ∈ set ↔ point.1 * point.2 = 1 := by
  -- Expose the defining equation once at the construction's owner boundary.
  rfl


end ReciprocalHyperbola

end
