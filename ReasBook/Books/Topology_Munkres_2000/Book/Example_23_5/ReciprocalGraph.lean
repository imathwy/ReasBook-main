module

public import Mathlib.Topology.Instances.Real.Lemmas

public section

namespace RealPlane

/-- The graph of `x ↦ 1 / x` over the positive real numbers. -/
def positiveReciprocalGraph : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ p.2 = 1 / p.1}

/-- Membership in the positive reciprocal graph. -/
theorem mem_positiveReciprocalGraph (p : ℝ × ℝ) :
    p ∈ positiveReciprocalGraph ↔ 0 < p.1 ∧ p.2 = 1 / p.1 :=
  Iff.rfl

end RealPlane
