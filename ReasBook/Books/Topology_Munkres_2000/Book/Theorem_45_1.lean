module

public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.MetricSpace.Defs

public section

universe u

/-- Theorem 45.1. A metric space is compact if and only if it is complete and
totally bounded. -/
theorem compactSpace_iff_completeSpace_totallyBounded
    {X : Type u} [MetricSpace X] :
    CompactSpace X ↔ CompleteSpace X ∧ TotallyBounded (Set.univ : Set X) := by
  rw [← isCompact_univ_iff, isCompact_iff_totallyBounded_isComplete,
    completeSpace_iff_isComplete_univ, and_comm]

end
