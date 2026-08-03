module

public import Mathlib.Topology.Instances.Int

public section

universe u

/- Proposition 45.1 (1): Every compact metric space is complete. -/
#check fun (X : Type u) [MetricSpace X] [CompactSpace X] ↦
  (inferInstance : CompleteSpace X)

/- Proposition 45.1 (2): The complete metric space ℤ is not compact, so the
converse does not hold. -/
#check (inferInstance : CompleteSpace ℤ)
#check (not_compactSpace_iff.mpr (inferInstance : NoncompactSpace ℤ) : ¬ CompactSpace ℤ)
