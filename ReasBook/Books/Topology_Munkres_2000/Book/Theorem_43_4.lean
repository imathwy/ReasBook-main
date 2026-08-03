module

import Mathlib.Topology.Metrizable.CompletelyMetrizable

public section

/- Theorem 43.4: The product space `ℝ^ω`, represented by `ℕ → ℝ`, admits a
metric inducing its product topology with respect to which it is complete. -/
#check (inferInstance : TopologicalSpace.IsCompletelyMetrizableSpace (ℕ → ℝ))
