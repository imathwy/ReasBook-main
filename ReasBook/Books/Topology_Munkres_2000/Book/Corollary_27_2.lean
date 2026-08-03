module

import Mathlib.Topology.UniformSpace.Real
import Mathlib.Topology.Order.Compact

public section

/- Corollary 27.2: Every closed interval in `ℝ` is compact. -/
#check (ConditionallyCompleteLinearOrder.isCompact_Icc :
  ∀ a b : ℝ, IsCompact (Set.Icc a b))
