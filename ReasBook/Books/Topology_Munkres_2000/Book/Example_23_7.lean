module

import Mathlib.Topology.Connected.PathConnected

/- Example 23.7: The countable product `ℕ → ℝ`, with the product topology, is connected. -/
#check (inferInstance : ConnectedSpace (ℕ → ℝ))
