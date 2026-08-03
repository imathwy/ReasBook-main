module

import Mathlib.Data.PNat.Interval
import Mathlib.Topology.Instances.PNat
import Mathlib.Topology.Instances.Discrete

/- Example 14.3: The positive integers have least element `1`, and their order
topology is discrete; equivalently, every singleton set is open. -/
#check PNat.bot_eq_one
#synth OrderTopology ℕ+
#synth DiscreteTopology ℕ+
#check fun n : ℕ+ ↦ isOpen_discrete ({n} : Set ℕ+)
