module

import Mathlib.Topology.Order.Basic

universe u

variable (X : Type u) [LinearOrder X] [t : TopologicalSpace X] [OrderTopology X]

/- Proposition 14.2: In a simply ordered set with the order topology, the open
rays form a subbasis for the order topology. -/
#check (OrderTopology.topology_eq_generate_intervals :
  t =
    TopologicalSpace.generateFrom
      {s : Set X | ∃ a, s = Set.Ioi a ∨ s = Set.Iio a})
