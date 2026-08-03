module

import Mathlib.Topology.Bases

/- Exercise 30.2. `SecondCountableTopology X` expresses that `X` has a countable
topological basis. Every topological basis of `X` contains a countable subfamily
that is still a topological basis. -/
#check TopologicalSpace.IsTopologicalBasis.exists_countable
