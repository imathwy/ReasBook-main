module

import Mathlib.Topology.Homotopy.Path

/- Definition 51.3: Paths with common endpoints have type `Path x₀ x₁`.
Mathlib represents a fixed-endpoint path homotopy with the homotopy parameter
first, so its `F (t, s)` corresponds to the source's `F (s, t)`. -/
#check Path.Homotopy
#check Path.Homotopic
