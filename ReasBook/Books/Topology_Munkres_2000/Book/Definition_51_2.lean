module

import Mathlib.Topology.Path

/- Definition 51.2: A path from `x₀` to `x₁` is a continuous map from
`unitInterval` to `X` with initial point `x₀` and final point `x₁`. Mathlib
bundles these endpoint conditions in `Path x₀ x₁`. -/
#check Path
#check Path.toContinuousMap
#check Path.source
#check Path.target
#check unitInterval
