module

import Mathlib.Topology.ContinuousMap.Compact

public section

/- Notation 49.1: The unit interval `I = [0, 1]` is `unitInterval`, and the
space `𝒞 = 𝒞(I, ℝ)` is the bundled continuous-map type `C(unitInterval, ℝ)`.
Its canonical metric is the uniform metric: mathlib writes its distance as the
supremum `⨆ x, dist (f x) (g x)`, with real pointwise distance equal to
`|f x - g x|`. Compactness of `unitInterval` makes this supremum the maximum
appearing in the source. -/
#check unitInterval
#check C(unitInterval, ℝ)
#check ContinuousMap.instMetricSpace
#check ContinuousMap.dist_eq_iSup
#check Real.dist_eq
