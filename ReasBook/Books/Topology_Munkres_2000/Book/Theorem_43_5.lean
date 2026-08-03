import Mathlib.Topology.MetricSpace.UniformConvergence

open scoped UniformConvergence

universe u v

variable (J : Type u) (Y : Type v) [MetricSpace Y] [CompleteSpace Y]

/- Theorem 43.5. If `Y` is complete in its metric, then `J →ᵤ Y`, the canonical
uniform-convergence model of the full function space `Yᴶ`, is complete. The source uniform
metric is recovered on raw functions by `MetricSpace.uniformFun` and
`MetricSpace.uniformFun_dist`, using the standard bounded metric associated to the metric on
`Y`. -/
#synth CompleteSpace (J →ᵤ Y)
