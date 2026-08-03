module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs

public section

/-
Definition 47.1. A uniform structure is the structure represented in Mathlib by
`UniformSpace`. Every pseudometric structure induces a uniform structure via
`PseudoMetricSpace.toUniformSpace`.
-/
#check UniformSpace
#check PseudoMetricSpace.toUniformSpace
