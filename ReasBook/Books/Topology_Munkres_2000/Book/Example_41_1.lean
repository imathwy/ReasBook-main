module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.EMetricSpace.Paracompact

public section

/- Example 41.1: Every finite-dimensional real coordinate space
`EuclideanSpace ℝ (Fin n)` is paracompact. -/
#check fun n : ℕ ↦ (inferInstance : ParacompactSpace (EuclideanSpace ℝ (Fin n)))
