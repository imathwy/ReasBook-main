module

public import «Mathlib».«Topology».«ContinuousMap».«SecondCountableSpace»
public import Mathlib.Topology.UnitInterval

public section

open scoped unitInterval

/- Exercise 30.15: The space `C(unitInterval, ℝ)` of continuous real-valued functions on `[0, 1]`
has a countable dense subset. -/
#check (ContinuousMap.instSeparableSpace : TopologicalSpace.SeparableSpace C(unitInterval, ℝ))

/- Exercise 30.15: Consequently, `C(unitInterval, ℝ)` has a countable basis. -/
#check (ContinuousMap.instSecondCountableTopology : SecondCountableTopology C(unitInterval, ℝ))
