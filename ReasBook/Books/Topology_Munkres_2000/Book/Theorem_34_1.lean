module

public import Mathlib.Topology.Metrizable.Urysohn

public section

/- Theorem 34.1 (Urysohn metrization theorem): every regular space `X`,
represented by `T3Space X`, with a countable basis, represented by
`SecondCountableTopology X`, is metrizable via
`TopologicalSpace.MetrizableSpace X`. -/
#check TopologicalSpace.metrizableSpace_of_t3_secondCountable
