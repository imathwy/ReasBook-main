module

public import Topology_Munkres_2000.Book.Exercise_20_8.EventuallyZero
public import Mathlib.Topology.Instances.Real.Lemmas

public section

/-- Eventually-zero real sequences equipped with the induced box topology. -/
abbrev EventuallyZeroRealBox :=
  WithTopology eventuallyZeroRealSequences eventuallyZeroRealBoxTopology
