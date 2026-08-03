module

public import Topology_Munkres_2000.Book.Example_23_1.Instances
public import Mathlib.Topology.WithTopology

public section

/- Example 23.1: A two-point space with the indiscrete topology is connected. -/
#check (inferInstance : ConnectedSpace (WithTopology (Fin 2) ⊤))
