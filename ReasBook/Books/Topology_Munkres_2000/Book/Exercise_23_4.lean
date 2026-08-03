module

public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Connected.Basic

public section

universe u

variable (X : Type u) [Infinite X]

/- Exercise 23.4. If `X` is infinite, then `X` is connected in the finite
complement topology. -/
#check (inferInstance : ConnectedSpace (CofiniteTopology X))
