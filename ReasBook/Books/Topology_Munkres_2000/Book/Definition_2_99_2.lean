module

public import Topology_Munkres_2000.Book.Definition_2_99_2.HomeomorphAction

public section

universe u

/- Definition 2.99.2: A topological space is homogeneous when every point can be
carried to every other point by a self-homeomorphism. -/
#check fun (X : Type u) [TopologicalSpace X] ↦ MulAction.IsPretransitive (X ≃ₜ X) X
#check MulAction.isPretransitive_iff
