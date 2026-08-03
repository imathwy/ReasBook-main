module

import Mathlib.Topology.Algebra.Group.Quotient

universe u

/- Exercise 29.9: If `G` is a locally compact topological group and `H` is a subgroup,
then `G ⧸ H` is locally compact. -/
#check fun {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] (H : Subgroup G) ↦
  (inferInstance : LocallyCompactSpace (G ⧸ H))
