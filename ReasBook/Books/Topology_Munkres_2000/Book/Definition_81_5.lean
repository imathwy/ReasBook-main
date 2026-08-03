module

public import Topology_Munkres_2000.Book.Definition_81_5.HomeomorphGroup

public section

open scoped HomeomorphGroup

universe u

variable {X : Type u} [TopologicalSpace X] (G : Subgroup (X ≃ₜ X))

/- Definition 81.5: For a space `X` and a subgroup `G` of its self-homeomorphisms,
the orbit space `X/G` is the quotient by evaluation, and the equivalence class of
`x` is its `G`-orbit. -/
#check (X / G)
#check (HomeomorphGroup.mk G : X → X / G)
#check HomeomorphGroup.mk_eq_quotient_mk
#check MulAction.orbit
#check HomeomorphGroup.mem_orbit_iff
#check HomeomorphGroup.mk_eq_mk_iff
#check HomeomorphGroup.quotientOrbit_mk
#check HomeomorphGroup.isQuotientMap_mk
