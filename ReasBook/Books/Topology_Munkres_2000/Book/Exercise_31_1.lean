module

import Mathlib.Topology.Separation.Regular

public section

universe u

/- Exercise 31.1: In a regular space, every pair of distinct points has open
neighborhoods whose closures are disjoint. -/
#check fun {X : Type u} [TopologicalSpace X] [T3Space X] {x y : X}
    (hxy : x ≠ y) ↦ exists_open_nhds_disjoint_closure hxy
