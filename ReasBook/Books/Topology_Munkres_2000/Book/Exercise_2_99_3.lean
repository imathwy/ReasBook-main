module

import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Separation.Basic

public section

universe u

/- Exercise 2.99.3 (1): A subgroup `H` of a T₁ topological group, equipped
with its inherited subtype topology, is a topological group. -/
#check fun {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T1Space G] (H : Subgroup G) ↦ (inferInstance : IsTopologicalGroup H)
#check fun {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T1Space G] (H : Subgroup G) ↦ (inferInstance : T1Space H)

/- Exercise 2.99.3 (2): The subgroup `H.topologicalClosure`, whose carrier is
`closure (H : Set G)`, is also a topological group. -/
#check fun {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T1Space G] (H : Subgroup G) ↦ H.topologicalClosure_coe
#check fun {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T1Space G] (H : Subgroup G) ↦
      (inferInstance : IsTopologicalGroup H.topologicalClosure)
#check fun {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T1Space G] (H : Subgroup G) ↦ (inferInstance : T1Space H.topologicalClosure)
