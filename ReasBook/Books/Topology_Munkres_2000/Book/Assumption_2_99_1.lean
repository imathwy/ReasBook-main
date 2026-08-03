module

public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Separation.Basic
public import Topology_Munkres_2000.Book.Definition_2_99_1

public section

universe u

/- Assumption 2.99.1: Throughout the following exercises, let `G` denote a
topological group. In accordance with Definition 2.99.1, this includes the
separation assumption `T1Space G`. -/
#check fun (G : Type u) [TopologicalSpace G] [Group G] [T1Space G]
    [IsTopologicalGroup G] ↦ G
