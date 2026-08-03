module

public import Topology_Munkres_2000.Book.Example_16_2
public import Topology_Munkres_2000.Book.Example_16_3

public section

open scoped Topology

/- Theorem 16.1 (1): The subspace topology and intrinsic order topology on
`Set.Icc (0 : ℝ) 1` agree. -/
#check (OrderTopology.topology_eq_generate_intervals :
  (inferInstance : TopologicalSpace (Set.Icc (0 : ℝ) 1)) =
    Preorder.topology (Set.Icc (0 : ℝ) 1))

/- Theorem 16.1 (2): On `[0, 1) ∪ {2}`, the singleton at `2` is open in the
subspace topology but not in the intrinsic order topology. -/
#check isolatedPointIsOpenSubspace
#check isolatedPointNotIsOpenOrder

/- Theorem 16.1 (3): On the lexicographic unit square, the induced topology
differs from the intrinsic order topology, as witnessed by the upper vertical
segment. -/
#check LexUnitSquare.inclusion
#check LexUnitSquare.topology_ne_induced
#check LexUnitSquare.upperVerticalSegment_isOpen_induced
#check LexUnitSquare.upperVerticalSegment_not_isOpen_order
