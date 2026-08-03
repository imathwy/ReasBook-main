module

public import Topology_Munkres_2000.Book.Exercise_3_99_8.Subnet
public import Mathlib.Topology.Neighborhoods

public section

universe u v w

/- Exercise 3.99.8: If a net converges to `x`, then its precomposition with any
monotone reindexing map having cofinal range also converges to `x`. -/
#check fun {J : Type u} {K : Type v} {X : Type w} [Preorder J] [Preorder K]
    [TopologicalSpace X] {f : J → X} {g : K → J} {x : X}
    (hsub : Net.IsSubnetMap g) (hf : Filter.Tendsto f Filter.atTop (nhds x)) ↦
  hsub.tendsto_comp hf
