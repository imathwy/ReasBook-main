module

import Topology_Munkres_2000.Book.Exercise_3_99_8.Subnet
import Topology_Munkres_2000.Book.Exercise_3_99_1
import Topology_Munkres_2000.Book.Exercise_3_99_2
import Topology_Munkres_2000.Book.Exercise_3_99_3
import Topology_Munkres_2000.Book.Lemma_3_99_1.ClusterPoint
import Topology_Munkres_2000.Book.Theorem_3_99_1
import Topology_Munkres_2000.Book.Theorem_3_99_2
import Topology_Munkres_2000.Book.Theorem_3_99_3
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Separation.Hausdorff

universe u v w

open scoped Pointwise

/- Exercise 3.99.12: Condition (2) is antisymmetry, so omitting it replaces
`PartialOrder` by `Preorder`. The net results above use only a nonempty directed
preorder; antisymmetry is not needed. -/
#check fun {J : Type u} [Preorder J] ↦
  (Filter.atTop_neBot_iff :
    (Filter.atTop : Filter J).NeBot ↔ Nonempty J ∧ IsDirectedOrder J)

#check fun {J : Type u} [LinearOrder J] ↦
  (inferInstance : IsDirectedOrder J)

#check fun {S : Type u} ↦
  (inferInstance : IsDirectedOrder (Set S))

#check fun {S : Type u} {𝒜 : Set (Set S)} (h𝒜 : InfClosed 𝒜) ↦
  h𝒜.codirectedOn.isCodirectedOrder

#check fun {X : Type u} [TopologicalSpace X] ↦
  (inferInstance : IsDirectedOrder (TopologicalSpace.Closeds X))

#check fun {J : Type u} [Preorder J] [IsDirectedOrder J]
    {K : Set J} (hK : IsCofinal K) ↦
  hK.isDirectedOrder

#check fun (X : Type u) ↦
  (ℕ+ → X)

#check fun {X : Type u} [TopologicalSpace X] (sequence : ℕ+ → X) (x : X) ↦
  (tendsto_atTop_nhds :
    Filter.Tendsto sequence Filter.atTop (nhds x) ↔
      ∀ U, x ∈ U → IsOpen U → ∃ N : ℕ+, ∀ n, N ≤ n → sequence n ∈ U)

#check fun {J : Type u} {X : Type v} [Nonempty J] [Preorder J]
    [IsDirectedOrder J] [TopologicalSpace X] (net : J → X) (x : X) ↦
  (Filter.tendsto_atTop' :
    Filter.Tendsto net Filter.atTop (nhds x) ↔
      ∀ s ∈ nhds x, ∃ a, ∀ b ≥ a, net b ∈ s)

#check fun {J : Type u} {X : Type v} {Y : Type w} [Nonempty J] [Preorder J]
    [IsDirectedOrder J] [TopologicalSpace X] [TopologicalSpace Y]
    {xNet : J → X} {yNet : J → Y} {x : X} {y : Y}
    (hx : Filter.Tendsto xNet Filter.atTop (nhds x))
    (hy : Filter.Tendsto yNet Filter.atTop (nhds y)) ↦
  hx.prodMk_nhds hy

#check fun {J : Type u} {X : Type v} [Nonempty J] [Preorder J]
    [IsDirectedOrder J] [TopologicalSpace X] [T2Space X]
    {net : J → X} {x y : X} (hx : Filter.Tendsto net Filter.atTop (nhds x))
    (hy : Filter.Tendsto net Filter.atTop (nhds y)) ↦
  tendsto_nhds_unique hx hy

#check mem_closure_iff_exists_tendsto_net

#check continuous_iff_preserves_net_limits

#check fun {K : Type u} {J : Type v} {X : Type w} [Preorder K] [Preorder J]
    {g : K → J} {net : J → X} {l : Filter X} (hg : Net.IsSubnetMap g)
    (hnet : Filter.Tendsto net Filter.atTop l) ↦
  Net.IsSubnetMap.tendsto_comp hg hnet

#check Net.mapClusterPt_iff_exists_tendsto_subnet

#check compactSpace_iff_exists_tendsto_subnet

#check fun {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {A B : Set G} (hA : IsClosed A) (hB : IsCompact B) ↦
  IsClosed.mul_right_of_isCompact hA hB
