module

public import Topology_Munkres_2000.Book.Exercise_46_10.CompactExhaustible
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

public section

open Set
open scoped Uniformity

universe u v

namespace UniformOnFun

/-- Compact convergence on all functions into a separated uniform space is separated. -/
instance compactConvergenceT2Space (X : Type u) (Y : Type v)
    [TopologicalSpace X] [UniformSpace Y] [T2Space Y] :
    T2Space (UniformOnFun X Y {K : Set X | IsCompact K}) :=
  UniformOnFun.t2Space_of_covering <| by
    rw [sUnion_eq_univ_iff]
    intro x
    exact ⟨{x}, isCompact_singleton, mem_singleton x⟩

/-- Compact convergence has countably generated uniformity on a compactly exhaustible domain
when the codomain uniformity is countably generated. -/
instance compactConvergenceIsCountablyGenerated (X : Type u) (Y : Type v)
    [TopologicalSpace X] [CompactlyExhaustibleSpace X]
    [UniformSpace Y] [Filter.IsCountablyGenerated (uniformity Y)] :
  Filter.IsCountablyGenerated
      (uniformity (UniformOnFun X Y {K : Set X | IsCompact K})) :=
  UniformOnFun.isCountablyGenerated_uniformity
    {K : Set X | IsCompact K}
    (fun n ↦ (CompactExhaustion.choice X).isCompact n)
    (fun _ _ h ↦ (CompactExhaustion.choice X).subset h)
    (fun _ hK ↦ (CompactExhaustion.choice X).exists_superset_of_isCompact hK)

/-- Compact convergence on all functions is metrizable for a compactly exhaustible domain and
a separated uniform codomain with countably generated uniformity. -/
noncomputable instance compactConvergenceMetrizableSpace (X : Type u) (Y : Type v)
    [TopologicalSpace X] [CompactlyExhaustibleSpace X]
    [UniformSpace Y] [T2Space Y] [Filter.IsCountablyGenerated (uniformity Y)] :
    TopologicalSpace.MetrizableSpace (UniformOnFun X Y {K : Set X | IsCompact K}) :=
  UniformSpace.metrizableSpace

end UniformOnFun
