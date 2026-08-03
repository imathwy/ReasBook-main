module

public import Mathlib.Topology.Compactness.Paracompact

public section

universe u

namespace DiscreteTopology

/-- Exercise 41.4 (1): A discrete topological space is paracompact. -/
instance instParacompactSpace {X : Type u} [TopologicalSpace X] [DiscreteTopology X] :
    ParacompactSpace X := by
  refine ⟨fun α s _ cover ↦ ?_⟩
  choose index hindex using Set.iUnion_eq_univ_iff.mp cover
  -- Refine the cover by all singletons; discreteness makes them open and locally finite.
  refine ⟨X, fun x ↦ {x}, fun _ ↦ isOpen_discrete _, ?_, ?_, fun x ↦ ⟨index x, ?_⟩⟩
  · exact Set.iUnion_eq_univ_iff.mpr fun x ↦ ⟨x, Set.mem_singleton x⟩
  · intro x
    refine ⟨{x}, (isOpen_discrete _).mem_nhds (Set.mem_singleton x), ?_⟩
    refine (Set.finite_singleton x).subset ?_
    rintro i ⟨y, hyi, hyx⟩
    rw [Set.mem_singleton_iff] at hyi hyx ⊢
    exact hyi.symm.trans hyx
  · exact Set.singleton_subset_iff.mpr (hindex x)

end DiscreteTopology
