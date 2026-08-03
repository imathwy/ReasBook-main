module

public import Mathlib.Topology.Compactness.Paracompact

public section

universe u

/- Theorem 41.2. Every closed subspace of a paracompact space is paracompact. -/
#check fun {X : Type u} [TopologicalSpace X] [ParacompactSpace X]
    (s : Set X) (hs : IsClosed s) ↦ hs.isClosedEmbedding_subtypeVal.paracompactSpace
