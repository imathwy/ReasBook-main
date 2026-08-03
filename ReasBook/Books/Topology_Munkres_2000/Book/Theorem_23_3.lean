module

public import Mathlib.Topology.Connected.Basic

public section

/-- Theorem 23.3: The union of a nonempty family of connected subspaces with a
point in common is connected. -/
theorem isConnected_iUnion {X : Type u} [TopologicalSpace X] {ι : Type v} [Nonempty ι]
    {A : ι → Set X} (h_inter : (⋂ i, A i).Nonempty) (hA : ∀ i, IsConnected (A i)) :
    IsConnected (⋃ i, A i) :=
  ⟨Nonempty.elim ‹Nonempty ι› fun i ↦ (hA i).nonempty.mono (Set.subset_iUnion A i),
    isPreconnected_iUnion h_inter fun i ↦ (hA i).isPreconnected⟩
