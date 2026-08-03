module

public import Mathlib.Topology.Connected.LocallyConnected

public section

open Set Topology

universe u

/-- A space is weakly locally connected at `x` if every neighborhood of `x`
contains a connected set that is itself a neighborhood of `x`. -/
def WeaklyLocallyConnectedAt {X : Type u} [TopologicalSpace X] (x : X) : Prop :=
  ∀ U ∈ 𝓝 x, ∃ C ∈ 𝓝 x, IsConnected C ∧ C ⊆ U

/-- The defining connected-neighborhood characterization of weak local connectedness. -/
theorem weaklyLocallyConnectedAt_iff {X : Type u} [TopologicalSpace X] (x : X) :
    WeaklyLocallyConnectedAt x ↔
      ∀ U ∈ 𝓝 x, ∃ C ∈ 𝓝 x, IsConnected C ∧ C ⊆ U :=
  Iff.rfl

/-- A topological space is weakly locally connected when it is weakly locally
connected at every point. -/
class WeaklyLocallyConnectedSpace (X : Type u) [TopologicalSpace X] : Prop where
  /-- The space is weakly locally connected at each point. -/
  weaklyLocallyConnectedAt (x : X) : WeaklyLocallyConnectedAt x
