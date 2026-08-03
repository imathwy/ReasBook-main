module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

public section

open Filter Set Topology

universe u

/-- A space is locally simply connected at `y` when every neighborhood of `y` contains a
simply connected neighborhood of `y`. -/
def IsLocallySimplyConnectedAt {Y : Type u} [TopologicalSpace Y] (y : Y) : Prop :=
  ∀ U ∈ 𝓝 y, ∃ V ∈ 𝓝 y, IsSimplyConnected V ∧ V ⊆ U

/-- Local simple connectedness at a point is characterized by simply connected subneighborhoods. -/
theorem isLocallySimplyConnectedAt_iff
    {Y : Type u} [TopologicalSpace Y] {y : Y} :
    IsLocallySimplyConnectedAt y ↔
      ∀ U ∈ 𝓝 y, ∃ V ∈ 𝓝 y, IsSimplyConnected V ∧ V ⊆ U := Iff.rfl
