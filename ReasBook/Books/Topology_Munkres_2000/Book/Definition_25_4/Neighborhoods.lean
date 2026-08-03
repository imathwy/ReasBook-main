module

public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.Connected.LocallyPathConnected

public section

open Filter Set Topology

universe u

/-- A space is locally connected at `x` when every neighborhood of `x` contains a
connected open neighborhood of `x`. -/
def IsLocallyConnectedAt {X : Type u} [TopologicalSpace X] (x : X) : Prop :=
  ∀ U ∈ 𝓝 x, ∃ V, V ⊆ U ∧ IsOpen V ∧ x ∈ V ∧ IsConnected V

/-- The defining connected-open-neighborhood formulation of local connectedness at a point. -/
theorem isLocallyConnectedAt_iff_connected_neighborhoods
    {X : Type u} [TopologicalSpace X] {x : X} :
    IsLocallyConnectedAt x ↔
      ∀ U ∈ 𝓝 x, ∃ V, V ⊆ U ∧ IsOpen V ∧ x ∈ V ∧ IsConnected V :=
  Iff.rfl

/-- Local connectedness at a point can equivalently use preconnected open neighborhoods. -/
theorem isLocallyConnectedAt_iff_preconnected_neighborhoods
    {X : Type u} [TopologicalSpace X] {x : X} :
    IsLocallyConnectedAt x ↔
      ∀ U ∈ 𝓝 x, ∃ V, V ⊆ U ∧ IsOpen V ∧ x ∈ V ∧ IsPreconnected V := by
  constructor
  · intro h U hU
    obtain ⟨V, hVU, hV_open, hxV, hV_connected⟩ := h U hU
    exact ⟨V, hVU, hV_open, hxV, hV_connected.isPreconnected⟩
  · intro h U hU
    obtain ⟨V, hVU, hV_open, hxV, hV_preconnected⟩ := h U hU
    exact ⟨V, hVU, hV_open, hxV, ⟨⟨x, hxV⟩, hV_preconnected⟩⟩

/-- A space is locally connected exactly when it is locally connected at every point. -/
theorem locallyConnectedSpace_iff_isLocallyConnectedAt
    {X : Type u} [TopologicalSpace X] :
    LocallyConnectedSpace X ↔ ∀ x : X, IsLocallyConnectedAt x := by
  exact locallyConnectedSpace_iff_subsets_isOpen_isConnected

/-- A space is locally path connected at `x` when every neighborhood of `x` contains a
path-connected neighborhood of `x`. -/
def IsLocallyPathConnectedAt {X : Type u} [TopologicalSpace X] (x : X) : Prop :=
  ∀ U ∈ 𝓝 x, ∃ V ∈ 𝓝 x, IsPathConnected V ∧ V ⊆ U

/-- A space is locally path connected exactly when it is locally path connected at every point. -/
theorem locallyPathConnectedSpace_iff_isLocallyPathConnectedAt
    {X : Type u} [TopologicalSpace X] :
    LocallyPathConnectedSpace X ↔ ∀ x : X, IsLocallyPathConnectedAt x := by
  constructor
  · intro h x U hU
    obtain ⟨V, ⟨hV, hV_pathConnected⟩, hVU⟩ := h.path_connected_basis x |>.mem_iff.mp hU
    exact ⟨V, hV, hV_pathConnected, hVU⟩
  · intro h
    exact ⟨fun x ↦ by
      rw [Filter.hasBasis_self]
      intro U hU
      obtain ⟨V, hV, hV_pathConnected, hVU⟩ := h x U hU
      exact ⟨V, hV, hV_pathConnected, hVU⟩⟩
