module

public import Mathlib.Topology.Connected.Basic

public section

open Set

namespace Set

/-- `U` is a connected component of `S` when it is the canonical component in `S`
of one of its points. -/
def IsConnectedComponentIn {X : Type u} [TopologicalSpace X] (S U : Set X) : Prop :=
  ∃ x ∈ S, U = connectedComponentIn S x

/-- The connected component in `S` containing a point of `S` is a component of `S`. -/
public theorem IsConnectedComponentIn.of_mem {X : Type u} [TopologicalSpace X]
    {S : Set X} {x : X}
    (hx : x ∈ S) : IsConnectedComponentIn S (connectedComponentIn S x) :=
  ⟨x, hx, rfl⟩

/-- A connected component of `S` is contained in `S`. -/
public theorem IsConnectedComponentIn.subset {X : Type u} [TopologicalSpace X] {S U : Set X}
    (hU : IsConnectedComponentIn S U) : U ⊆ S := by
  obtain ⟨x, _, rfl⟩ := hU
  exact connectedComponentIn_subset S x

/-- A connected component of `S` is connected. -/
public theorem IsConnectedComponentIn.isConnected {X : Type u} [TopologicalSpace X]
    {S U : Set X}
    (hU : IsConnectedComponentIn S U) : IsConnected U := by
  obtain ⟨x, hx, rfl⟩ := hU
  exact isConnected_connectedComponentIn_iff.mpr hx

/-- A connected component of `S` is nonempty. -/
public theorem IsConnectedComponentIn.nonempty {X : Type u} [TopologicalSpace X]
    {S U : Set X}
    (hU : IsConnectedComponentIn S U) : U.Nonempty :=
  hU.isConnected.nonempty

/-- A component of `S` is the canonical component in `S` of each of its points. -/
public theorem IsConnectedComponentIn.eq_connectedComponentIn {X : Type u}
    [TopologicalSpace X] {S U : Set X}
    (hU : IsConnectedComponentIn S U) {x : X} (hx : x ∈ U) :
    U = connectedComponentIn S x := by
  obtain ⟨y, _, rfl⟩ := hU
  exact connectedComponentIn_eq hx

end Set
