module

public import Topology_Munkres_2000.Book.Definition_25_1.ComponentIn
public import Mathlib.Topology.Connected.Clopen

public section

open Set

/-- Definition 25.1: two points are related by `connectedComponentSetoid X` exactly when a
connected subset of `X` contains both points. -/
theorem connectedComponentSetoid_rel_iff {X : Type u} [TopologicalSpace X] (x y : X) :
    connectedComponentSetoid X x y ↔
      ∃ C : Set X, IsConnected C ∧ x ∈ C ∧ y ∈ C := by
  -- Replace the setoid relation by equality of the canonical connected components.
  change connectedComponent x = connectedComponent y ↔ _
  constructor
  · intro hxy
    -- The component of `x` is connected and contains both points.
    refine ⟨connectedComponent x, isConnected_connectedComponent,
      mem_connectedComponent, ?_⟩
    rw [hxy]
    exact mem_connectedComponent
  · rintro ⟨C, hC, hx, hy⟩
    -- Maximality puts the connected witness inside the component of `x`.
    exact connectedComponent_eq (hC.subset_connectedComponent hx hy)

/- Definition 25.1 (2): the equivalence classes, called the connected components of `X`,
form the quotient type `ConnectedComponents X`. -/
#check ConnectedComponents
