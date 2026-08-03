module

public import Topology_Munkres_2000.Book.Definition_25_1

public section

/- Theorem 25.1 (1): every connected component of `X` is connected. -/
#check isConnected_connectedComponent

/- Theorem 25.1 (2): distinct connected components of `X` are disjoint. -/
#check connectedComponent_disjoint

/-- Theorem 25.1 (3): the connected components of `X`, indexed by their points,
cover the whole space. -/
theorem iUnion_connectedComponent_eq_univ {X : Type u} [TopologicalSpace X] :
    (⋃ x : X, connectedComponent x) = Set.univ := by
  rw [Set.iUnion_eq_univ_iff]
  exact fun x ↦ ⟨x, mem_connectedComponent⟩

/-- Theorem 25.1 (4): a connected subspace of `X` cannot intersect two distinct
connected components. -/
theorem connectedComponent_eq_of_isConnected_intersects {X : Type u} [TopologicalSpace X]
    {A : Set X} (hA : IsConnected A) {x y : X}
    (hx : (A ∩ connectedComponent x).Nonempty)
    (hy : (A ∩ connectedComponent y).Nonempty) :
    connectedComponent x = connectedComponent y := by
  obtain ⟨a, ha, hax⟩ := hx
  obtain ⟨b, hb, hby⟩ := hy
  exact (connectedComponent_eq hax).trans <|
    (connectedComponent_eq (hA.subset_connectedComponent ha hb)).trans
      (connectedComponent_eq hby).symm
