module

public import Topology_Munkres_2000.Book.Definition_25_2

public section

/- Theorem 25.2 (1): every path component of `X` is path-connected. -/
#check isPathConnected_pathComponent

/-- Theorem 25.2 (2): distinct path components of `X` are disjoint. -/
theorem pathComponent_disjoint {X : Type u} [TopologicalSpace X] {x y : X}
    (h : pathComponent x ≠ pathComponent y) :
    Disjoint (pathComponent x) (pathComponent y) := by
  rw [Set.disjoint_left]
  intro z hzx hzy
  exact h ((pathComponent_congr hzx).symm.trans (pathComponent_congr hzy))

/-- Theorem 25.2 (3): the path components of `X`, indexed by their points,
cover the whole space. -/
theorem iUnion_pathComponent_eq_univ {X : Type u} [TopologicalSpace X] :
    (⋃ x : X, pathComponent x) = Set.univ := by
  rw [Set.iUnion_eq_univ_iff]
  exact fun x ↦ ⟨x, mem_pathComponent_self x⟩

/-- Theorem 25.2 (4): a path-connected subspace of `X` cannot intersect two
distinct path components. -/
theorem pathComponent_eq_of_isPathConnected_intersects {X : Type u} [TopologicalSpace X]
    {A : Set X} (hA : IsPathConnected A) {x y : X}
    (hx : (A ∩ pathComponent x).Nonempty)
    (hy : (A ∩ pathComponent y).Nonempty) :
    pathComponent x = pathComponent y := by
  obtain ⟨a, ha, hax⟩ := hx
  obtain ⟨b, hb, hby⟩ := hy
  exact (pathComponent_congr hax).symm.trans <|
    (pathComponent_congr (hA.mem_pathComponent ha hb)).symm.trans
      (pathComponent_congr hby)
