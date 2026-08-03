module

public import Topology_Munkres_2000.Book.Definition_23_1.Separation

public section

universe u

namespace Set.IsSeparation

/-- Lemma 23.2: If `C` and `D` form a separation and `Y` is preconnected, then
`Y` lies entirely within either `C` or `D`. -/
theorem subset_or_subset {X : Type u} [TopologicalSpace X] {C D Y : Set X}
    (hCD : C.IsSeparation D) (hY : IsPreconnected Y) : Y ⊆ C ∨ Y ⊆ D :=
  hY.subset_or_subset hCD.isOpen_left hCD.isOpen_right hCD.disjoint
    (hCD.union_eq_univ ▸ Set.subset_univ Y)

end Set.IsSeparation
