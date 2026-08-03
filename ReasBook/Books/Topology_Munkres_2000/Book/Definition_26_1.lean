module

public import Topology_Munkres_2000.Book.Definition_26_1.Cover

public section

universe u

/- Definition 26.1 (1) -/
#check fun {X : Type u} (𝒜 : Set (Set X)) ↦ Set.covers 𝒜 (Set.univ : Set X)

/- Equivalently, the union of the collection is the whole space. -/
#check Set.covers_univ_iff

/- Definition 26.1 (2) -/
#check fun {X : Type u} [TopologicalSpace X] (𝒜 : Set (Set X))
    (h_open : ∀ U ∈ 𝒜, IsOpen U) ↦
  TopologicalSpace.IsOpenCover (fun U : 𝒜 ↦ ⟨U.1, h_open U.1 U.2⟩)

/- The set-indexed and subtype-indexed formulations agree. -/
#check Set.isOpenCover_subtype_iff
