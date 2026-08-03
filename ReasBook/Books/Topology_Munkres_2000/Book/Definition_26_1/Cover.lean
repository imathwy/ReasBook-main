module

public import Mathlib.Data.Set.Lattice
public import Mathlib.Topology.Sets.OpenCover

universe u

public section

namespace Set

/-- A collection of subsets covers a set when its union contains that set. -/
def covers {X : Type u} (𝒜 : Set (Set X)) (Y : Set X) : Prop :=
  Y ⊆ ⋃₀ 𝒜

/-- A collection covers a set exactly when each point of the set belongs to one
member of the collection. -/
theorem covers_iff {X : Type u} {𝒜 : Set (Set X)} {Y : Set X} :
    covers 𝒜 Y ↔ ∀ y ∈ Y, ∃ U ∈ 𝒜, y ∈ U := by
  simp [covers, Set.subset_def]

/-- A collection covers the whole space exactly when its union is the whole space. -/
theorem covers_univ_iff {X : Type u} {𝒜 : Set (Set X)} :
    covers 𝒜 Set.univ ↔ ⋃₀ 𝒜 = Set.univ := by
  simp [covers]

/-- A collection of open sets covers the whole space exactly when its subtype-indexed
family is an open cover. -/
theorem isOpenCover_subtype_iff {X : Type u} [TopologicalSpace X] (𝒜 : Set (Set X))
    (h_open : ∀ U ∈ 𝒜, IsOpen U) :
    TopologicalSpace.IsOpenCover (fun U : 𝒜 ↦ ⟨U.1, h_open U.1 U.2⟩) ↔
      covers 𝒜 Set.univ := by
  constructor
  · intro h_cover
    rw [covers_iff]
    intro x _
    obtain ⟨U, hxU⟩ := h_cover.exists_mem x
    exact ⟨U.1, U.2, hxU⟩
  · intro h_cover
    refine TopologicalSpace.IsOpenCover.of_sets (fun U : 𝒜 ↦ h_open U.1 U.2) ?_
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨U, hU, hxU⟩ := covers_iff.mp h_cover x (Set.mem_univ x)
    exact ⟨⟨U, hU⟩, hxU⟩

end Set
