module

public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Topology_Munkres_2000.Book.Definition_39_4.Refinement
public import Topology_Munkres_2000.Book.Definition_6_0_3.CountablyLocallyFinite

public section

universe u

namespace Set

/-- Helper for Lemma 39.2: a locally finite collection is countably locally finite. -/
lemma LocallyFinite.countablyLocallyFinite {X : Type u} [TopologicalSpace X]
    {𝒜 : Set (Set X)} (h𝒜 : 𝒜.LocallyFinite) : 𝒜.CountablyLocallyFinite := by
  -- Use the collection itself as the zeroth locally finite layer.
  rw [countablyLocallyFinite_iff]
  refine ⟨fun n ↦ if n = 0 then 𝒜 else ∅, ?_, ?_⟩
  · ext U
    simp
  · intro n
    by_cases hn : n = 0
    · simpa [hn] using h𝒜
    · simp [hn, locallyFinite_of_finite]

end Set

/-- Helper for Lemma 39.2: the range of an indexed open refinement is an open refinement. -/
lemma isOpenRefinement_range {X : Type u} [TopologicalSpace X] {ι : Type*}
    (v : ι → Set X) (𝒜 : Set (Set X))
    (h_open : ∀ i, IsOpen (v i))
    (h_sub : ∀ i, ∃ A ∈ 𝒜, v i ⊆ A) :
    IsOpenRefinement (Set.range v) 𝒜 := by
  -- Unpack range membership to recover the indexed refinement data.
  rw [isOpenRefinement_iff, isRefinement_iff]
  constructor
  · rintro B ⟨i, rfl⟩
    exact h_sub i
  · rintro B ⟨i, rfl⟩
    exact h_open i

namespace TopologicalSpace.MetrizableSpace

/-- Lemma 39.2. Every open cover of a metrizable space has a countably locally finite
open refinement that covers the space. -/
theorem exists_countablyLocallyFinite_openRefinement
    {X : Type u} [TopologicalSpace X] [MetrizableSpace X]
    (𝒜 : Set (Set X)) (h_open : ∀ U ∈ 𝒜, IsOpen U) (h_cover : ⋃₀ 𝒜 = Set.univ) :
    ∃ ℰ : Set (Set X),
      IsOpenRefinement ℰ 𝒜 ∧ ⋃₀ ℰ = Set.univ ∧ ℰ.CountablyLocallyFinite := by
  classical
  -- Install a compatible metric, hence the canonical paracompactness instance.
  letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  have h_indexedOpen : ∀ U : 𝒜, IsOpen (U : Set X) := fun U ↦ h_open U U.property
  have h_indexedCover : ⋃ U : 𝒜, (U : Set X) = Set.univ := by
    rwa [← Set.sUnion_range, Subtype.range_coe]
  obtain ⟨v, h_vOpen, h_vCover, h_vFinite, h_vSub⟩ :=
    precise_refinement (fun U : 𝒜 ↦ (U : Set X)) h_indexedOpen h_indexedCover
  -- Package the precise indexed refinement as its range collection.
  refine ⟨Set.range v, isOpenRefinement_range v 𝒜 ?_ ?_, ?_, ?_⟩
  · exact h_vOpen
  · exact fun U ↦ ⟨U, U.property, h_vSub U⟩
  · rwa [Set.sUnion_range]
  · exact Set.LocallyFinite.countablyLocallyFinite h_vFinite.on_range

end TopologicalSpace.MetrizableSpace
