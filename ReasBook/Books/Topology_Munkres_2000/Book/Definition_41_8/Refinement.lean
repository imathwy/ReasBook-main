module

public import Topology_Munkres_2000.Book.Definition_39_4.Refinement

public section

open Set

universe u v

/-- Two indexed families form a precise refinement when each set in the first
family is contained in the correspondingly indexed set of the second. -/
class IsPreciseRefinement {ι : Type v} {X : Type u} (V U : ι → Set X) : Prop where
  subset (i : ι) : V i ⊆ U i

/-- A precise refinement canonically gives an ordinary refinement of the
corresponding ranges. -/
instance IsPreciseRefinement.toIsRefinement {ι : Type v} {X : Type u}
    {V U : ι → Set X} [IsPreciseRefinement V U] :
    IsRefinement (Set.range V) (Set.range U) := by
  constructor
  rintro B ⟨i, rfl⟩
  exact ⟨U i, ⟨i, rfl⟩, IsPreciseRefinement.subset i⟩

/-- The pointwise containment characterization of precise refinement. -/
theorem isPreciseRefinement_iff {ι : Type v} {X : Type u} {V U : ι → Set X} :
    IsPreciseRefinement V U ↔ ∀ i, V i ⊆ U i := by
  constructor
  · exact fun h i ↦ h.subset i
  · exact fun h ↦ ⟨h⟩
