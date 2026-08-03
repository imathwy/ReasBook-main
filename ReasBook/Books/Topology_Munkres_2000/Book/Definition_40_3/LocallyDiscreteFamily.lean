module

public import Mathlib.Topology.LocallyFinite

public section

open Set Function Filter Topology

universe u v w

variable {ι : Type u} {κ : Type v} {X : Type w} [TopologicalSpace X]

/-- A family of subsets is locally discrete if every point has a neighborhood meeting at most
one member of the family. -/
def LocallyDiscreteFamily (f : ι → Set X) : Prop :=
  ∀ x : X, ∃ t ∈ 𝓝 x, {i | (f i ∩ t).Nonempty}.Subsingleton

/-- A collection is locally discrete exactly when every point has a neighborhood meeting at most
one member of the collection. -/
theorem locallyDiscreteFamily_subtype_iff {𝒜 : Set (Set X)} :
    LocallyDiscreteFamily (Subtype.val : 𝒜 → Set X) ↔
      ∀ x : X, ∃ t ∈ 𝓝 x, {A : 𝒜 | ((A : Set X) ∩ t).Nonempty}.Subsingleton :=
  Iff.rfl

namespace LocallyDiscreteFamily

/-- Every locally discrete family is locally finite. -/
theorem locallyFinite {f : ι → Set X} (hf : LocallyDiscreteFamily f) : LocallyFinite f := by
  intro x
  obtain ⟨t, htx, ht⟩ := hf x
  exact ⟨t, htx, ht.finite⟩

/-- An injective reindexing of a locally discrete family is locally discrete. -/
theorem comp_injective {f : ι → Set X} {g : κ → ι}
    (hf : LocallyDiscreteFamily f) (hg : Injective g) :
    LocallyDiscreteFamily (f ∘ g) := by
  intro x
  obtain ⟨t, htx, ht⟩ := hf x
  refine ⟨t, htx, ?_⟩
  rintro i hi j hj
  exact hg (ht hi hj)

end LocallyDiscreteFamily
