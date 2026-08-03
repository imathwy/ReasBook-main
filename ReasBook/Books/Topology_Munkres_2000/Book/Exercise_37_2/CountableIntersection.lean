module

public import Mathlib.Data.Set.Countable

public section

open Set

universe u v

namespace Set

/-- A collection of subsets has the countable intersection property if every
countable subcollection has nonempty intersection. -/
def CountableIntersectionProperty {X : Type u} (𝒜 : Set (Set X)) : Prop :=
  ∀ ⦃𝒞 : Set (Set X)⦄, 𝒞 ⊆ 𝒜 → 𝒞.Countable → (⋂₀ 𝒞).Nonempty

namespace CountableIntersectionProperty

/-- The countable intersection property passes to subcollections. -/
theorem mono {X : Type u} {𝒜 𝓑 : Set (Set X)}
    (h𝒜 : 𝒜.CountableIntersectionProperty) (h𝓑 : 𝓑 ⊆ 𝒜) :
    𝓑.CountableIntersectionProperty := by
  intro 𝒞 h𝒞 hCountable
  -- A countable subcollection of `𝓑` is also one of `𝒜`.
  exact h𝒜 (h𝒞.trans h𝓑) hCountable

/-- A countably indexed family drawn from a collection with the countable
intersection property has nonempty intersection. -/
theorem iInter_nonempty {X : Type u} {ι : Type v} [Countable ι]
    {𝒜 : Set (Set X)} (h𝒜 : 𝒜.CountableIntersectionProperty)
    (A : ι → Set X) (hA : ∀ i, A i ∈ 𝒜) :
    (⋂ i, A i).Nonempty := by
  -- Apply the property to the countable range of the indexed family.
  have hRange : Set.range A ⊆ 𝒜 := Set.range_subset_iff.mpr hA
  simpa only [Set.sInter_range] using h𝒜 hRange (Set.countable_range A)

end CountableIntersectionProperty

end Set
