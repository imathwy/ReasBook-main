module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice
public import Mathlib.Order.CompleteLattice.Finset

public section

open Set

universe u

namespace Set

/-- Definition 26.5. A collection `𝒞` of subsets of `X` has the finite intersection
property if every finite subcollection has nonempty intersection. -/
def FiniteIntersectionProperty {X : Type u} (𝒜 : Set (Set X)) : Prop :=
  ∀ ⦃𝒞 : Set (Set X)⦄, 𝒞 ⊆ 𝒜 → 𝒞.Finite → (⋂₀ 𝒞).Nonempty

namespace FiniteIntersectionProperty

/-- The finite intersection property is equivalent to nonemptiness of every
intersection indexed by a finite list without repetitions. -/
theorem finset_iff {X : Type u} {𝒜 : Set (Set X)} :
    𝒜.FiniteIntersectionProperty ↔
      ∀ s : Finset (Set X), (∀ A ∈ s, A ∈ 𝒜) → (⋂ A ∈ s, A).Nonempty := by
  constructor
  · -- Regard a finset as the finite subcollection in the defining property.
    intro h𝒜 s hs
    have hnonempty := h𝒜 (𝒞 := (s : Set (Set X))) hs s.finite_toSet
    simpa only [sInter_eq_biInter, Finset.set_biInter_coe] using hnonempty
  · -- Enumerate an arbitrary finite subcollection by its canonical finset.
    intro hfinset 𝒞 h𝒞 h𝒞finite
    have hnonempty := hfinset h𝒞finite.toFinset fun A hA ↦
      h𝒞 (h𝒞finite.mem_toFinset.mp hA)
    simpa only [← Finset.set_biInter_coe, h𝒞finite.coe_toFinset,
      sInter_eq_biInter] using hnonempty

end FiniteIntersectionProperty

end Set
