module

public import Topology_Munkres_2000.Book.Definition_37_2.Maximal

public section

open Set

universe u

namespace Set.FiniteIntersectionProperty

/-- Helper for Lemma 37.2: adjoining a set that meets every finite intersection
of a family produces a family with the finite intersection property. -/
theorem insert_of_intersects_sInter {X : Type u} {𝒟 : Set (Set X)} {A : Set X}
    (hA : ∀ ⦃𝒞 : Set (Set X)⦄, 𝒞 ⊆ 𝒟 → 𝒞.Finite → (A ∩ ⋂₀ 𝒞).Nonempty) :
    (insert A 𝒟).FiniteIntersectionProperty := by
  classical
  rw [Set.FiniteIntersectionProperty.finset_iff]
  intro s hs
  -- Remove the adjoined set to obtain a finite subfamily of the original family.
  have hresidual_subset : (s.erase A : Set (Set X)) ⊆ 𝒟 := by
    intro B hB
    have hB_ne : B ≠ A := (Finset.mem_erase.mp hB).1
    have hBs : B ∈ s := (Finset.mem_erase.mp hB).2
    rcases hs B hBs with hBA | hB𝒟
    · exact False.elim (hB_ne hBA)
    · exact hB𝒟
  have hresidual_finite : (s.erase A : Set (Set X)).Finite := (s.erase A).finite_toSet
  obtain ⟨x, hxA, hxresidual⟩ := hA hresidual_subset hresidual_finite
  -- The chosen point lies in the adjoined set and in every residual member.
  refine ⟨x, ?_⟩
  simp only [mem_iInter]
  intro B hBs
  by_cases hBA : B = A
  · simpa only [hBA] using hxA
  · have hBresidual : B ∈ (s.erase A : Set (Set X)) := Finset.mem_erase.mpr ⟨hBA, hBs⟩
    exact mem_sInter.mp hxresidual B hBresidual

end Set.FiniteIntersectionProperty

namespace IsMaximalFiniteIntersection

/-- Lemma 37.2 (1): The intersection of a finite subfamily of a family maximal
with respect to the finite intersection property belongs to the family. -/
theorem finite_sInter_mem {X : Type u} {𝒟 𝒞 : Set (Set X)}
    (h𝒟 : IsMaximalFiniteIntersection 𝒟) (h𝒞 : 𝒞 ⊆ 𝒟) (h𝒞_finite : 𝒞.Finite) :
    ⋂₀ 𝒞 ∈ 𝒟 := by
  -- Maximality reduces membership to preserving the finite-intersection property.
  apply h𝒟.mem_of_prop_insert
  refine Set.FiniteIntersectionProperty.insert_of_intersects_sInter ?_
  intro 𝓑 h𝓑 h𝓑_finite
  -- The required intersection is the intersection indexed by the finite union.
  have hunion_subset : 𝒞 ∪ 𝓑 ⊆ 𝒟 := union_subset h𝒞 h𝓑
  have hunion_finite : (𝒞 ∪ 𝓑).Finite := h𝒞_finite.union h𝓑_finite
  have hfinset := Set.FiniteIntersectionProperty.finset_iff.mp h𝒟.prop
  have hunion_nonempty := hfinset hunion_finite.toFinset fun B hB ↦
    hunion_subset (hunion_finite.mem_toFinset.mp hB)
  have hunion_sInter_nonempty : (⋂₀ (𝒞 ∪ 𝓑)).Nonempty := by
    simpa only [← Finset.set_biInter_coe, hunion_finite.coe_toFinset,
      sInter_eq_biInter] using hunion_nonempty
  simpa only [sInter_union] using hunion_sInter_nonempty

/-- The finset-indexed form of `IsMaximalFiniteIntersection.finite_sInter_mem`. -/
theorem finiteInter_mem {X : Type u} {𝒟 : Set (Set X)}
    (h𝒟 : IsMaximalFiniteIntersection 𝒟) (s : Finset (Set X))
    (hs : ∀ A ∈ s, A ∈ 𝒟) :
    (⋂ A ∈ s, A) ∈ 𝒟 := by
  -- Regard the finset as a finite set-indexed subfamily.
  have hs_subset : (s : Set (Set X)) ⊆ 𝒟 := by
    intro A hAs
    exact hs A hAs
  have hsInter_mem := h𝒟.finite_sInter_mem hs_subset s.finite_toSet
  -- Normalize the set-indexed intersection to the finset notation.
  simpa only [sInter_eq_biInter, Finset.set_biInter_coe] using hsInter_mem

/-- Lemma 37.2 (2): A set intersecting every member of a family maximal with respect
to the finite intersection property belongs to the family. -/
theorem mem_of_intersects {X : Type u} {𝒟 : Set (Set X)}
    (h𝒟 : IsMaximalFiniteIntersection 𝒟) {A : Set X}
    (hA : ∀ D ∈ 𝒟, (A ∩ D).Nonempty) : A ∈ 𝒟 := by
  -- Maximality again reduces membership to the insertion property.
  apply h𝒟.mem_of_prop_insert
  refine Set.FiniteIntersectionProperty.insert_of_intersects_sInter ?_
  intro 𝒞 h𝒞 h𝒞_finite
  -- Part (1) makes each finite intersection a member of the maximal family.
  exact hA (⋂₀ 𝒞) (h𝒟.finite_sInter_mem h𝒞 h𝒞_finite)

end IsMaximalFiniteIntersection
