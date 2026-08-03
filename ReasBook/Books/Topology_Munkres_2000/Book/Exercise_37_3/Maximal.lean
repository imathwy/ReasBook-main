module

public import Topology_Munkres_2000.Book.Exercise_37_2.CountableIntersection
public import Mathlib.Order.Minimal
import Topology_Munkres_2000.Book.Exercise_37_2

public section

open Set

universe u

/-- A family of subsets is maximal with respect to the countable intersection property. -/
abbrev IsMaximalCountableIntersection {X : Type u} (𝒟 : Set (Set X)) : Prop :=
  Maximal Set.CountableIntersectionProperty 𝒟

/-- A maximal countable-intersection family has the countable intersection property. -/
theorem IsMaximalCountableIntersection.countableIntersectionProperty
    {X : Type u} {𝒟 : Set (Set X)} (h𝒟 : IsMaximalCountableIntersection 𝒟) :
    𝒟.CountableIntersectionProperty :=
  h𝒟.prop

/-- A family is maximal with respect to the countable intersection property exactly when it
has that property and every larger family having it is equal to the original family. -/
theorem isMaximalCountableIntersection_iff {X : Type u} {𝒟 : Set (Set X)} :
    IsMaximalCountableIntersection 𝒟 ↔
      𝒟.CountableIntersectionProperty ∧
        ∀ ⦃𝒞 : Set (Set X)⦄, 𝒞.CountableIntersectionProperty → 𝒟 ⊆ 𝒞 → 𝒟 = 𝒞 :=
  maximal_subset_iff

/-- A countable intersection of members of a maximal countable-intersection family
belongs to the family. -/
theorem IsMaximalCountableIntersection.countable_sInter_mem
    {X : Type u} {𝒟 𝒞 : Set (Set X)} (h𝒟 : IsMaximalCountableIntersection 𝒟)
    (h𝒞 : 𝒞 ⊆ 𝒟) (h𝒞_countable : 𝒞.Countable) :
    ⋂₀ 𝒞 ∈ 𝒟 := by
  classical
  -- Maximality reduces membership to preserving the countable intersection property.
  apply h𝒟.mem_of_prop_insert
  have hRange :
      (Set.range ((↑) : ↥(insert (⋂₀ 𝒞) 𝒟) → Set X)).CountableIntersectionProperty := by
    refine (Set.CountableIntersectionProperty.range_iff _).mpr ?_
    intro s hs
    have hResidual_subset :
        (((↑) : ↥(insert (⋂₀ 𝒞) 𝒟) → Set X) '' s) \ {⋂₀ 𝒞} ⊆ 𝒟 := by
      intro B hB
      obtain ⟨B', hB's, rfl⟩ := hB.1
      rcases B'.property with hB'_eq | hB'_mem
      · exact False.elim (hB.2 (Set.mem_singleton_iff.mpr hB'_eq))
      · exact hB'_mem
    have hResidual_countable :
        ((((↑) : ↥(insert (⋂₀ 𝒞) 𝒟) → Set X) '' s) \ {⋂₀ 𝒞}).Countable :=
      (hs.image _).mono Set.sdiff_subset
    have hUnion_subset :
        𝒞 ∪ ((((↑) : ↥(insert (⋂₀ 𝒞) 𝒟) → Set X) '' s) \ {⋂₀ 𝒞}) ⊆ 𝒟 :=
      Set.union_subset h𝒞 hResidual_subset
    have hUnion_countable :
        (𝒞 ∪ ((((↑) : ↥(insert (⋂₀ 𝒞) 𝒟) → Set X) '' s) \ {⋂₀ 𝒞})).Countable :=
      h𝒞_countable.union hResidual_countable
    letI : Countable
        ↥(𝒞 ∪ ((((↑) : ↥(insert (⋂₀ 𝒞) 𝒟) → Set X) '' s) \ {⋂₀ 𝒞})) :=
      hUnion_countable.to_subtype
    obtain ⟨x, hx⟩ := h𝒟.countableIntersectionProperty.iInter_nonempty
      ((↑) : ↥(𝒞 ∪ ((((↑) : ↥(insert (⋂₀ 𝒞) 𝒟) → Set X) '' s) \ {⋂₀ 𝒞})) → Set X)
      (fun B ↦ hUnion_subset B.property)
    -- The common point lies in every selected subtype member.
    refine ⟨x, Set.mem_iInter₂.mpr ?_⟩
    intro B hBs
    by_cases hB_eq : (B : Set X) = ⋂₀ 𝒞
    · rw [hB_eq]
      exact Set.mem_sInter.mpr fun C hC ↦
        Set.mem_iInter.mp hx ⟨C, Set.mem_union_left _ hC⟩
    · exact Set.mem_iInter.mp hx
        ⟨B, Set.mem_union_right _
          ⟨⟨B, hBs, rfl⟩, Set.mem_singleton_iff.not.mpr hB_eq⟩⟩
  simpa only [Subtype.range_coe] using hRange

/-- A set intersecting every member of a maximal countable-intersection family
belongs to the family. -/
theorem IsMaximalCountableIntersection.mem_of_intersects_all
    {X : Type u} {𝒟 : Set (Set X)} (h𝒟 : IsMaximalCountableIntersection 𝒟)
    {A : Set X} (hA : ∀ B ∈ 𝒟, (A ∩ B).Nonempty) :
    A ∈ 𝒟 := by
  classical
  -- Maximality again reduces membership to the insertion property.
  apply h𝒟.mem_of_prop_insert
  have hRange :
      (Set.range ((↑) : ↥(insert A 𝒟) → Set X)).CountableIntersectionProperty := by
    refine (Set.CountableIntersectionProperty.range_iff _).mpr ?_
    intro s hs
    have hResidual_subset :
        (((↑) : ↥(insert A 𝒟) → Set X) '' s) \ {A} ⊆ 𝒟 := by
      intro B hB
      obtain ⟨B', hB's, rfl⟩ := hB.1
      rcases B'.property with hB'_eq | hB'_mem
      · exact False.elim (hB.2 (Set.mem_singleton_iff.mpr hB'_eq))
      · exact hB'_mem
    have hResidual_countable :
        ((((↑) : ↥(insert A 𝒟) → Set X) '' s) \ {A}).Countable :=
      (hs.image _).mono Set.sdiff_subset
    have hResidual_mem : ⋂₀ ((((↑) : ↥(insert A 𝒟) → Set X) '' s) \ {A}) ∈ 𝒟 :=
      h𝒟.countable_sInter_mem hResidual_subset hResidual_countable
    obtain ⟨x, hxA, hxResidual⟩ :=
      hA (⋂₀ ((((↑) : ↥(insert A 𝒟) → Set X) '' s) \ {A})) hResidual_mem
    -- The chosen point lies in the adjoined set and every selected residual member.
    refine ⟨x, Set.mem_iInter₂.mpr ?_⟩
    intro B hBs
    by_cases hB_eq : (B : Set X) = A
    · simpa only [hB_eq] using hxA
    · exact Set.mem_sInter.mp hxResidual B
        ⟨⟨B, hBs, rfl⟩, Set.mem_singleton_iff.not.mpr hB_eq⟩
  simpa only [Subtype.range_coe] using hRange
