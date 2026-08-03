module

public import Topology_Munkres_2000.Book.Remark_37_2

public section

open Set

universe u v

/-- Lemma 37.3 (1). The first-coordinate images of a family with the finite
intersection property also have the finite intersection property. -/
theorem firstProjection_finiteIntersectionProperty {X₁ : Type u} {X₂ : Type v}
    (𝒜 : Set (Set (X₁ × X₂))) (h𝒜 : 𝒜.FiniteIntersectionProperty) :
    ((fun A : Set (X₁ × X₂) ↦ Prod.fst '' A) '' 𝒜).FiniteIntersectionProperty :=
  h𝒜.image Prod.fst

/-- Lemma 37.3 (2). The closures of the first-coordinate images of a family with the
finite intersection property also have the finite intersection property. -/
theorem closureFirstProjection_finiteIntersectionProperty {X₁ : Type u} {X₂ : Type v}
    [TopologicalSpace X₁] (𝒜 : Set (Set (X₁ × X₂)))
    (h𝒜 : 𝒜.FiniteIntersectionProperty) :
    ((fun A : Set (X₁ × X₂) ↦ closure (Prod.fst '' A)) '' 𝒜).FiniteIntersectionProperty := by
  simpa [Function.comp_def, Set.image_image] using (h𝒜.image Prod.fst).closure

/-- Lemma 37.3 (3). In a compact first factor, the closures of all first-coordinate
images of a family with the finite intersection property have a common point. -/
theorem iInter_closure_firstProjection_nonempty {X₁ : Type u} {X₂ : Type v}
    [TopologicalSpace X₁] [CompactSpace X₁] (𝒜 : Set (Set (X₁ × X₂)))
    (h𝒜 : 𝒜.FiniteIntersectionProperty) :
    (⋂ A ∈ 𝒜, closure (Prod.fst '' A)).Nonempty := by
  rcases CompactSpace.iInter_closure_nonempty
      ((fun A : Set (X₁ × X₂) ↦ Prod.fst '' A) '' 𝒜) (h𝒜.image Prod.fst) with ⟨x, hx⟩
  refine ⟨x, Set.mem_iInter.2 fun A ↦ Set.mem_iInter.2 fun hA ↦ ?_⟩
  exact Set.mem_iInter.1 (Set.mem_iInter.1 hx (Prod.fst '' A)) ⟨A, hA, rfl⟩
